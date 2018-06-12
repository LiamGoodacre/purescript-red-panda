module Main where

import Prelude
import FRP.Event as FRP
import Data.Foldable ( traverse_, foldMap )
import Data.Function.Uncurried ( Fn2, mkFn2, runFn2, Fn3, mkFn3, runFn3 )
import Data.Maybe ( Maybe (..) )
import Data.Profunctor ( class Profunctor, dimap, lcmap )
import Data.Tuple ( Tuple (..), snd )
import Web.DOM ( Node, Element ) as Web
import Web.DOM.Document ( createTextNode, createElement ) as Web
import Web.DOM.Element ( setAttribute, removeAttribute, toEventTarget, toNode ) as Web.Element
import Web.DOM.Node ( appendChild, removeChild ) as Web
import Web.DOM.Text ( toNode ) as Web.Text
import Web.Event.Event ( Event, EventType (..) ) as Web
import Web.Event.EventTarget ( addEventListener, eventListener, removeEventListener ) as Web
import Web.HTML ( window ) as Web
import Web.HTML.HTMLDocument ( body, toDocument ) as Web
import Web.HTML.HTMLElement ( toElement, toNode ) as Web.HTML.HTMLElement
import Web.HTML.Window ( document ) as Web
import Effect ( Effect )
import Effect.Ref as Ref
import Control.Alternative ( empty, (<|>) )

data Property input output =
  Literal String ( Watcher input String ) |
  Handler Web.EventType ( Watcher input ( Web.Event -> Maybe output ) )

instance profunctorValue :: Profunctor Property where
  dimap f g = case _ of
    Literal attr op ->
      Literal attr ( lcmap f op )

    Handler eventType op ->
      Handler eventType ( dimap f ( map ( map g ) ) op )

data Change output = Remove | NotChanged | Changed output

derive instance functorChange :: Functor Change

data Watcher input output =
  Ignoring output |
  Watching ( input -> Change output )

instance profunctorWatcher :: Profunctor Watcher where
  dimap f g = case _ of
    Ignoring output ->
      Ignoring ( g output )

    Watching observe ->
      Watching ( dimap f ( map g ) observe )

newtype Result input output =
  Result
    { consumer :: Maybe ( input -> Effect Unit )
    , producer :: FRP.Event output
    , cancel :: Effect Unit
    }

appendResult ::
  forall input output .
  Fn2
    (Result input output)
    (Result input output)
    (Result input output)
appendResult = mkFn2 \ ( Result l ) ( Result r ) ->
  Result
    { consumer: l.consumer <> r.consumer
    , producer: l.producer <|> r.producer
    , cancel: l.cancel <> r.cancel
    }

emptyResult :: forall input output . Result input output
emptyResult =
  Result
    { consumer: mempty
    , producer: empty
    , cancel: mempty
    }

instance semigroupResult :: Semigroup (Result input output) where
  append l r = runFn2 appendResult l r

instance monoidResult :: Monoid (Result input output) where
  mempty = emptyResult

type Key = Array String

data Element input output = Element Key ( Watcher input ( Node input output ) )

instance profunctorElement :: Profunctor Element where
  dimap f g ( Element key op ) =
    Element key ( dimap f ( dimap f g ) op )

instance semigroupElement :: Semigroup ( Element input output ) where
  append l r = group [ l, r ]

type TagName = String

data Node input output =
  Group ( Array ( Element input output ) ) |
  Text String |
  Tag TagName ( Array ( Property input output ) ) ( Array ( Element input output ) )

instance profunctorNode :: Profunctor Node where
  dimap f g = case _ of
    Group elements ->
      Group ( map ( dimap f g ) elements )

    Text s ->
      Text s

    Tag tag properties children ->
      Tag tag ( dimap f g <$> properties ) ( dimap f g <$> children )

instance semigroupNode :: Semigroup ( Node input output ) where
  append l r = Group [ element_ l, element_ r ]

drawLiteral :: Fn3 String Web.Element String ( Effect ( Effect Unit ) )
drawLiteral = mkFn3 \ key element content -> do
  Web.Element.setAttribute key content element
  pure ( Web.Element.removeAttribute key element )

drawHandler ::
  Fn3
    Web.EventType
    Web.Element
    ( Web.Event -> Effect Unit )
    ( Effect ( Effect Unit ) )
drawHandler = mkFn3 \ eventType element onEvent -> do
  let eventTarget = Web.Element.toEventTarget element
  listener <- Web.eventListener onEvent
  Web.addEventListener eventType listener false eventTarget
  pure ( Web.removeEventListener eventType listener false eventTarget )

renderPropertyWatcher ::
  forall input value output .
  Fn2
    ( input -> Change value )
    ( value -> Effect ( Effect Unit ) )
    ( Effect ( Result input output ) )
renderPropertyWatcher = mkFn2 \ observer render -> do
  cancelRef <- Ref.new Nothing

  let
    cancel = do
      cancelAttr <- Ref.read cancelRef
      Ref.write Nothing cancelRef
      case cancelAttr of
        Just op -> op
        Nothing -> pure unit

    observe = case _ of
      Remove -> cancel
      NotChanged -> pure unit
      Changed content -> do
        cancel
        cancelContent <- render content
        Ref.write ( Just cancelContent ) cancelRef

  pure
    ( Result
      { consumer: Just ( observe <<< observer )
      , producer: empty
      , cancel
      } )

renderLiteral ::
  forall input output .
  Fn3
    Web.Element
    String
    ( Watcher input String )
    ( Effect ( Result input output ) )
renderLiteral = mkFn3 \ element attr -> case _ of
  Ignoring content -> do
    cancel <- runFn3 drawLiteral attr element content
    pure
      ( Result
        { consumer: Nothing
        , producer: empty
        , cancel
        } )

  Watching observer ->
    runFn2 renderPropertyWatcher observer \ content ->
      runFn3 drawLiteral attr element content

renderHandler ::
  forall input output .
  Fn3
    Web.Element
    Web.EventType
    ( Watcher input ( Web.Event -> Maybe output ) )
    ( Effect ( Result input output ) )
renderHandler = mkFn3 \ element eventType -> case _ of
  Ignoring onEvent -> do
    { push, event: producer } <- FRP.create

    cancel <- runFn3 drawHandler eventType element \ e ->
      case onEvent e of
        Just output -> push output
        Nothing -> pure unit

    pure
      ( Result
        { consumer: Nothing
        , producer
        , cancel
        } )

  Watching observer -> do
    { push, event: producer } <- FRP.create

    runFn2 renderPropertyWatcher observer \ onEvent ->
      runFn3 drawHandler eventType element \ event ->
        case onEvent event of
          Just output -> push output
          Nothing -> pure unit

renderProperty ::
  forall input output .
  Fn2
    Web.Element
    ( Property input output )
    ( Effect ( Result input output ) )
renderProperty = mkFn2 \ element -> case _ of
  Literal attr content -> runFn3 renderLiteral element attr content
  Handler eventType content -> runFn3 renderHandler element eventType content

renderIgnoringElement ::
  forall input output .
  Fn3
    Web.Node
    Key
    ( Node input output )
    ( Effect ( Result input output ) )
renderIgnoringElement = mkFn3 \ parent key -> case _ of
  Group elements ->
    elements # foldMap \ element ->
      runFn2 renderElement parent element

  Text text -> do
    window <- Web.window
    document <- Web.document window
    textElement <- Web.createTextNode text ( Web.toDocument document )

    let textNode = Web.Text.toNode textElement

    _ <- Web.appendChild textNode parent
    pure
      ( Result
        { consumer: Nothing
        , producer: empty
        , cancel: do
            _ <- Web.removeChild textNode parent
            pure unit
        } )

  Tag tagName configProperties configChildren -> do
    window <- Web.window
    document <- Web.document window
    tagElement <- Web.createElement tagName ( Web.toDocument document )

    let
      tagNode = Web.Element.toNode tagElement

      self = Result
        { consumer: Nothing
        , producer: empty
        , cancel: do
            _ <- Web.removeChild tagNode parent
            pure unit
        }

    properties <- configProperties # foldMap \ property ->
      runFn2 renderProperty tagElement property

    -- TODO: actually use children keys
    children <- configChildren # foldMap \ child ->
      runFn2 renderElement tagNode child

    _ <- Web.appendChild tagNode parent
    pure ( runFn2 appendResult ( runFn2 appendResult children properties ) self )

renderWatchingElement ::
  forall input output .
  Fn3
    Web.Node
    Key
    ( input -> Change ( Node input output ) )
    ( Effect ( Result input output ) )
renderWatchingElement = mkFn3 \ parent key observer -> do
  cleanUpRef <- Ref.new Nothing
  childRef <- Ref.new Nothing
  { push, event: producer } <- FRP.create

  let
    cancel = do
      cleanUp <- Ref.read cleanUpRef
      child <- Ref.read childRef
      Ref.write Nothing cleanUpRef
      Ref.write Nothing childRef
      case child of
        Just ( Result c ) -> c.cancel
        Nothing -> pure unit
      case cleanUp of
        Just doCleanUp -> doCleanUp
        Nothing -> pure unit

    observe render update = case _ of
      Remove -> cancel

      NotChanged -> do
        child <- Ref.read childRef
        case child of
          Just ( Result c ) ->
            case c.consumer of
              Just doConsumer -> doConsumer update
              Nothing -> pure unit
          Nothing -> pure unit

      Changed content -> do
        cancel
        Result child <- render content
        cleanUp <- FRP.subscribe child.producer push
        Ref.write ( Just cleanUp ) cleanUpRef
        Ref.write ( Just ( Result child ) ) childRef
        case child.consumer of
          Just doConsumer -> doConsumer update
          Nothing -> pure unit

    consumer = Just \ update ->
      observe
        ( \ node -> runFn3 renderIgnoringElement parent key node )
        update
        ( observer update )

  pure
    ( Result
      { consumer
      , cancel
      , producer
      } )

renderElement ::
  forall input output .
  Fn2 Web.Node ( Element input output ) ( Effect ( Result input output ) )
renderElement = mkFn2 \ parent ( Element key view ) -> case view of
  Ignoring node -> runFn3 renderIgnoringElement parent key node
  Watching observer -> runFn3 renderWatchingElement parent key observer

newtype App state update event = App
  { view :: Element ( Tuple ( Maybe update ) state ) event
  , subscription :: FRP.Event event
  , initial :: state
  , update ::
      ( ( state -> Tuple update state ) -> Effect Unit ) ->
      ( Effect state -> event -> Effect Unit )
  }

renderApp ::
  forall state update event .
  Web.Node ->
  App state update event ->
  Effect ( Result ( Tuple ( Maybe update ) state ) event )
renderApp parent ( App app ) = do
  stateRef <- Ref.new app.initial
  Result component <- runFn2 renderElement parent app.view
  let events = app.subscription <|> component.producer

  cleanUp <-
    case component.consumer of
      Just consumer -> let
        onChange change = do
          state1 <- Ref.read stateRef
          let Tuple update state2 = change state1
          Ref.write state2 stateRef
          consumer ( Tuple ( Just update ) state2 )

        subscriber =
          app.update onChange ( Ref.read stateRef )

        in do
          cancelSubscription <- FRP.subscribe events subscriber
          consumer ( Tuple Nothing app.initial )
          pure cancelSubscription

      Nothing -> pure ( pure unit )

  let
    cancel = do
      component.cancel
      cleanUp

  pure ( Result component { cancel = cancel } )

element_ :: forall input output. Node input output -> Element input output
element_ node = Element [] ( Ignoring node )

group :: forall input output. Array ( Element input output ) -> Element input output
group elements = element_ ( Group elements )

null :: forall input output. Element input output
null = group []

text_ :: forall input output. String -> Element input output
text_ str = element_ ( Text str )

tagNode_ :: forall input output. TagName -> Array ( Property input output ) -> Array ( Element input output ) -> Element input output
tagNode_ tag props children = element_ ( Tag tag props children )

strong_ :: forall input output. Array ( Property input output ) -> Array ( Element input output ) -> Element input output
strong_ = tagNode_ "strong"

button_ :: forall input output. Array ( Property input output ) -> Array ( Element input output ) -> Element input output
button_ = tagNode_ "button"

redText :: forall t. Property Boolean t
redText =
  Literal "style"
    ( Watching case _ of
        true -> Changed "color: red"
        false -> Remove )

data Update = Toggle
data Event = Toggled

toggle :: Property Boolean Event
toggle =
  Handler ( Web.EventType "click" )
    ( Ignoring \ _ -> Just Toggled )

toggleButton :: Element Boolean Event
toggleButton =
  button_ [ redText, toggle ]
    [ Element [] ( Ignoring ( Text "Howdy" ) )
    ]

myApp :: App Boolean Update Event
myApp = App
  { view: lcmap snd toggleButton
  , subscription: empty
  , initial: false
  , update: \ dispatch _ -> case _ of
      Toggled -> dispatch \ s -> Tuple Toggle ( not s )
  }

main :: Effect Unit
main = do
  window <- Web.window
  document <- Web.document window
  Web.body document >>= traverse_ \ bodyHTML -> let
    bodyElement = Web.HTML.HTMLElement.toElement bodyHTML
    bodyNode = Web.HTML.HTMLElement.toNode bodyHTML in
    renderApp bodyNode myApp

