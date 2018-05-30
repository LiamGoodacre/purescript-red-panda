module Main where

import Prelude

import FRP.Event as FRP
import Data.Foldable (traverse_, sequence_, for_, foldMap)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Profunctor (class Profunctor, dimap, lcmap)
import Data.Tuple (Tuple(..), snd)
import Web.DOM (Node, Element) as Web
import Web.DOM.Document (createTextNode, createElement) as Web
import Web.DOM.Element (setAttribute, removeAttribute, toEventTarget, toNode) as Web.Element
import Web.DOM.Node (appendChild, removeChild) as Web
import Web.DOM.Text (toNode) as Web.Text
import Web.Event.Event (Event, EventType (..)) as Web
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener) as Web
import Web.HTML (window) as Web
import Web.HTML.HTMLDocument (body, toDocument) as Web
import Web.HTML.HTMLElement (toElement, toNode) as Web.HTML.HTMLElement
import Web.HTML.Window (document) as Web
import Effect (Effect)
import Effect.Ref as Ref
import Control.Alternative (empty, (<|>))

data Value
  (input :: Type)
  (output :: Type) =

    Literal
      String
      (Watcher input String) |

    Handler
      Web.EventType
      (Watcher input (Web.Event -> Maybe output))

instance profunctorValue :: Profunctor Value where
  dimap f _ (Literal attr op) = Literal attr (lcmap f op)
  dimap f g (Handler eventType op) = Handler eventType (dimap f (map (map g)) op)

data Change
  (output :: Type) =
    Remove |
    NotChanged |
    Changed output

derive instance functorChange :: Functor Change

data Watcher
  (input :: Type)
  (output :: Type) =

    Ignoring
      output |

    Watching
      (input -> Change output)

instance profunctorWatcher :: Profunctor Watcher where
  dimap _ g (Ignoring output) = Ignoring (g output)
  dimap f g (Watching observe) = Watching (dimap f (map g) observe)

newtype Result
  (input :: Type)
  (output :: Type) =

    Result
      { onUpdate :: Maybe (input -> Effect Unit)
      , cancel :: Effect Unit
      --event :: Alternate FRP.Event output
      , event :: FRP.Event output
      }

--derive newtype instace semigroupResult :: Semigroup (Result input output)
--derive newtype instace monoidResult :: Monoid (Result input output)

instance semigroupResult ::
  Semigroup (Result input output)
  where
    append (Result l) (Result r) =
      Result
        { onUpdate: l.onUpdate <> r.onUpdate
        , cancel: l.cancel <> r.cancel
        , event: l.event <|> r.event
        }

instance monoidResult ::
  Monoid (Result input output)
  where
    mempty = Result
      { onUpdate: mempty
      , cancel: mempty
      , event: empty
      }

type Key = List String

data Component
  (input :: Type)
  (output :: Type) =

    Component
      Key
      (Watcher input (Node input output))

instance profunctorComponent :: Profunctor Component where
  dimap f g (Component key op) = Component key (dimap f (dimap f g) op)

type Tag = String

data Node
  (input :: Type)
  (output :: Type) =

  TextNode
    String |

  TagNode
    Tag
    (List (Value input output))
    (List (Component input output))

instance profunctorNode :: Profunctor Node where
  dimap _ _ (TextNode s) = TextNode s
  dimap f g (TagNode tag properties children) = TagNode tag (dimap f g <$> properties) (dimap f g <$> children)

the ::
  forall arg input output .
  (arg -> Node input output) ->
  (arg -> Component input output)
the f o =
  Component Nil (Ignoring (f o))

watchingC ::
  forall input output .
  Key ->
  (input -> Change (Node input output)) ->
  Component input output
watchingC k f =
  Component k (Watching f)

drawLiteral ::
  String ->
  Web.Element ->
  String ->
  Effect (Effect Unit)
drawLiteral key element content = do
  Web.Element.setAttribute key content element
  pure (Web.Element.removeAttribute key element)

drawHandler ::
  Web.EventType ->
  Web.Element ->
  (Web.Event -> Effect Unit) ->
  Effect (Effect Unit)
drawHandler eventType element onEvent = do
  let
    eventTarget = Web.Element.toEventTarget element

  listener <- Web.eventListener onEvent

  Web.addEventListener eventType listener false eventTarget
  pure (Web.removeEventListener eventType listener false eventTarget)

renderLiteral ::
  forall input output .
  Web.Element ->
  String ->
  Watcher input String ->
  Effect (Result input output)
renderLiteral element attr = case _ of
  Ignoring content -> do
    cancel <- drawLiteral attr element content
    pure (Result
      { onUpdate: Nothing
      , cancel
      , event: empty
      })

  Watching observer -> do
    cancelRef <- Ref.new Nothing

    let
      cancel = do
        cancelAttr <- Ref.read cancelRef
        Ref.write Nothing cancelRef
        sequence_ cancelAttr

      observe ::
        forall value .
        (value -> Effect (Effect Unit)) ->
        Change value ->
        Effect Unit
      observe render = case _ of
        Remove -> cancel
        NotChanged -> pure unit
        Changed content -> do
          cancelContent <- render content
          Ref.write (Just cancelContent) cancelRef

    pure (Result
      { onUpdate: Just (observe (drawLiteral attr element) <<< observer)
      , cancel
      , event: empty
      })

renderHandler ::
  forall input output .
  Web.Element ->
  Web.EventType ->
  Watcher input (Web.Event -> Maybe output) ->
  Effect (Result input output)
renderHandler element eventType = case _ of
  Ignoring onEvent -> do
    { push, event } ← FRP.create
    cancel <- drawHandler eventType element (\e -> traverse_ push (onEvent e))
    pure (Result
      { onUpdate: Nothing
      , cancel
      , event
      })

  Watching observer -> do
    cancelRef <- Ref.new Nothing

    let
      cancel = do
        cancelAttr <- Ref.read cancelRef
        Ref.write Nothing cancelRef
        sequence_ cancelAttr

      observe ::
        forall value .
        (value -> Effect (Effect Unit)) ->
        Change value ->
        Effect Unit
      observe render = case _ of
        Remove -> cancel
        NotChanged -> pure unit
        Changed content -> do
          cancelContent <- render content
          Ref.write (Just cancelContent) cancelRef

    { push, event } <- FRP.create

    let
      render onEvent =
        drawHandler eventType element (traverse_ push <<< onEvent)

    pure (Result
      { onUpdate: Just (observe render <<< observer)
      , cancel
      , event
      })

renderProperty ::
  forall input output .
  Web.Element ->
  Value input output ->
  Effect (Result input output)
renderProperty element = case _ of
  Literal attr content -> renderLiteral element attr content
  Handler eventType content -> renderHandler element eventType content

renderIgnoringComponent ::
  forall input output .
  Web.Node ->
  Key ->
  Node input output ->
  Effect (Result input output)
renderIgnoringComponent parent key = case _ of
  TextNode text -> do
    document <- Web.toDocument <$> (Web.document =<< Web.window)
    textElement <- Web.createTextNode text document

    let
      textNode = Web.Text.toNode textElement

    _ <- Web.appendChild textNode parent
    pure (Result
      { onUpdate: Nothing
      , cancel: Web.removeChild textNode parent $> unit
      , event: empty
      })

  TagNode configTag configProperties configChildren -> do
    document <- Web.toDocument <$> (Web.document =<< Web.window)
    tagElement <- Web.createElement configTag document

    let
      tagNode = Web.Element.toNode tagElement

      self = Result
        { onUpdate: Nothing
        , cancel: Web.removeChild tagNode parent $> unit
        , event: empty
        }

    properties <- foldMap (renderProperty tagElement) configProperties

    -- TODO: actually use children keys
    children <- foldMap (renderComponent tagNode) configChildren

    _ <- Web.appendChild tagNode parent
    pure (children <> properties <> self)

renderWatchingComponent ::
  forall input output .
  Web.Node ->
  Key ->
  (input -> Change (Node input output)) ->
  Effect (Result input output)
renderWatchingComponent parent key observer = do
  cleanUpRef <- Ref.new Nothing
  childRef <- Ref.new Nothing
  { push, event } <- FRP.create

  let
    cancel = do
      cleanUp <- Ref.read cleanUpRef
      child <- Ref.read childRef
      Ref.write Nothing cleanUpRef
      Ref.write Nothing childRef
      for_ child \(Result c) -> c.cancel
      sequence_ cleanUp

    observe render update = case _ of
      Remove -> cancel

      NotChanged -> do
        child <- Ref.read childRef
        for_ child \(Result c) ->
          for_ c.onUpdate (_ $ update)

      Changed content -> do
        cancel
        Result child <- render content
        cleanUp <- FRP.subscribe child.event push
        Ref.write (Just cleanUp) cleanUpRef
        Ref.write (Just (Result child)) childRef
        for_ child.onUpdate (_ $ update)

    onUpdate = Just \update ->
      observe (renderIgnoringComponent parent key) update $
      observer update

  pure (Result
    { onUpdate
    , cancel
    , event
    })

renderComponent ::
  forall input output .
  Web.Node ->
  Component input output ->
  Effect (Result input output)
renderComponent parent (Component key view) = case view of
  Ignoring node -> renderIgnoringComponent parent key node
  Watching observer -> renderWatchingComponent parent key observer

newtype App
  (state :: Type)
  (update :: Type)
  (event :: Type) =

    App
      { view :: Component (Tuple update state) update
      , subscription :: FRP.Event event
      , initial :: Tuple update state
      , update ::
          ((state -> Tuple update state) -> Effect Unit) ->
          (Tuple state event -> Effect Unit)
      }

renderApp ::
  forall state update event .
  Web.Node ->
  App state update event ->
  Effect (Result (Tuple update state) update)
renderApp parent (App app) = do
  Result component <- renderComponent parent app.view
  for_ component.onUpdate (_ $ app.initial)
  pure (Result component)

main :: Effect Unit
main = Web.window >>= Web.document >>= Web.body >>= traverse_ \bodyHTML -> do

  let
    bodyElement = Web.HTML.HTMLElement.toElement bodyHTML
    bodyNode = Web.HTML.HTMLElement.toNode bodyHTML

  _ <- renderApp bodyNode myApp

--   for_ result.onUpdate \onUpdate -> do
--     FRP.subscribe result.event onUpdate

  pure unit

foo :: forall t. Value Boolean t
foo =
  Literal "style"
    (Watching case _ of
      true -> Changed "color: red"
      false -> Remove)

data Action =
  Init |
  Toggle

toggle :: Value Boolean Action
toggle =
  Handler (Web.EventType "click")
    (Ignoring \_ -> Just Toggle)

bar :: Component Boolean Action
bar =
  Component ("K" : Nil)
    (Ignoring $
      TagNode "button"
        ( foo
        : toggle
        : Nil )

        ( the TextNode "Howdy"
        : Nil ))

myApp ::
  forall event .
  App Boolean Action event
myApp =
  App
    { view: lcmap snd bar
    , subscription: empty
    , initial: Tuple Init false
    , update: \callback (Tuple s e) -> pure unit
    }

