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

data Value input output =
  Literal String (Watcher input String) |
  Handler Web.EventType (Watcher input (Web.Event -> Maybe output))

instance profunctorValue :: Profunctor Value where
  dimap f _ (Literal attr op) = Literal attr (lcmap f op)
  dimap f g (Handler eventType op) = Handler eventType (dimap f (map (map g)) op)

data Change output = Remove | NotChanged | Changed output

derive instance functorChange :: Functor Change

data Watcher input output =
  Ignoring output |
  Watching (input -> Change output)

instance profunctorWatcher :: Profunctor Watcher where
  dimap _ g (Ignoring output) = Ignoring (g output)
  dimap f g (Watching observe) = Watching (dimap f (map g) observe)

newtype Result input output =
  Result
    { consumer :: Maybe (input -> Effect Unit)
    , cancel :: Effect Unit
    , producer :: FRP.Event output
    }

instance semigroupResult :: Semigroup (Result input output) where
  append (Result l) (Result r) = Result
    { consumer: l.consumer <> r.consumer
    , cancel: l.cancel <> r.cancel
    , producer: l.producer <|> r.producer
    }

instance monoidResult :: Monoid (Result input output) where
  mempty = Result
    { consumer: mempty
    , cancel: mempty
    , producer: empty
    }

type Key = List String

data Component input output = Component Key (Watcher input (Node input output))

instance profunctorComponent :: Profunctor Component where
  dimap f g (Component key op) = Component key (dimap f (dimap f g) op)

type Tag = String

data Node input output =
  TextNode String |
  TagNode Tag (List (Value input output)) (List (Component input output))

instance profunctorNode :: Profunctor Node where
  dimap _ _ (TextNode s) = TextNode s
  dimap f g (TagNode tag properties children) = TagNode tag (dimap f g <$> properties) (dimap f g <$> children)

drawLiteral :: String -> Web.Element -> String -> Effect (Effect Unit)
drawLiteral key element content = do
  Web.Element.setAttribute key content element
  pure (Web.Element.removeAttribute key element)

drawHandler ::
  Web.EventType ->
  Web.Element ->
  (Web.Event -> Effect Unit) ->
  Effect (Effect Unit)
drawHandler eventType element onEvent = do
  let eventTarget = Web.Element.toEventTarget element
  listener <- Web.eventListener onEvent
  Web.addEventListener eventType listener false eventTarget
  pure (Web.removeEventListener eventType listener false eventTarget)

renderPropertyWatcher ::
  forall input value output .
  (input -> Change value) ->
  (value -> Effect (Effect Unit)) ->
  Effect (Result input output)
renderPropertyWatcher observer render = do
  cancelRef <- Ref.new Nothing

  let
    cancel = do
      cancelAttr <- Ref.read cancelRef
      Ref.write Nothing cancelRef
      sequence_ cancelAttr

    observe = case _ of
      Remove -> cancel
      NotChanged -> pure unit
      Changed content -> do
        cancel
        cancelContent <- render content
        Ref.write (Just cancelContent) cancelRef

  pure (Result
    { consumer: Just (observe <<< observer)
    , cancel
    , producer: empty
    })


renderLiteral ::
  forall input output .
  Web.Element ->
  String ->
  Watcher input String ->
  Effect (Result input output)
renderLiteral element attr = case _ of
  Ignoring content -> do
    cancel <- drawLiteral attr element content
    pure (Result { consumer: Nothing , cancel , producer: empty })

  Watching observer ->
    renderPropertyWatcher observer (drawLiteral attr element)

renderHandler ::
  forall input output .
  Web.Element ->
  Web.EventType ->
  Watcher input (Web.Event -> Maybe output) ->
  Effect (Result input output)
renderHandler element eventType = case _ of
  Ignoring onEvent -> do
    { push, event: producer } ← FRP.create
    cancel <- drawHandler eventType element (\e -> traverse_ push (onEvent e))
    pure (Result
      { consumer: Nothing
      , cancel
      , producer
      })

  Watching observer -> do
    { push, event: producer } <- FRP.create
    let pushEvent onEvent = traverse_ push <<< onEvent
    renderPropertyWatcher observer (drawHandler eventType element <<< pushEvent)

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
      { consumer: Nothing
      , cancel: Web.removeChild textNode parent $> unit
      , producer: empty
      })

  TagNode configTag configProperties configChildren -> do
    document <- Web.toDocument <$> (Web.document =<< Web.window)
    tagElement <- Web.createElement configTag document

    let
      tagNode = Web.Element.toNode tagElement

      self = Result
        { consumer: Nothing
        , cancel: Web.removeChild tagNode parent $> unit
        , producer: empty
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
  { push, event: producer } <- FRP.create

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
          for_ c.consumer (_ $ update)

      Changed content -> do
        cancel
        Result child <- render content
        cleanUp <- FRP.subscribe child.producer push
        Ref.write (Just cleanUp) cleanUpRef
        Ref.write (Just (Result child)) childRef
        for_ child.consumer (_ $ update)

    consumer = Just \update ->
      observe (renderIgnoringComponent parent key) update $
      observer update

  pure (Result
    { consumer
    , cancel
    , producer
    })

renderComponent ::
  forall input output .
  Web.Node ->
  Component input output ->
  Effect (Result input output)
renderComponent parent (Component key view) = case view of
  Ignoring node -> renderIgnoringComponent parent key node
  Watching observer -> renderWatchingComponent parent key observer

newtype App state update event =
  App
    { view :: Component (Tuple (Maybe update) state) event
    , subscription :: FRP.Event event
    , initial :: state
    , update ::
        ((state -> Tuple update state) -> Effect Unit) ->
        (Effect state -> event -> Effect Unit)
    }

renderApp ::
  forall state update event .
  Web.Node ->
  App state update event ->
  Effect (Result (Tuple (Maybe update) state) event)
renderApp parent (App app) = do
  stateRef <- Ref.new app.initial
  Result component <- renderComponent parent app.view
  let events = app.subscription <|> component.producer

  cleanUp <- component.consumer `flip foldMap` \consumer -> let

    onChange change = do
      state1 <- Ref.read stateRef
      let Tuple update state2 = change state1
      Ref.write state2 stateRef
      consumer (Tuple (Just update) state2)

    subscriber =
      app.update onChange (Ref.read stateRef)

    in
      FRP.subscribe events subscriber <*
      consumer (Tuple Nothing app.initial)

  pure (Result component { cancel = component.cancel *> cleanUp })

main :: Effect Unit
main = Web.window >>= Web.document >>= Web.body >>= traverse_ \bodyHTML -> let
  bodyElement = Web.HTML.HTMLElement.toElement bodyHTML
  bodyNode = Web.HTML.HTMLElement.toNode bodyHTML
  in renderApp bodyNode myApp

redText :: forall t. Value Boolean t
redText =
  Literal "style"
    (Watching case _ of
      true -> Changed "color: red"
      false -> Remove)

data Update = Toggle
data Event = Toggled

toggle :: Value Boolean Event
toggle =
  Handler (Web.EventType "click")
    (Ignoring \_ -> Just Toggled)

toggleButton :: Component Boolean Event
toggleButton =
  Component ("K" : Nil)
    (Ignoring $
      TagNode "button"
        ( redText
        : toggle
        : Nil )

        ( Component Nil (Ignoring (TextNode "Howdy"))
        : Nil ))

myApp ::
  App Boolean Update Event
myApp =
  App
    { view: lcmap snd toggleButton
    , subscription: empty
    , initial: false
    , update: \dispatch _ -> case _ of
        Toggled -> dispatch \s -> Tuple Toggle (not s)
    }

