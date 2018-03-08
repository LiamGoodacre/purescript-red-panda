module Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

import Control.Monad.Eff.Ref as Ref
import Control.Plus (empty)

import Data.Either (Either(..))
import Data.Foldable (sequence_, traverse_, for_)
import Data.Identity (Identity(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Profunctor.Joker (Joker(..))
import Data.Profunctor.Star (Star(..))

import DOM.Event.EventTarget (addEventListener, eventListener, removeEventListener, EventListener) as DOM
import DOM.Event.Types (Event, EventType) as DOM
import DOM.HTML (window) as DOM
import DOM.HTML.Document (body) as DOM
import DOM.HTML.Types (htmlDocumentToDocument, htmlElementToNode, htmlElementToElement) as DOM
import DOM.HTML.Window (document) as DOM
import DOM.Node.Element (setAttribute, removeAttribute) as DOM
import DOM.Node.Types (Node, Element, elementToEventTarget) as DOM

import FRP.Event as FRP

data Value p input output
  = Literal String        (p input String)
  | Handler DOM.EventType (p input (DOM.Event -> Maybe output))

data Change output
  = Remove
  | NotChanged
  | Changed output

data Watcher k input output
  = Ignoring (k (Joker Identity) input output)
  | Watching (k (Star Change)    input output)

newtype Result eff input output = Result
  { onUpdate :: Maybe (input -> Eff eff Unit)
  , cancel :: Eff eff Unit
  , event :: FRP.Event output
  }

renderLiteral ::
  String ->
  String ->
  DOM.Element ->
  Eff _ (Eff _ Unit)
renderLiteral key content element = do
  DOM.setAttribute key content element
  pure (DOM.removeAttribute key element)

renderHandler ::
  DOM.EventType ->
  (DOM.Event -> Eff _ Unit) ->
  DOM.Element ->
  Eff _ (Eff _ Unit)
renderHandler eventType onEvent element = do
  let eventTarget = DOM.elementToEventTarget element
      listener    = DOM.eventListener onEvent
  DOM.addEventListener eventType listener false eventTarget
  pure (DOM.removeEventListener eventType listener false eventTarget)

renderValue :: forall input output.
  Value (Joker Identity) input output ->
  DOM.Element ->
  Eff _ (Result _ input output)
renderValue value element =
  case value of
    Literal key (Joker (Identity content)) -> do
      cancel <- renderLiteral key content element
      pure (Result
        { onUpdate: Nothing
        , cancel
        , event: empty
        })

    Handler eventType (Joker (Identity onEvent)) -> do
      { push, event } ← FRP.create
      cancel <- renderHandler eventType (\e -> traverse_ push (onEvent e)) element
      pure (Result
        { onUpdate: Nothing
        , cancel
        , event
        })

renderAttrWatching :: forall input output.
  Value (Star Change) input output ->
  DOM.Element ->
  Eff _ (Result _ input output)
renderAttrWatching value element = do
  let noop = pure unit
  cancelRef <- Ref.newRef noop

  let cancel = do
        cancelAttr <- Ref.readRef cancelRef
        Ref.writeRef cancelRef noop
        cancelAttr

  let observe :: forall value.
        (value -> DOM.Element -> Eff _ (Eff _ Unit)) ->
        Change value ->
        Eff _ Unit
      observe render = case _ of
        Remove -> cancel
        NotChanged -> pure unit
        Changed content -> do
          cancelContent <- render content element
          Ref.writeRef cancelRef cancelContent

  case value of
    Literal key (Star observer) ->
      pure (Result
        { onUpdate: Just (observe (renderLiteral key) <<< observer)
        , cancel
        , event: empty
        })

    Handler eventType (Star observer) -> do
      { push, event } <- FRP.create

      let render onEvent =
            renderHandler eventType (traverse_ push <<< onEvent)

      pure (Result
        { onUpdate: Just (observe render <<< observer)
        , cancel
        , event
        })

renderProperty :: forall input output.
  Watcher Value input output ->
  DOM.Element ->
  Eff _ (Result _ input output)
renderProperty = case _ of
  Ignoring value -> renderValue value
  Watching value -> renderAttrWatching value

main :: Eff _ Unit
main = do
  window <- DOM.window
  document <- DOM.document window
  DOM.body document >>= traverse_ \body -> do
    Result result <- renderProperty foo (DOM.htmlElementToElement body)
    for_ result.onUpdate \onUpdate -> do
      onUpdate true
      onUpdate false
    pure unit

foo = Watching
  (Literal "style"
    (Star case _ of
      true -> Changed "background-color: blue"
      false -> Remove))

