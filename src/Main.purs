module Main where

import Prelude

import Control.Alternative
  ( empty
  , (<|>)
  )

import Effect
  ( Effect
  )

import Effect.Ref
  as Ref

import Data.Foldable
  ( traverse_
  , for_
  , foldMap
  )

import Data.Identity
  ( Identity(..)
  )

import Data.List
  ( List(..)
  , (:)
  )

import Data.Maybe
  ( Maybe(..)
  )

import Data.Profunctor.Joker
  ( Joker(..)
  )

import Data.Profunctor.Star
  ( Star(..)
  )

import Web.Event.Event
  ( Event
  , EventType
  ) as Web

import Web.Event.EventTarget
  ( addEventListener
  , eventListener
  , removeEventListener
  ) as Web

import Web.DOM.Document
  ( createTextNode
  , createElement
  ) as Web

import Web.DOM.Element
  ( setAttribute
  , removeAttribute
  , toEventTarget
  , toNode
  ) as Web.Element

import Web.DOM.Node
  ( appendChild
  , removeChild
  ) as Web

import Web.DOM.Text
  ( toNode
  ) as Web.Text

import Web.DOM
  ( Node
  , Element
  ) as Web

import Web.HTML
  ( window
  ) as Web

import Web.HTML.HTMLDocument
  ( body
  , toDocument
  ) as Web

import Web.HTML.HTMLElement
  ( toElement
  , toNode
  ) as Web.HTML.HTMLElement

import Web.HTML.Window
  ( document
  ) as Web

import FRP.Event
  as FRP


data Value
  (operation :: Type -> Type -> Type)
  (input :: Type)
  (output :: Type) =

    Literal
      String
      (operation input String) |

    Handler
      Web.EventType
      (operation input (Web.Event -> Maybe output))

data Change
  (output :: Type) =
    Remove |
    NotChanged |
    Changed output

data Watcher
  (context :: (Type -> Type -> Type) -> Type -> Type -> Type)
  (input :: Type)
  (output :: Type) =

    Ignoring
      (context (Joker Identity) input output) |

    Watching
      (context (Star Change) input output)

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

newtype Key = Key (List String)

data Component
  (operation :: Type -> Type -> Type)
  (input :: Type)
  (output :: Type) =

    Component
      Key
      (operation input (Node input output))

data Node
  (input :: Type)
  (output :: Type) =

  TextNode
    String |

  TagNode
    { tag :: String
    , properties :: List (Watcher Value input output)
    , children :: List (Watcher Component input output)
    }

the ::
  forall arg input output .
  (arg -> Node input output) ->
  (arg -> Watcher Component input output)
the f o =
  Ignoring (Component (Key Nil) (Joker (Identity (f o))))

infix 4 the as !

watchingC ::
  forall input output .
  Key ->
  (input -> Change (Node input output)) ->
  Watcher Component input output
watchingC k f =
  Watching (Component k (Star f))

renderLiteral ::
  String ->
  Web.Element ->
  String ->
  Effect (Effect Unit)
renderLiteral key element content = do
  Web.Element.setAttribute key content element
  pure (Web.Element.removeAttribute key element)

renderHandler ::
  Web.EventType ->
  Web.Element ->
  (Web.Event -> Effect Unit) ->
  Effect (Effect Unit)
renderHandler eventType element onEvent = do
  let
    eventTarget = Web.Element.toEventTarget element

  listener <- Web.eventListener onEvent

  Web.addEventListener eventType listener false eventTarget
  pure (Web.removeEventListener eventType listener false eventTarget)

renderIgnoringValue ::
  forall input output .
  Web.Element ->
  Value (Joker Identity) input output ->
  Effect (Result input output)
renderIgnoringValue element value =
  case value of
    Literal key (Joker (Identity content)) -> do
      cancel <- renderLiteral key element content
      pure (Result
        { onUpdate: Nothing
        , cancel
        , event: empty
        })

    Handler eventType (Joker (Identity onEvent)) -> do
      { push, event } ← FRP.create
      cancel <- renderHandler eventType element (\e -> traverse_ push (onEvent e))
      pure (Result
        { onUpdate: Nothing
        , cancel
        , event
        })

renderWatchingValue ::
  forall input output .
  Web.Element ->
  Value (Star Change) input output ->
  Effect (Result input output)
renderWatchingValue element value = do
  cancelRef <- Ref.new mempty

  let
    cancel = do
      cancelAttr <- Ref.read cancelRef
      Ref.write mempty cancelRef
      cancelAttr

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
        Ref.write cancelContent cancelRef

  case value of
    Literal key (Star observer) ->
      pure (Result
        { onUpdate: Just (observe (renderLiteral key element) <<< observer)
        , cancel
        , event: empty
        })

    Handler eventType (Star observer) -> do
      { push, event } <- FRP.create

      let
        render onEvent =
          renderHandler eventType element (traverse_ push <<< onEvent)

      pure (Result
        { onUpdate: Just (observe render <<< observer)
        , cancel
        , event
        })

renderProperty ::
  forall input output .
  Web.Element ->
  Watcher Value input output ->
  Effect (Result input output)
renderProperty element = case _ of
  Ignoring value -> renderIgnoringValue element value
  Watching value -> renderWatchingValue element value

renderIgnoringComponent ::
  forall input output .
  Web.Node ->
  Component (Joker Identity) input output ->
  Effect (Result input output)
renderIgnoringComponent parent component =
  case component of
    Component key (Joker (Identity (TextNode text))) -> do
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

    Component key (Joker (Identity (TagNode config))) -> do
      document <- Web.toDocument <$> (Web.document =<< Web.window)
      tagElement <- Web.createElement config.tag document

      let
        tagNode = Web.Element.toNode tagElement

        self = Result
          { onUpdate: Nothing
          , cancel: Web.removeChild tagNode parent $> unit
          , event: empty
          }

      properties <- foldMap (renderProperty tagElement) config.properties

      -- TODO: actually use children keys
      children <- foldMap (renderComponent tagNode) config.children

      _ <- Web.appendChild tagNode parent
      pure (children <> properties <> self)

renderWatchingComponent ::
  forall input output .
  Web.Node ->
  Component (Star Change) input output ->
  Effect (Result input output)
renderWatchingComponent node component = do
  childRef <- Ref.new mempty
  { push, event } <- FRP.create

  let
    cancel = do
      cancelChild <- Ref.read childRef
      Ref.write mempty childRef
      cancelChild

    observe render update = case _ of
      Remove -> cancel
      NotChanged -> pure unit
      Changed content -> do
        cancel
        Result child <- render content
        cancelChild <- FRP.subscribe child.event push
        Ref.write (child.cancel *> cancelChild) childRef
        for_ child.onUpdate (_ $ update)

  case component of
    Component key (Star observer) ->
      let
        onUpdate = Just \update ->
          observe (renderIgnoringComponent node <<< Component key <<< Joker <<< Identity) update $
          observer update

      in
        pure (Result
          { onUpdate
          , cancel
          , event
          })

renderComponent ::
  forall input output .
  Web.Node ->
  Watcher Component input output ->
  Effect (Result input output)
renderComponent node = case _ of
  Ignoring component -> renderIgnoringComponent node component
  Watching component -> renderWatchingComponent node component

main :: Effect Unit
main = do
  window <- Web.window
  document <- Web.document window
  Web.body document >>= traverse_ \bodyHTML -> do

    let
      bodyElement = Web.HTML.HTMLElement.toElement bodyHTML
      bodyNode = Web.HTML.HTMLElement.toNode bodyHTML

    Result result <- renderComponent bodyNode bar
    --Result result <- renderProperty bodyElement foo
    for_ result.onUpdate \onUpdate -> do
      onUpdate true
      onUpdate false
      onUpdate true
    pure unit

foo :: forall t. Watcher Value Boolean t
foo = Watching
  (Literal "style"
    (Star case _ of
      true -> Changed "background-color: green"
      false -> Remove))

bar :: forall t. Watcher Component Boolean t
bar =
  watchingC (Key Nil) case _ of
    true ->
      Changed $ TagNode
        { tag: "button"
        , properties: foo : Nil
        , children: the TextNode "Howdy" : Nil
        }

    false ->
      Changed (TextNode "What")

