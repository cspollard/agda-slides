{-# OPTIONS --safe --without-K #-}

-- The slide vocabulary as containers.
--
-- A deck is a program in the free monad over `DeckC`; the content of a
-- slide is a program over `BlockC = ContentC ⊎ LayoutC`.  Nesting is
-- stratified rather than recursive: the shape of the `slide` command
-- *contains* a body, and the shape of `columns` contains content programs,
-- so no container mentions itself and strict positivity is not an issue.
-- Backends are algebras for each level (`Container.Interpret`); the algebra
-- for `BlockC` is the copairing of the algebras for its summands
-- (`Container.Sum`).
--
-- All commands have a single continuation (`Position = ⊤`).

module Slides.Core where

open import Level using (0ℓ)
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_)

open import Slides.Math using (Math)
open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Param using (AnyParam)

------------------------------------------------------------------------
-- Inline markup

data Inline : Set where
  text       : String → Inline
  emph       : List Inline → Inline
  strong     : List Inline → Inline
  inlineMath : Math → Inline
  codeSpan   : String → Inline
  link       : (url : String) → List Inline → Inline
  -- a citation of a bibliography key (checked against the deck's resources)
  cite       : (key : String) → Inline

-- Running text.
Text : Set
Text = List Inline

------------------------------------------------------------------------
-- Content inside a slide

-- How an animation's frames are played: one act per reveal step, resting on the
-- given frames (nondecreasing; one reveal fragment per entry), or forever in a
-- cycle (`looping`) while the slide is shown (frame `t mod n`, see `Slides.Anim.Loop`),
-- or `both`: the loop runs under the steps (frame `phase * n + step`).
data Play : Set where
  onSteps : List ℕ → Play
  looping : Play
  -- both at once: steps `rests` of a single phase, over a loop of `period` phases;
  -- the frames are the phases one after the other, each a full copy of the steps
  both    : List ℕ → (period : ℕ) → Play

data ContentShape : Set where
  heading     : (level : ℕ) → Text → ContentShape
  paragraph   : Text → ContentShape
  bullets     : (incremental : Bool) → List Text → ContentShape
  code        : (language source : String) → ContentShape
  displayMath : Math → ContentShape
  figure      : (src : String) (caption : Text) → ContentShape
  notes       : Text → ContentShape
  table       : (header : List Text) (rows : List (List Text)) → ContentShape
  -- the bibliography: keys with their entries
  references  : List (String × Text) → ContentShape
  -- an inline vector diagram
  diagram     : Diagram → ContentShape
  -- an animation: the first frame and the others (they share one `viewBox`), the
  -- time one frame is shown in milliseconds, and how they are played.  With
  -- `onSteps rests`, showing step `k` plays the frames from where step `k-1` rested
  -- to `rests !! (k-1)`, one every `ms`; going back plays them in reverse.  Step 0
  -- rests on the first frame.  With `looping` the frames repeat in order, one every
  -- `ms`, from the moment the slide is shown.  `both rests p` lays `p` phases of the
  -- steps end to end (`rests` index within one phase): step `k` plays within the
  -- current phase while the phase itself advances every `ms`.
  animation   : Diagram → List Diagram → (ms : ℕ) → Play → ContentShape
  -- the same animation of templates (`Slides.Anim.Param`): the frames as they are
  -- when the page cannot play them (`Slides.Lower`), and, for a page that can, the
  -- symbolic layouts, from which the page computes each frame (continuous or
  -- discrete templates, `Slides.Diagram.Param.AnyParam`)
  paramAnimation : Diagram → List Diagram → AnyParam → (ms : ℕ) → Play → ContentShape
  -- JavaScript run once, when the slide holding it is first shown, with the
  -- slide element as `slide` (unchecked; carried in a `data-js` attribute)
  script      : String → ContentShape
  -- an empty element with the given id, for scripts to draw into
  mount       : String → ContentShape

ContentC : Container 0ℓ 0ℓ
ContentC = ContentShape ▷ λ _ → ⊤

-- A program over `ContentC`: the content of a column or box.
Content : Set
Content = ContentC ⋆ ⊤

------------------------------------------------------------------------
-- Layout

data LayoutShape : Set where
  columns : List Content → LayoutShape
  box     : (title : Text) → Content → LayoutShape
  -- the content appears on a later step; the style is a reveal.js fragment
  -- class (fade-up, grow, highlight-red, …)
  fragment : (style : Maybe String) → Content → LayoutShape
  -- `pause`: everything after it in the body appears step by step (see
  -- `Slides.Steps`); renders as nothing by itself
  pause    : LayoutShape
  -- content in a `<div>` with the given CSS class(es), for stylesheets
  classed  : (classes : String) → Content → LayoutShape
  -- content in a box at a fixed position: left, top, width, height, in whole
  -- percentages of the slide
  placed   : (x y w h : ℕ) → Content → LayoutShape
  -- a layout command that appears on a later step (produced by `Slides.Steps`)
  stepped  : (style : Maybe String) → LayoutShape → LayoutShape

LayoutC : Container 0ℓ 0ℓ
LayoutC = LayoutShape ▷ λ _ → ⊤

-- Everything that can appear directly in a slide.
BlockC : Container 0ℓ 0ℓ
BlockC = ContentC ⊎ LayoutC

-- The body of a slide.
Body : Set
Body = BlockC ⋆ ⊤

------------------------------------------------------------------------
-- The deck

record SlideOptions : Set where
  field
    background : Maybe String   -- any CSS colour
    transition : Maybe String   -- none, fade, slide, convex, concave, zoom

defaultSlide : SlideOptions
defaultSlide = record { background = nothing ; transition = nothing }

data DeckShape : Set where
  -- a horizontal slide
  slide : SlideOptions → Body → DeckShape
  -- a vertical stack of slides (reveal.js nested sections)
  stack : SlideOptions → List Body → DeckShape

DeckC : Container 0ℓ 0ℓ
DeckC = DeckShape ▷ λ _ → ⊤

Deck : Set
Deck = DeckC ⋆ ⊤
