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
open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.List using (List)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_)
import Data.Container.Combinator as CB
open import Data.Container.FreeMonad using (_⋆_)

open import Slides.Math using (Math)

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
  -- a layout command that appears on a later step (produced by `Slides.Steps`)
  stepped  : (style : Maybe String) → LayoutShape → LayoutShape

LayoutC : Container 0ℓ 0ℓ
LayoutC = LayoutShape ▷ λ _ → ⊤

-- Everything that can appear directly in a slide.
BlockC : Container 0ℓ 0ℓ
BlockC = ContentC CB.⊎ LayoutC

------------------------------------------------------------------------
-- Capabilities (see `plan/Capabilities.md`)
--
-- Optional features are capabilities.  A capability is just the type of its
-- command shapes (so that `Body K` determines `K` by unification); how a
-- command appears on a later step (after a `pause`) is the `Steppable`
-- instance.  A deck is indexed by the capability `K` it may use; a backend
-- must support `K` to render it.

-- No optional features.
NoCap : Set
NoCap = ⊥

infixr 5 _⊕_
_⊕_ : Set → Set → Set
K ⊕ L = K ⊎ L

record Steppable (K : Set) : Set where
  field
    later : K → K

open Steppable {{...}} public

instance
  steppable-⊥ : Steppable ⊥
  steppable-⊥ = record { later = λ () }

  steppable-⊕ : ∀ {K L} {{_ : Steppable K}} {{_ : Steppable L}} → Steppable (K ⊕ L)
  steppable-⊕ = record { later = map⊎ later later }

-- `S ⊑ K`: the capability `K` provides the commands `S` (data types à la
-- carte).  Instances for reflexivity and for each side of `⊕`.
record _⊑_ (S K : Set) : Set where
  field
    inj : S → K

open _⊑_ {{...}} public

instance
  ⊑-refl : ∀ {S} → S ⊑ S
  ⊑-refl = record { inj = λ s → s }

  ⊑-left : ∀ {S K L} {{_ : S ⊑ K}} → S ⊑ (K ⊕ L)
  ⊑-left = record { inj = λ s → inj₁ (inj s) }

  ⊑-right : ∀ {S K L} {{_ : S ⊑ L}} → S ⊑ (K ⊕ L)
  ⊑-right = record { inj = λ s → inj₂ (inj s) }

capC : Set → Container 0ℓ 0ℓ
capC K = K ▷ λ _ → ⊤

variable
  K L : Set

-- Everything that can appear directly in a slide using the capability `K`.
BlockOf : Set → Container 0ℓ 0ℓ
BlockOf K = BlockC CB.⊎ capC K

-- The body of a slide.
Body : Set → Set
Body K = BlockOf K ⋆ ⊤

------------------------------------------------------------------------
-- The deck

record SlideOptions : Set where
  field
    background : Maybe String   -- any CSS colour
    transition : Maybe String   -- none, fade, slide, convex, concave, zoom

defaultSlide : SlideOptions
defaultSlide = record { background = nothing ; transition = nothing }

-- parametric in the type of slide bodies
data DeckShape (B : Set) : Set where
  -- a horizontal slide
  slide : SlideOptions → B → DeckShape B
  -- a vertical stack of slides (reveal.js nested sections)
  stack : SlideOptions → List B → DeckShape B

DeckC : Set → Container 0ℓ 0ℓ
DeckC K = DeckShape (Body K) ▷ λ _ → ⊤

Deck : Set → Set
Deck K = DeckC K ⋆ ⊤
