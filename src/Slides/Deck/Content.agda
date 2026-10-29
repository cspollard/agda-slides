{-# OPTIONS --safe --without-K #-}

-- Content: the leaves of a slide.
--
-- Flow content (text, lists, math, tables, boxes) is laid out by the browser, so it is a carrier
-- of its own, sharing the temporal structure of scenes but not the geometry of diagrams.  A
-- `Flow` is a list of blocks, the free monoid on them; overlaying two leaves of a scene is
-- concatenation (`++`, associative, which is all `Slides.Scene.Sample` asks of a leaf carrier).
-- Blocks nest (columns, boxes, fragments and styled divisions hold flows), which is a nested
-- inductive type: the recursion below goes through `List` by mutual functions.
--
-- Its semantics is a monoid homomorphism to lines of plain text (`plain`, `plain-++`): the
-- reading a plain-text backend gives.  The HTML reading is the other homomorphism
-- (`Slides.Backend.Render`); both need nothing else from this module.
--
-- The vocabulary is what the examples use (legacy `Slides.Core`): the legacy `Play`,
-- `paramAnimation` and pre-rendered frame lists are not here (an animation is a scene of
-- diagrams, `Slides.Deck.Anim`, shipped by `Slides.Backend.Animation`).

module Slides.Deck.Content where

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.String.Base using (String; intersperse; concat) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Data.List.Properties as ListP

open import Slides.Deck.Math using (Math; toLaTeX)
open import Slides.Diagram.Syntax using (Dia)
open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling)
import Slides.Scene.Moving ratSpace ratTime ratCoupling as Mv

data Inline : Set where
  text codeSpan : String → Inline
  emph strong : List Inline → Inline
  inlineMath : Math → Inline
  link       : (url : String) → List Inline → Inline
  cite       : (key : String) → Inline          -- a bibliography key (checked by `Slides.Deck.DSL`)

Text : Set
Text = List Inline

data Block : Set where
  heading     : ℕ → Text → Block
  paragraph   : Text → Block
  bullets     : (incremental : Bool) → List Text → Block
  code        : (language source : String) → Block
  displayMath : Math → Block
  figure      : (src : String) (caption : Text) → Block
  notes       : Text → Block
  table       : (header : List Text) (rows : List (List Text)) → Block
  references  : List (String × Text) → Block
  diagram     : (name : String) (percent : ℕ) → Dia ℕ → Block
  -- an animation: a name (unique in the deck), the displayed percent, milliseconds per tick, and
  -- its acts, one reveal step each: a step plays the next act (`Slides.Backend.Animation`)
  animation   : String → ℕ → ℕ → List Mv.Anim → Block
  -- an animation that loops while its slide is shown
  animationLoop : String → ℕ → ℕ → Mv.Anim → Block
  script      : String → Block       -- JavaScript run once when its slide is shown (`slide`)
  mount       : String → Block       -- an empty element with this id, for scripts
  columns     : List (List Block) → Block
  box         : Text → List Block → Block
  fragment    : Maybe String → List Block → Block   -- a reveal.js fragment (style class)
  classed     : String → List Block → Block         -- a division with CSS classes
  placed      : (x y w h : ℕ) → List Block → Block  -- percentages of the slide

Flow : Set
Flow = List Block

------------------------------------------------------------------------
-- Plain text

mutual
  plainI : Inline → String
  plainI (text s)       = s
  plainI (codeSpan s)   = s
  plainI (emph is)      = plainT is
  plainI (strong is)    = plainT is
  plainI (inlineMath m) = toLaTeX m
  plainI (link _ is)    = plainT is
  plainI (cite k)       = "[" ++ˢ k ++ˢ "]"

  plainT : Text → String
  plainT []       = ""
  plainT (i ∷ is) = plainI i ++ˢ plainT is

mutual
  plainB : Block → List String
  plainB (heading _ t)   = plainT t ∷ []
  plainB (paragraph t)   = plainT t ∷ []
  plainB (bullets _ ts)  = map (λ t → "- " ++ˢ plainT t) ts
  plainB (code _ s)      = s ∷ []
  plainB (displayMath m) = toLaTeX m ∷ []
  plainB (figure _ c)    = plainT c ∷ []
  plainB (notes _)       = []
  plainB (table h rows)  = row h ∷ map row rows
    where row = λ cs → intersperse " | " (map plainT cs)
  plainB (references rs) = map (λ r → plainT (proj₂ r)) rs
  plainB (diagram _ _ _) = []
  plainB (animation _ _ _ _) = []
  plainB (animationLoop _ _ _ _) = []
  plainB (script _)      = []
  plainB (mount _)       = []
  plainB (columns cs)    = plains cs
  plainB (box _ f)       = plain f
  plainB (fragment _ f)  = plain f
  plainB (classed _ f)   = plain f
  plainB (placed _ _ _ _ f) = plain f

  plain : Flow → List String
  plain []       = []
  plain (b ∷ bs) = plainB b ++ plain bs

  plains : List Flow → List String
  plains []       = []
  plains (f ∷ fs) = plain f ++ plains fs

plain-++ : ∀ xs ys → plain (xs ++ ys) ≡ plain xs ++ plain ys
plain-++ []       ys = refl
plain-++ (b ∷ xs) ys = trans (cong (plainB b ++_) (plain-++ xs ys)) (sym (ListP.++-assoc (plainB b) (plain xs) (plain ys)))
