{-# OPTIONS --safe --without-K #-}

-- The layout carrier: a `Layout` is a rectangle of known size that knows how to
-- draw itself at any offset, plus the named sub-rectangles ("anchors") inside
-- it.  The operations here are the semantics of the connectives of
-- `Slides.Diagram.Syntax`; `Slides.Diagram.Layout` assembles them into an
-- algebra.
--
-- Coordinates are natural numbers: a layout always lives at non-negative
-- offsets inside its own frame, and every operation grows the frame to fit.

module Slides.Diagram.Place where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _/_; _⊔_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram using (Style; Element; rect; circle; line; arrow; label)
open import Slides.Diagram.Geometry
open import Slides.Diagram.TextMetrics using (textWidth)

record Layout : Set where
  field
    width   : ℕ
    height  : ℕ
    -- draw with the top-left corner at the given offset
    render  : ℕ → ℕ → List Element
    anchors : List (String × Box)

open Layout public

------------------------------------------------------------------------
-- Primitives

spacer : ℕ → ℕ → Layout
spacer w h = record { width = w ; height = h ; render = λ _ _ → [] ; anchors = [] }

rectangle : ℕ → ℕ → Style → Layout
rectangle w h s = record
  { width = w ; height = h ; anchors = []
  ; render = λ x y → rect x y w h s ∷ [] }

disc : ℕ → Style → Layout
disc r s = record
  { width = 2 * r ; height = 2 * r ; anchors = []
  ; render = λ x y → circle (x + r) (y + r) r s ∷ [] }

segment : ℕ → ℕ → Style → Layout
segment w h s = record
  { width = w ; height = h ; anchors = []
  ; render = λ x y → line x y (x + w) (y + h) s ∷ [] }

-- text: as wide as its characters (`pct` percent, for a heavier font), and
-- `size * 3/2` high
text : ℕ → ℕ → String → Style → Layout
text pct size t s = record
  { width = w ; height = (size * 3) / 2 ; anchors = []
  ; render = λ x y → label (x + w / 2) (y + (size * 3) / 4) size t s ∷ [] }
  where w = (textWidth size t * pct) / 100

raw : ℕ → ℕ → List Element → Layout
raw w h es = record { width = w ; height = h ; anchors = [] ; render = λ _ _ → es }

------------------------------------------------------------------------
-- Moving and combining

-- the same layout, shifted inside a frame of a given size
inFrame : ℕ → ℕ → ℕ → ℕ → Layout → Layout
inFrame w h dx dy d = record
  { width = w ; height = h
  ; render = λ x y → render d (x + dx) (y + dy)
  ; anchors = map (λ { (n , b) → n , shiftBox dx dy b }) (anchors d) }

-- two layouts in one frame, the second drawn over the first
overlay : ℕ → ℕ → Layout → Layout → Layout
overlay w h a b = record
  { width = w ; height = h
  ; render = λ x y → render a x y ++ render b x y
  ; anchors = anchors a ++ anchors b }

atop : Layout → Layout → Layout
atop a b =
  let w = width a ⊔ width b ; h = height a ⊔ height b in
  overlay w h (inFrame w h (centre w (width a)) (centre h (height a)) a)
              (inFrame w h (centre w (width b)) (centre h (height b)) b)

besideA : VAlign → ℕ → Layout → Layout → Layout
besideA al g a b =
  let w = width a + g + width b ; h = height a ⊔ height b in
  overlay w h (inFrame w h 0 (valignOffset al h (height a)) a)
              (inFrame w h (width a + g) (valignOffset al h (height b)) b)

aboveA : Align → ℕ → Layout → Layout → Layout
aboveA al g a b =
  let w = width a ⊔ width b ; h = height a + g + height b in
  overlay w h (inFrame w h (alignOffset al w (width a)) 0 a)
              (inFrame w h (alignOffset al w (width b)) (height a + g) b)

margin : ℕ → ℕ → ℕ → ℕ → Layout → Layout
margin l t r b d = inFrame (l + width d + r) (t + height d + b) l t d

topAligned : ℕ → Layout → Layout
topAligned h d = inFrame (width d) (h ⊔ height d) 0 0 d

minWidth : ℕ → Layout → Layout
minWidth w d = let w′ = w ⊔ width d in inFrame w′ (height d) (centre w′ (width d)) 0 d

labelAbove labelBelow : ℕ → Layout → Layout → Layout
labelAbove g lbl d = aboveA centred g lbl (aboveA centred g d (spacer 0 (height lbl)))
labelBelow g lbl d = aboveA centred g (spacer 0 (height lbl)) (aboveA centred g d lbl)

------------------------------------------------------------------------
-- Names and connections

named : String → Layout → Layout
named n d = record d { anchors = (n , box 0 0 (width d) (height d)) ∷ anchors d }

private
  find : String → List (String × Box) → Maybe Box
  find n [] = nothing
  find n ((m , b) ∷ bs) = if ⌊ n ≟ m ⌋ then just b else find n bs

-- An arrow between two named boxes.  A name that does not exist draws
-- nothing; `Slides.Diagram.Names` reports such connections.
connectP : String → Port → String → Port → Style → Layout → Layout
connectP a pa b pb s d with find a (anchors d) | find b (anchors d)
... | just ba | just bb =
  let (x₁ , y₁) = portPoint pa ba ; (x₂ , y₂) = portPoint pb bb in
  record d { render = λ x y → render d x y ++ arrow (x + x₁) (y + y₁) (x + x₂) (y + y₂) s ∷ [] }
... | _ | _ = d
