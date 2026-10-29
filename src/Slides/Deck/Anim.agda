{-# OPTIONS --safe --without-K #-}

-- Authoring animations: scenes of diagrams over the rationals (`Slides.Scene.Moving` at ℚ).
--
-- An `Anim` is a scene whose leaves are diagrams over scalar *terms* in one variable, the
-- parameter `now` (the value of the enclosing driver at the leaf's local time, 0 outside any).
-- `lit n` is the constant `n`, `_⊞_`/`_⊟_` and the Space and Time operations build terms; a
-- driver is a Coupling term (`move`, `tween`).  Whole ticks are written `ι n` (n/1).  `frame d l`
-- shows the leaf `l` for `d` ticks; `a ⨾ b` is `b` after `a`, `a ∥ b` together.  The leaves
-- use `Slides.Diagram.Syntax` unchanged: `rectangle (lit 40) (lit 30) style`, `beside`, `named`, ...

module Slides.Deck.Anim where

open import Data.Fin using (zero; suc)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Bool.Base using (if_then_else_)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (inj₁)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.List.Base using (List; []; _∷_; map; upTo)
open import Data.Bool.ListAction using (all)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Rational.Properties as ℚP
import Data.Rational as ℚ
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Scalar.Time using (Time)
open import Data.Container.FreeMonad using (pure; impure)

open import Container.Pick using (pick2)
open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling; ι; ratEase; ratRatio) public
open import Slides.Scalar.Space using (Plus; Minus; Max; Lt; Pct)
open import Slides.Scalar.Coupling using (Easing; Linear; Step; StepStart; Bezier) public
open import Slides.Scene.Moving ratSpace ratTime ratCoupling public
open import Slides.Scene.Syntax using (hold; delay; _⨾_; _∥_; drive; repeat) public
open import Slides.Diagram.Style using (Style; defaultStyle; stroked; filled; withId; withClass; rounded) public
import Slides.Diagram.Syntax as D

lit : ℕ → Sc
lit n = pure (just (ι n))

litQ : ℚ → Sc
litQ q = pure (just q)

-- the parameter
now : Sc
now = pure nothing

infixl 6 _⊞_ _⊟_
_⊞_ _⊟_ : Sc → Sc → Sc
a ⊞ b = impure (inj₁ Plus , pick2 a b)
a ⊟ b = impure (inj₁ Minus , pick2 a b)

-- `ifle a b x y`: `x` if `a ≤ b`, else `y`; `pctOf p x`: p percent of `x`
ifle : Sc → Sc → Sc → Sc → Sc
ifle a b x y = impure (inj₁ Lt , λ { zero → a ; (suc zero) → b ; (suc (suc zero)) → x ; (suc (suc (suc zero))) → y })

pctOf : ℕ → Sc → Sc
pctOf p x = impure (inj₁ (Pct p) , λ _ → x)

-- shown for `d` ticks
frame′ : ℕ → Leaf → Anim
frame′ d l = hold (ι d) (pure l)

-- a line of text as a leaf
txt : ℕ → String → Style → Leaf
txt size t = D.text lit 100 size t

------------------------------------------------------------------------
-- Acts and frame lists as scenes

-- a leaf from a static diagram over ℕ
liftDia : D.Dia ℕ → Leaf
liftDia = D.mapDia lit

-- nothing, for no time
idle : Anim
idle = hold (ι 0) (pure (D.spacer (lit 0) (lit 0)))

-- acts one after the other (the empty list is `idle`)
sequence : List Anim → Anim
sequence []       = idle
sequence (a ∷ []) = a
sequence (a ∷ as) = a ⨾ sequence as

-- the cumulative durations of acts: the rests of the reveal steps
rests : List Anim → List ℚ
rests = go (ι 0)
  where go : ℚ → List Anim → List ℚ
        go t []       = []
        go t (x ∷ xs) = let t′ = t ℚ.+ duration x in t′ ∷ go t′ xs

-- a list of static frames, one tick each
frames : List (D.Dia ℕ) → Anim
frames ds = sequence (map (λ d → frame′ 1 (liftDia d)) ds)

-- a flip book: `ticks` frames of `f` at the eased progress `k / ticks`, `k = 0 … ticks - 1` (the
-- raw frame list the legacy `flipTween` computed, as a scene of one-tick frames)
flipTween : ℕ → Easing → (ℚ → D.Dia ℕ) → Anim
flipTween ticks e f = frames (map (λ k → f (ratEase e (ratRatio (ι k) (ι ticks)))) (upTo ticks))

-- steps over a loop: `period` phases, each the acts `acts φ` in sequence, end to end; the rests
-- are those of phase 0 and every phase must have the same (`uniform?`, checked where it is used)
bothScene : ℕ → (ℕ → List Anim) → Anim
bothScene period acts = sequence (map (λ φ → sequence (acts φ)) (upTo period))

private
  sameRests : List ℚ → List ℚ → Bool
  sameRests []       []       = true
  sameRests (a ∷ as) (b ∷ bs) = ⌊ a ℚP.≟ b ⌋ ∧ sameRests as bs
  sameRests _        _        = false

uniform? : ℕ → (ℕ → List Anim) → Bool
uniform? period acts = all (λ φ → sameRests (rests (acts φ)) (rests (acts 0))) (upTo period)

-- the frame at a whole tick, empty when nothing is shown
layoutAt : Anim → ℕ → Layout ℚ
layoutAt a n with frame a n
... | nothing = mkLayout (ι 0) (ι 0) [] []
... | just l  = l

-- the last whole tick at which an act ending at the instant `q` is still shown
lastTick : ℚ → ℕ
lastTick q = if q ℚ.≤ᵇ ι (Time.floor ratTime q) then Time.floor ratTime q ∸ 1 else Time.floor ratTime q

-- the length of acts in sequence, and the instant zero
totalDuration : List Anim → ℚ
totalDuration as = duration (sequence as)

zeroQ : ℚ
zeroQ = ι 0
