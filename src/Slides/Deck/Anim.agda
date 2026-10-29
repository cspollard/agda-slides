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
open import Data.Nat.Base using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (inj₁)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Container.FreeMonad using (pure; impure)

open import Container.Pick using (pick2)
open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling; ι) public
open import Slides.Scalar.Space using (Plus; Minus; Max)
open import Slides.Scalar.Coupling using (Easing; Linear; Step; StepStart; Bezier) public
open import Slides.Scene.Moving ratSpace ratTime ratCoupling public
open import Slides.Scene.Syntax using (hold; delay; _⨾_; _∥_; drive; repeat) public
open import Slides.Diagram.Style using (Style; defaultStyle; stroked; filled; withId) public
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

-- shown for `d` ticks
frame′ : ℕ → Leaf → Anim
frame′ d l = hold (ι d) (pure l)

-- a line of text as a leaf
txt : ℕ → String → Style → Leaf
txt size t = D.text lit 100 size t
