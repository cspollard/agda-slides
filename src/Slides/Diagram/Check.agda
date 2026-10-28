{-# OPTIONS --safe --without-K #-}

-- Computation check over ℕ: two named boxes side by side, joined by an arrow.  The size, the
-- names and the single arrow all reduce by `refl`, and the print type-checks.

module Slides.Diagram.Check where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.XML.AST using (XMLM)

open import Slides.Scalar.Model.Nat using (natSpace)
open import Slides.Diagram.Style using (defaultStyle)
open import Slides.Diagram.Draw
open import Slides.Diagram.Syntax
open import Slides.Diagram.Layout natSpace using (layout)
open import Slides.Diagram.Names using (dangling)
open import Slides.Diagram.Laws natSpace using (size)
open import Slides.Diagram.Print using (renderSVG; natPrint)

box₁ box₂ : Dia ℕ
box₁ = named "a" (rectangle 4 2 defaultStyle)
box₂ = named "b" (rectangle 6 3 defaultStyle)

pair : Dia ℕ
pair = connect "a" east "b" west defaultStyle (beside box₁ box₂)

_ : size pair ≡ (10 , 3)
_ = refl

_ : dangling pair ≡ []
_ = refl

_ : dangling (connect "a" east "c" west defaultStyle box₁) ≡ "c" ∷ []
_ = refl

-- `a` is centred in the height of `b` (positions are in half units), and the arrow joins the
-- midpoints of a's east edge and b's west edge
_ : Layout.draws (layout pair) ≡
      rect 0 1 4 2 defaultStyle ∷ rect 8 0 6 3 defaultStyle
    ∷ arrow 8 3 8 3 defaultStyle ∷ []
_ = refl

_ : XMLM ℕ
_ = renderSVG natPrint "pair" 50 (layout pair)
