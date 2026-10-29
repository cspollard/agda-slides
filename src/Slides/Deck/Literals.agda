{-# OPTIONS --safe --without-K #-}

-- Overloaded literals for the authoring vocabulary: a string literal at `Text` or `Inline` is plain
-- text, at `Math` an identifier; a number literal at `Math` is `num`.  This is the one place
-- instance arguments appear, and only because Agda's literal overloading is instance
-- resolution: four non-overlapping instances of `IsString`/`Number`, never used by the
-- core (`Slides.Deck.Content` and below).  Import this module (or `Slides.Deck.DSL`) once per
-- module, not together with `Data.String.Literals` or `Data.Nat.Literals`.

module Slides.Deck.Literals where

open import Agda.Builtin.FromNat using (Number; fromNat) public
open import Agda.Builtin.FromString using (IsString; fromString) public
open import Data.List.Base using (_∷_; [])
open import Data.String.Base using (String)
open import Data.Unit using (⊤) public
import Data.String.Literals
import Data.Nat.Literals
open import Data.Nat.Base using (ℕ)

open import Slides.Deck.Content using (Inline; Text; text)
open import Slides.Math using (Math; var; num)

instance
  isStringString : IsString String
  isStringString = Data.String.Literals.isString

  numberNat : Number ℕ
  numberNat = Data.Nat.Literals.number

  isStringInline : IsString Inline
  isStringInline = record { Constraint = λ _ → ⊤ ; fromString = λ s → text s }

  isStringText : IsString Text
  isStringText = record { Constraint = λ _ → ⊤ ; fromString = λ s → text s ∷ [] }

  isStringMath : IsString Math
  isStringMath = record { Constraint = λ _ → ⊤ ; fromString = λ s → var s }

  numberMath : Number Math
  numberMath = record { Constraint = λ _ → ⊤ ; fromNat = λ n → num n }
