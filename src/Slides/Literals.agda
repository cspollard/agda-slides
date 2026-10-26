{-# OPTIONS --safe --without-K #-}

-- Overloaded literals for the slide vocabulary.
--
-- A string literal at type `Text` or `Inline` is plain text; at type `Math`
-- it is an identifier, and a number literal at type `Math` is `num`.  Agda
-- resolves a literal's side condition with the instance `tt : ⊤`, which must
-- be in scope where the literal is written, and so must `fromString` and
-- `fromNat`; all are re-exported from here.  Once literals are overloaded,
-- `String` literals need an instance too.  Import this module (or
-- `Slides.DSL`, which re-exports it) once per module, never both
-- `Data.String.Literals` / `Data.Nat.Literals` and this.

module Slides.Literals where

open import Agda.Builtin.FromNat using (Number; fromNat) public
open import Agda.Builtin.FromString using (IsString; fromString) public
open import Data.List using (_∷_; [])
open import Data.String using (String)
open import Data.Unit using (⊤) public
import Data.String.Literals
import Data.Nat.Literals
open import Data.Nat using (ℕ)

open import Slides.Core using (Inline; Text; text)
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
