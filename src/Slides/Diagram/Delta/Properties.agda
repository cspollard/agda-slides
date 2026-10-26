{-# OPTIONS --safe --without-K #-}

-- The round trip of `Slides.Diagram.Delta`: `patchL (diffL old new) old ≡ new`, and shipping the first frame and the
-- edits loses nothing (`replay-deltas`).
module Slides.Diagram.Delta.Properties where

open import Data.List using ([]; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram
open import Slides.DecEq

open import Slides.Diagram.Delta

------------------------------------------------------------------------
-- The round trip

patchE-diffN : ∀ a b → patchE (diffN a b) a ≡ b
patchE-diffN a b with a ≟ₑ b
... | yes eq = eq
... | no _ with setNums (trimNums (numsOf a) (numsOf b)) a ≟ₑ b
...   | yes eq = eq
...   | no _   = refl

mutual
  patchE-diffE : ∀ a b → patchE (diffE a b) a ≡ b
  patchE-diffE (group xs) b = patchE-diffG xs b
  patchE-diffE (rect v1 v2 v3 v4 v5) b = patchE-diffN (rect v1 v2 v3 v4 v5) b
  patchE-diffE (circle v1 v2 v3 v4) b = patchE-diffN (circle v1 v2 v3 v4) b
  patchE-diffE (line v1 v2 v3 v4 v5) b = patchE-diffN (line v1 v2 v3 v4 v5) b
  patchE-diffE (arrow v1 v2 v3 v4 v5) b = patchE-diffN (arrow v1 v2 v3 v4 v5) b
  patchE-diffE (label v1 v2 v3 v4 v5) b = patchE-diffN (label v1 v2 v3 v4 v5) b
  patchE-diffE (path v1 v2) b = patchE-diffN (path v1 v2) b

  patchE-diffG : ∀ xs b → patchE (diffG xs b) (group xs) ≡ b
  patchE-diffG xs (group ys) = cong group (patchL-diffL xs ys)
  patchE-diffG xs (rect v1 v2 v3 v4 v5) = patchE-diffN (group xs) (rect v1 v2 v3 v4 v5)
  patchE-diffG xs (circle v1 v2 v3 v4) = patchE-diffN (group xs) (circle v1 v2 v3 v4)
  patchE-diffG xs (line v1 v2 v3 v4 v5) = patchE-diffN (group xs) (line v1 v2 v3 v4 v5)
  patchE-diffG xs (arrow v1 v2 v3 v4 v5) = patchE-diffN (group xs) (arrow v1 v2 v3 v4 v5)
  patchE-diffG xs (label v1 v2 v3 v4 v5) = patchE-diffN (group xs) (label v1 v2 v3 v4 v5)
  patchE-diffG xs (path v1 v2) = patchE-diffN (group xs) (path v1 v2)

  patchL-diffL : ∀ xs ys → patchL (diffL xs ys) xs ≡ ys
  patchL-diffL (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (patchE-diffE x y) (patchL-diffL xs ys)
  patchL-diffL (x ∷ xs) []       = refl
  patchL-diffL []       ys       = refl

-- shipping the first frame and `deltas` loses nothing
replay-deltas : ∀ e fs → replay e (deltas e fs) ≡ fs
replay-deltas e []       = refl
replay-deltas e (f ∷ fs) rewrite patchL-diffL e f = cong (f ∷_) (replay-deltas f fs)
