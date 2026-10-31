{-# OPTIONS --safe --without-K #-}

-- Laws of the curve extension (the generic Kleisli laws, `lower-bind`, `lower-⋙` and `lower-ret`, are
-- in `Container.Lowering.Properties`).

module Slides.Diagram.Curve.Properties where

open import Data.Container.FreeMonad using (pure; impure)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Container.Lowering using (_≈⋆_)
open import Container.Sum.Properties using (lower-copairL-inl)
open import Slides.Diagram.Curve
open import Slides.Diagram.Syntax using (Dia)

-- the embedding agrees: a diagram lowered after `inject` is itself
lower-inject : ∀ {S} (sm : Sampler S) n (d : Dia S) → lowerDia sm n (inject d) ≈⋆ d
lower-inject sm n = lower-copairL-inl _
