{-# OPTIONS --safe --without-K #-}

-- The Pairs diagrams lay out identically in ℕ and in ℤ (checked by evaluation).

module Slides.Examples.PairsScalar where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Diagram.Layout using (module LayoutWith; compile)
open import Slides.Diagram.Scalar using (intOps)
open import Slides.Examples.Pairs

private
  module Z = LayoutWith intOps

_ : Z.compile "d-problem" 100 problemDia ≡ compile "d-problem" 100 problemDia
_ = refl
_ : Z.compile "d-pipeline" 100 pipelineDia ≡ compile "d-pipeline" 100 pipelineDia
_ = refl
_ : Z.compile "d-stages" 100 stagesDia ≡ compile "d-stages" 100 stagesDia
_ = refl
_ : Z.compile "d-chain" 100 chainDia ≡ compile "d-chain" 100 chainDia
_ = refl
_ : Z.compile "d-results" 100 resultsDia ≡ compile "d-results" 100 resultsDia
_ = refl
_ : Z.compile "d-tiles" 100 tilesDia ≡ compile "d-tiles" 100 tilesDia
_ = refl
