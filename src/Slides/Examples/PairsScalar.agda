{-# OPTIONS --safe --without-K #-}

-- Checks on the Pairs diagrams, by evaluation:
--   * they lay out identically in ℕ and in ℤ;
--   * `dangling` being empty means every connection is drawn (`soundness`);
--   * `dangling` resolves a connection inside its own diagram: a name declared
--     next to a `connect`, not under it, is reported.

module Slides.Examples.PairsScalar where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List using (_∷_; [])

open import Slides.Diagram using (defaultStyle)
open import Slides.Diagram.Layout using (module LayoutWith; compile)
open import Slides.Diagram.Names using (dangling)
import Slides.Diagram.NamesSound as Sound
open import Slides.Diagram.Notation
open import Slides.Diagram.Scalar using (intOps; natOps)
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

private
  module N = Sound natOps

_ : N.Draws problemDia
_ = N.soundness problemDia refl
_ : N.Draws pipelineDia
_ = N.soundness pipelineDia refl
_ : N.Draws stagesDia
_ = N.soundness stagesDia refl
_ : N.Draws chainDia
_ = N.soundness chainDia refl

-- "b" is declared next to the connection, not under it: it draws nothing
scoped : Dia
scoped = (("a" ⦂ rectangle 10 10 defaultStyle) ▹ "a" ⟶ "b" ∶ defaultStyle) ∥ ("b" ⦂ rectangle 10 10 defaultStyle)

_ : dangling scoped ≡ "b" ∷ []
_ = refl
