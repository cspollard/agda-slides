{-# OPTIONS --safe --without-K #-}

-- Checks on the Pairs diagrams, by evaluation:
--   * they lay out identically in ℕ, ℤ and ℚ;
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
open import Slides.Diagram.Scalar using (Ops; intOps; natOps; ratOps)
open import Data.Nat using (ℕ)
open import Slides.Examples.Pairs

private
  module Z = LayoutWith intOps
  module Q = LayoutWith ratOps

_ : Z.compile "d-problem" 100 (mapDia (Ops.fromℕ intOps) problemDia) ≡ compile "d-problem" 100 problemDia
_ = refl
_ : Z.compile "d-pipeline" 100 (mapDia (Ops.fromℕ intOps) pipelineDia) ≡ compile "d-pipeline" 100 pipelineDia
_ = refl
_ : Z.compile "d-stages" 100 (mapDia (Ops.fromℕ intOps) stagesDia) ≡ compile "d-stages" 100 stagesDia
_ = refl
_ : Z.compile "d-chain" 100 (mapDia (Ops.fromℕ intOps) chainDia) ≡ compile "d-chain" 100 chainDia
_ = refl
_ : Z.compile "d-results" 100 (mapDia (Ops.fromℕ intOps) resultsDia) ≡ compile "d-results" 100 resultsDia
_ = refl
_ : Z.compile "d-tiles" 100 (mapDia (Ops.fromℕ intOps) tilesDia) ≡ compile "d-tiles" 100 tilesDia
_ = refl

_ : Q.compile "d-problem" 100 (mapDia (Ops.fromℕ ratOps) problemDia) ≡ compile "d-problem" 100 problemDia
_ = refl
_ : Q.compile "d-pipeline" 100 (mapDia (Ops.fromℕ ratOps) pipelineDia) ≡ compile "d-pipeline" 100 pipelineDia
_ = refl
_ : Q.compile "d-stages" 100 (mapDia (Ops.fromℕ ratOps) stagesDia) ≡ compile "d-stages" 100 stagesDia
_ = refl
_ : Q.compile "d-chain" 100 (mapDia (Ops.fromℕ ratOps) chainDia) ≡ compile "d-chain" 100 chainDia
_ = refl
_ : Q.compile "d-results" 100 (mapDia (Ops.fromℕ ratOps) resultsDia) ≡ compile "d-results" 100 resultsDia
_ = refl
_ : Q.compile "d-tiles" 100 (mapDia (Ops.fromℕ ratOps) tilesDia) ≡ compile "d-tiles" 100 tilesDia
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
scoped : Dia ℕ
scoped = (("a" ⦂ rectangle 10 10 defaultStyle) ▹ "a" ⟶ "b" ∶ defaultStyle) ∥ ("b" ⦂ rectangle 10 10 defaultStyle)

_ : dangling scoped ≡ "b" ∷ []
_ = refl
