{-# OPTIONS --safe --without-K #-}

-- A discrete template is an ordered one, sampled at ticks.
--
-- `Slides.Diagram.Euclid.DExpr` (read in ℕ at a tick) translates to `QExpr` (read in ℚ) along
-- the container morphism `dToQ`; the translation is `Container.Lowering.translate`, so it
-- is a monad morphism (`Signature.weaken-bind`) and evaluating it is folding with the restricted
-- handler (`Signature.foldT-translate`).  The theorem is the analogue of
-- `Slides.Diagram.Expr.Properties.Faithful.faithful`: `ι (evalD natD ρ e) ≡ evalQ ratQ (ι ∘ ρ)
-- (toQ e)`, with side conditions only at the core and sub nodes (exact percentages, minuend ≥
-- subtrahend; those of `Faithful`); the ordered nodes (`Lt`, `DivBy`, `ModBy`, `MulLit`) have none.
module Slides.Spike.Ordered.Properties.Discrete where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Shape; Position)
open import Data.Container.FreeMonad using (pure; impure)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Diagram.Signature
open import Slides.Diagram.Signature.Properties using (foldT-translate)
open import Slides.Diagram.Expr using (opsH; ExprOp; exprArity)
open import Slides.Diagram.Expr.Properties.Faithful using (ExprSide; ι-node)
open import Slides.Diagram.Euclid
open import Slides.Spike.Ordered
open import Slides.Spike.Ordered.Properties

-- the side conditions of a node: those of the core and sub layers only
DSide : (s : Shape DExprC) → (Position DExprC s → ℕ) → Set
DSide (inj₁ s) k = ExprSide s k
DSide (inj₂ _) k = ⊤

FaithfulD : ∀ {V} → (V → ℕ) → DExpr V → Set
FaithfulD ρ (pure v)         = ⊤
FaithfulD ρ (impure (s , k)) = (∀ q → FaithfulD ρ (k q)) × DSide s (λ q → evalD natD ρ (k q))

-- one node: `ι` commutes with the handler of the translation
node-ι : ∀ s (k : Position DExprC s → ℕ) → DSide s k →
         ι (dH natD .Handler.handle s k) ≡ restrict dToQ (qH ratQ) .Handler.handle s (λ q → ι (k q))
node-ι (inj₁ s)          k ex = ι-node s k ex
node-ι (inj₂ (DivBy d))  k _  = ι-divBy d (k tt)
node-ι (inj₂ (ModBy d))  k _  = ι-modBy d (k tt)
node-ι (inj₂ (MulLit n)) k _  = ι-mulLit n (k tt)
node-ι (inj₂ Lt) k _          = IsOrdHom.h-lt ι-ord (k zero) (k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))

-- a discrete template at a tick is its translation at `ι` of the tick
faithful-D : ∀ {V} (ρ : V → ℕ) (e : DExpr V) → FaithfulD ρ e →
             ι (evalD natD ρ e) ≡ evalQ ratQ (ι ∘ ρ) (toQ e)
faithful-D ρ e f = trans (go e f) (sym (foldT-translate dToQ (qH ratQ) (ι ∘ ρ) e))
  where
    go : ∀ e → FaithfulD ρ e → ι (evalD natD ρ e) ≡ foldT (restrict dToQ (qH ratQ)) (ι ∘ ρ) e
    go (pure v)         _        = refl
    go (impure (s , k)) (f , ex) =
      trans (node-ι s (λ q → evalD natD ρ (k q)) ex)
            (restrict dToQ (qH ratQ) .Handler.respects s (λ q → go (k q) (f q)))
