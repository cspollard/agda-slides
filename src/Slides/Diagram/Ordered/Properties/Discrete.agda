{-# OPTIONS --safe --without-K #-}

-- A discrete template is an ordered one, sampled at ticks (layers: core, Sub, Ord, Floor; Pct).
--
-- `Slides.Diagram.Euclid.DExpr` (read in ℕ at a tick) lowers to `QExpr` (read in ℚ): `Sub a b` to
-- `max (a − b) 0` and `Pct p x` to `⌊p·x/100⌋`, every other node to its namesake.  The theorem
-- `discrete-is-ordered`, with no hypothesis, is the analogue of
-- `Slides.Diagram.Expr.Properties.Faithful.faithful` with its side conditions removed: the
-- ordered nodes are `ι`-homomorphisms (`ι-ord`, `ι-floor`) and the other two are lowered.
module Slides.Diagram.Ordered.Properties.Discrete where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Position)
open import Data.Product using (_,_)
open import Data.Container.FreeMonad using (pure; impure)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr using (Zero; Lit; Plus; Max; Pct; Sub)
open import Slides.Diagram.Euclid
open import Slides.Diagram.Ordered
open import Slides.Diagram.Ordered.Properties
open import Slides.Diagram.Ordered.Properties.Laws using (pull; foldT-lower)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-⊔)

-- one node: the program a node is lowered to computes the ℕ value, read in ℚ
node-ι : ∀ s (k : Position DExprC s → ℕ) →
          ι (dH natD .Handler.handle s k) ≡ pull lowerD (qH ratQ) .Handler.handle s (λ q → ι (k q))
node-ι (inj₁ (inj₁ Zero))    k = refl
node-ι (inj₁ (inj₁ (Lit n))) k = refl
node-ι (inj₁ (inj₁ Plus))    k = ι-+ (k zero) (k (suc zero))
node-ι (inj₁ (inj₁ Max))     k = ι-⊔ (k zero) (k (suc zero))
node-ι (inj₁ (inj₁ (Pct p))) k = ι-pct p (k tt)
node-ι (inj₁ (inj₂ Sub))     k = ι-monus (k zero) (k (suc zero))
node-ι (inj₂ (DivBy d))      k = ι-divBy d (k tt)
node-ι (inj₂ (ModBy d))      k = ι-modBy d (k tt)
node-ι (inj₂ (MulLit n))     k = ι-mulLit n (k tt)
node-ι (inj₂ Lt)             k = IsOrdHom.h-lt ι-ord (k zero) (k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))

-- A discrete template at a tick is its lowering at `ι` of the tick: for every template and tick.
discrete-is-ordered : ∀ {V} (ρ : V → ℕ) (e : DExpr V) →
                      ι (evalD natD ρ e) ≡ evalQ ratQ (ι ∘ ρ) (lowerQ e)
discrete-is-ordered ρ e = trans (go e) (sym (foldT-lower lowerD (qH ratQ) (ι ∘ ρ) e))
  where
    go : ∀ e → ι (evalD natD ρ e) ≡ foldT (pull lowerD (qH ratQ)) (ι ∘ ρ) e
    go (pure v)         = refl
    go (impure (s , k)) =
      trans (node-ι s (λ q → evalD natD ρ (k q)))
            (pull lowerD (qH ratQ) .Handler.respects s (λ q → go (k q)))
