{-# OPTIONS --safe --without-K #-}

-- A discrete template is an ordered one, sampled at ticks (layers: core, Sub, Ord, Floor; Pct).
--
-- `lowerO` sends `Sub a b` to `(a ⊔ b) − b` and `Pct p x` to `⌊p·x/100⌋`, every other node to its
-- namesake.  Two theorems, neither with a hypothesis:
--
--   * `lower-ℕ`: lowering does not change the ℕ reading (the monus is `(a ⊔ b) ∸ b`, the
--     percentage rounds down);
--   * `discrete-is-ordered`: the ℕ reading, sent through `ι`, is the ℚ reading of the lowered
--     term at `ι ∘ ρ`.  It is the analogue of `Slides.Diagram.Expr.Properties.Faithful.faithful`
--     with its side conditions removed: the ordered nodes are `ι`-homomorphisms (`ι-ord`,
--     `ι-floor`) and the other two are lowered.
module Slides.Diagram.Ordered.Properties.Discrete where

open import Data.Nat as ℕ using (ℕ; suc; _∸_; _*_; _/_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_)
open import Data.Fin using (zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.Core using (Position)
open import Data.Container.FreeMonad using (pure; impure)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-⊔)
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr using (Zero; Lit; Plus; Max; Pct; Sub)
open import Slides.Diagram.Ordered
open import Slides.Diagram.Ordered.Properties
open import Slides.Diagram.Ordered.Properties.Laws using (pull; foldT-lower)

-- the handler of the lowering, at ℕ, is the handler of ℕ
private
  max-monus : ∀ a b → (a ℕ.⊔ b) ∸ b ≡ a ∸ b
  max-monus ℕ.zero    b       = trans (cong (_∸ b) (ℕP.⊔-identityˡ b)) (trans (ℕP.n∸n≡0 b) (sym (ℕP.0∸n≡0 b)))
  max-monus (suc a)   ℕ.zero  = ℕP.⊔-identityʳ (suc a)
  max-monus (suc a)   (suc b) = max-monus a b

node-ℕ : ∀ s (k : Position OC s → ℕ) → pull lowerO (oH natO) .Handler.handle s k ≡ oH natO .Handler.handle s k
node-ℕ (inj₁ (inj₁ Zero))    k = refl
node-ℕ (inj₁ (inj₁ (Lit n))) k = refl
node-ℕ (inj₁ (inj₁ Plus))    k = refl
node-ℕ (inj₁ (inj₁ Max))     k = refl
node-ℕ (inj₁ (inj₁ (Pct p))) k = cong (_/ 100) (ℕP.*-comm p (k tt))
node-ℕ (inj₁ (inj₂ Sub))     k = max-monus (k zero) (k (suc zero))
node-ℕ (inj₂ s)              k = refl

lower-ℕ : ∀ {V} (ρ : V → ℕ) (e : OExpr V) → evalO natO ρ (lowerQ e) ≡ evalO natO ρ e
lower-ℕ ρ e = trans (foldT-lower lowerO (oH natO) ρ e) (go e)
  where
    go : ∀ e → foldT (pull lowerO (oH natO)) ρ e ≡ evalO natO ρ e
    go (pure v)         = refl
    go (impure (s , k)) =
      trans (pull lowerO (oH natO) .Handler.respects s (λ q → go (k q))) (node-ℕ s (λ q → evalO natO ρ (k q)))

-- one node: the program a node is lowered to computes the ℕ value, read in ℚ
node-ι : ∀ s (k : Position OC s → ℕ) →
         ι (oH natO .Handler.handle s k) ≡ pull lowerO (oH ratO) .Handler.handle s (λ q → ι (k q))
node-ι (inj₁ (inj₁ Zero))    k = refl
node-ι (inj₁ (inj₁ (Lit n))) k = refl
node-ι (inj₁ (inj₁ Plus))    k = ι-+ (k zero) (k (suc zero))
node-ι (inj₁ (inj₁ Max))     k = ι-⊔ (k zero) (k (suc zero))
node-ι (inj₁ (inj₁ (Pct p))) k = ι-pct p (k tt)
node-ι (inj₁ (inj₂ Sub))     k = ι-monus (k zero) (k (suc zero))
node-ι (inj₂ (inj₁ Lt))      k = IsOrdHom.h-lt ι-ord (k zero) (k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))
node-ι (inj₂ (inj₁ Min))     k = IsOrdHom.h-min ι-ord (k zero) (k (suc zero))
node-ι (inj₂ (inj₂ (DivBy d)))  k = IsFloorHom.h-divBy ι-floor d (k tt)
node-ι (inj₂ (inj₂ (ModBy d)))  k = IsFloorHom.h-modBy ι-floor d (k tt)
node-ι (inj₂ (inj₂ (MulLit n))) k = IsFloorHom.h-mulLit ι-floor n (k tt)

-- A discrete template at a tick is its lowering at `ι` of the tick: for every template and tick.
discrete-is-ordered : ∀ {V} (ρ : V → ℕ) (e : OExpr V) →
                      ι (evalO natO ρ e) ≡ evalO ratO (ι ∘ ρ) (lowerQ e)
discrete-is-ordered ρ e = trans (go e) (sym (foldT-lower lowerO (oH ratO) (ι ∘ ρ) e))
  where
    go : ∀ e → ι (evalO natO ρ e) ≡ foldT (pull lowerO (oH ratO)) (ι ∘ ρ) e
    go (pure v)         = refl
    go (impure (s , k)) =
      trans (node-ι s (λ q → evalO natO ρ (k q)))
            (pull lowerO (oH ratO) .Handler.respects s (λ q → go (k q)))
