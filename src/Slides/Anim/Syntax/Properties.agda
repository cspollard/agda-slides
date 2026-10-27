{-# OPTIONS --safe --without-K #-}

-- Laws of the animation syntax: `foldA` commutes with `>>=`, and the durations of the connectives, of `pad` and of `par`.
module Slides.Anim.Syntax.Properties where

open import Data.Fin using (zero; suc)
open import Data.Nat using (_+_; _⊔_; _∸_; _≤_; _<ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Data.Bool using (T)
open import Data.Unit using (tt)

open import Slides.Diagram.Scalar using (Ops)
import Slides.Anim.Track as T
open import Data.Integer as ℤ using ()

open import Slides.Anim.Syntax

-- `foldA` commutes with `>>=` (a tween is a bind): substituting then folding is
-- folding with the folded substitution.  No extensionality is needed because
-- `Fin 2` continuations are applied at `zero` and `suc zero` only.
foldA-bind : ∀ {T U A : Set} (leaf : U → A) sq pr (m : AnimC ⋆ T) (g : T → AnimC ⋆ U) →
             foldA leaf sq pr (m >>= g) ≡ foldA (λ t → foldA leaf sq pr (g t)) sq pr m
foldA-bind leaf sq pr (pure t) g = refl
foldA-bind leaf sq pr (impure (Seq , k)) g =
  cong₂ sq (foldA-bind leaf sq pr (k zero) g) (foldA-bind leaf sq pr (k (suc zero)) g)
foldA-bind leaf sq pr (impure (Par , k)) g =
  cong₂ pr (foldA-bind leaf sq pr (k zero) g) (foldA-bind leaf sq pr (k (suc zero)) g)

dur-⨾ : ∀ {S} (a b : Anim S (Seg S)) → dur (a ⨾ b) ≡ dur a + dur b
dur-⨾ a b = refl

dur-∥ : ∀ {S} (a b : Anim S (Seg S)) → dur (a ∥ᵃ b) ≡ dur a ⊔ dur b
dur-∥ a b = refl

dur-none : ∀ {S} (O : Ops S) n → dur (none O n) ≡ n
dur-none O n = refl

dur-pad : ∀ {S} (O : Ops S) n (a : Anim S (Seg S)) → dur (pad O n a) ≡ dur a ⊔ n
dur-pad O n a with dur a <ᵇ n in eq
... | true  = trans (ℕP.m+[n∸m]≡n lt) (sym (ℕP.m≤n⇒m⊔n≡n lt))
  where lt = ℕP.<⇒≤ (ℕP.<ᵇ⇒< (dur a) n (subst T (sym eq) tt))
... | false = sym (ℕP.m≥n⇒m⊔n≡m (ℕP.≮⇒≥ (λ h → subst T eq (ℕP.<⇒<ᵇ h))))

-- the two sides of `par` last equally long, and as long as the longer input
par-balanced : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) → dur (pad O (dur b) a) ≡ dur (pad O (dur a) b)
par-balanced O a b = trans (dur-pad O (dur b) a) (trans (ℕP.⊔-comm (dur a) (dur b)) (sym (dur-pad O (dur a) b)))

dur-par : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) → dur (par O a b) ≡ dur a ⊔ dur b
dur-par O a b = trans (cong₂ _⊔_ (dur-pad O (dur b) a) (dur-pad O (dur a) b))
                      (trans (cong ((dur a ⊔ dur b) ⊔_) (ℕP.⊔-comm (dur b) (dur a)))
                             (ℕP.⊔-idem (dur a ⊔ dur b)))
