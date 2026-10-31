{-# OPTIONS --safe --without-K #-}

-- `bind` on trees respects `Eq` and satisfies the unit and associativity laws.  (The monad on
-- setoids is `Alg.FreeMonad`, from the adjunction `Free ⊣ Forget`; bind is its fold.)

module Container.FreeMonad.Properties where

open import Level using (Level; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)


open import Container.FreeMonad

private
  variable
    s p c ℓ : Level


module _ {C : Container s p}
         {a ℓa b ℓb} {A : Setoid a ℓa} {B : Setoid b ℓb} where
  private
    module A = Setoid A
    module B = Setoid B

  bind-cong : ∀ {t u : C ⋆ A.Carrier} {f g : A.Carrier → C ⋆ B.Carrier} →
              Eq A t u → (∀ {x y} → x A.≈ y → Eq B (f x) (g y)) →
              Eq B (t >>= f) (u >>= g)
  bind-cong {pure _}         {pure _}         (lift e)    h = h e
  bind-cong {pure _}         {impure _}       ()
  bind-cong {impure _}       {pure _}         ()
  bind-cong {impure (_ , _)} {impure (_ , _)} (refl , k≈) h =
    refl , λ q → bind-cong (k≈ q) h

bind-pure : ∀ {C : Container s p} {a ℓa} (A : Setoid a ℓa)
            (t : C ⋆ Setoid.Carrier A) → Eq A (t >>= pure) t
bind-pure A (pure _)         = lift (Setoid.refl A)
bind-pure A (impure (_ , k)) = refl , λ q → bind-pure A (k q)

bind-assoc : ∀ {C : Container s p} {a ℓa b ℓb d ℓd}
             (A : Setoid a ℓa) (B : Setoid b ℓb) (D : Setoid d ℓd)
             (t : C ⋆ Setoid.Carrier A)
             (f : Setoid.Carrier A → C ⋆ Setoid.Carrier B)
             (g : Setoid.Carrier B → C ⋆ Setoid.Carrier D) →
             Eq D ((t >>= f) >>= g) (t >>= λ x → f x >>= g)
bind-assoc A B D (pure _)         f g = refl⋆ D (f _ >>= g)
bind-assoc A B D (impure (_ , k)) f g = refl , λ q → bind-assoc A B D (k q) f g
