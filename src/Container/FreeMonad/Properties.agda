{-# OPTIONS --safe --without-K #-}

-- The free monad is a monad: `bind` respects equality of trees and satisfies the unit and associativity laws, the functor `Free C`,
-- the laws of `join`, and the monad `FreeMonad c ℓ C` on setoids.
module Container.FreeMonad.Properties where

open import Level using (Level; _⊔_; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Base using (id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using ()
import Categories.NaturalTransformation.Core as NT

open import Container.FreeMonad

private
  variable
    s p c ℓ : Level

------------------------------------------------------------------------
-- Properties of bind

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

------------------------------------------------------------------------
-- The free monad as a functor on Setoids

Free₁ : ∀ (C : Container s p) {X Y : Setoid c ℓ} →
        Func X Y → Func (Free₀ C X) (Free₀ C Y)
Free₁ C {X} {Y} g = record
  { to   = λ t → t >>= λ x → pure {C = C} (g ⟨$⟩ x)
  ; cong = λ {t} {u} e →
      bind-cong {C = C} {A = X} {B = Y} e (λ x≈y → lift (Func.cong g x≈y))
  }

Free : (C : Container s p) →
       Functor (Setoids c ℓ) (Setoids (c ⊔ s ⊔ p) (ℓ ⊔ s ⊔ p))
Free C = record
  { F₀           = Free₀ C
  ; F₁           = Free₁ C
  ; identity     = λ {A} {t} → bind-pure A t
  ; homomorphism = λ {X} {Y} {Z} {f} {g} {t} →
      sym⋆ Z (bind-assoc {C = C} X Y Z t (λ x → pure {C = C} (f ⟨$⟩ x))
                                     (λ y → pure {C = C} (g ⟨$⟩ y)))
  ; F-resp-≈     = λ {X} {Y} {f} {g} f≈g {t} →
      bind-cong {C = C} {A = X} {B = Y} (refl⋆ X t)
        (λ {x} {y} x≈y → lift (Setoid.trans Y (f≈g {x}) (Func.cong g x≈y)))
  }

-- Laws, as statements about equality of trees.

module _ {C : Container s p} {a ℓa b ℓb} (X : Setoid a ℓa) (Y : Setoid b ℓb) where
  private
    module X = Setoid X
    module Y = Setoid Y
    FX = Free₀ C X
    FY = Free₀ C Y

  join-natural : (f : Func X Y) (tt : C ⋆ (C ⋆ X.Carrier)) →
                 Eq Y (join (fmap (fmap (f ⟨$⟩_)) tt)) (fmap (f ⟨$⟩_) (join tt))
  join-natural f tt =
    trans⋆ Y (bind-assoc FX FY Y tt (λ t → pure (fmap (f ⟨$⟩_) t)) id)
             (sym⋆ Y (bind-assoc FX X Y tt id (λ x → pure (f ⟨$⟩ x))))

module _ {C : Container s p} {a ℓa} (X : Setoid a ℓa) where
  private FX = Free₀ C X

  join-assoc : (ttt : C ⋆ (C ⋆ (C ⋆ Setoid.Carrier X))) →
               Eq X (join (fmap join ttt)) (join (join ttt))
  join-assoc ttt =
    trans⋆ X (bind-assoc (Free₀ C FX) FX X ttt (λ tt → pure (join tt)) id)
             (sym⋆ X (bind-assoc (Free₀ C FX) FX X ttt id id))

  join-fmap-pure : (t : C ⋆ Setoid.Carrier X) →
                   Eq X (join (fmap pure t)) t
  join-fmap-pure t =
    trans⋆ X (bind-assoc X FX X t (λ x → pure (pure x)) id) (bind-pure X t)

-- `Free C` is an endofunctor on `Setoids c′ ℓ′` once the levels of the
-- container are absorbed: `c′ = c ⊔ s ⊔ p`, `ℓ′ = ℓ ⊔ s ⊔ p`.

FreeMonad : ∀ {s p} c ℓ (C : Container s p) →
            Monad (Setoids (c ⊔ s ⊔ p) (ℓ ⊔ s ⊔ p))
FreeMonad c ℓ C = record
  { F         = Free C
  ; η         = record
      { η           = λ X → record { to = pure ; cong = lift }
      ; commute     = λ {_} {Y} _ {_} → lift (Setoid.refl Y)
      ; sym-commute = λ {_} {Y} _ {_} → lift (Setoid.refl Y)
      }
  ; μ         = record
      { η           = λ X → record
          { to   = join
          ; cong = λ {t} {u} e → bind-cong {C = C} {A = Free₀ C X} {B = X} e id
          }
      ; commute     = λ {X} {Y} f {tt} → join-natural X Y f tt
      ; sym-commute = λ {X} {Y} f {tt} → sym⋆ Y (join-natural X Y f tt)
      }
  ; assoc     = λ {X} {ttt} → join-assoc X ttt
  ; sym-assoc = λ {X} {ttt} → sym⋆ X (join-assoc X ttt)
  ; identityˡ = λ {X} {t} → join-fmap-pure X t
  ; identityʳ = λ {X} {t} → refl⋆ X t
  }
