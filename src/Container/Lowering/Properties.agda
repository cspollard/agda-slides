{-# OPTIONS --safe --without-K #-}

-- Laws of lowerings: equality of programs, `lower` is a monad morphism, lowerings compose and the identity is `ret`
-- (`lower-ret`, `lower-⋙`), lowering along `embed m` is translation (`lower-embed`), and fusion (`lower-fusion`).
module Container.Lowering.Properties where

open import Level using (Level; 0ℓ; _⊔_; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Position; _⇒_; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.PropositionalEquality using (setoid)

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

open import Container.Lowering

private
  variable
    s p c a b d : Level

------------------------------------------------------------------------
-- Equality of programs

infix 4 _≈⋆_

_≈⋆_ : ∀ {C : Container s p} {X : Set c} → C ⋆ X → C ⋆ X → Set (c ⊔ s ⊔ p)
_≈⋆_ {C = C} {X = X} = Eq {C = C} (setoid X)

refl≈ : ∀ {C : Container s p} {X : Set c} (t : C ⋆ X) → t ≈⋆ t
refl≈ {X = X} = refl⋆ (setoid X)

sym≈ : ∀ {C : Container s p} {X : Set c} {t u : C ⋆ X} → t ≈⋆ u → u ≈⋆ t
sym≈ {X = X} = sym⋆ (setoid X)

trans≈ : ∀ {C : Container s p} {X : Set c} {t u v : C ⋆ X} → t ≈⋆ u → u ≈⋆ v → t ≈⋆ v
trans≈ {X = X} = trans⋆ (setoid X)

bind-cong≈ : ∀ {C : Container s p} {A : Set a} {B : Set b} {t u : C ⋆ A} {f g : A → C ⋆ B} →
             t ≈⋆ u → (∀ x → f x ≈⋆ g x) → (t >>= f) ≈⋆ (u >>= g)
bind-cong≈ {A = A} {B = B} e h =
  bind-cong {A = setoid A} {B = setoid B} e (λ { {x} refl → h x })

bind-pure≈ : ∀ {C : Container s p} {A : Set a} (t : C ⋆ A) → (t >>= pure) ≈⋆ t
bind-pure≈ {A = A} = bind-pure (setoid A)

bind-assoc≈ : ∀ {C : Container s p} {A : Set a} {B : Set b} {D : Set d} (t : C ⋆ A)
              (f : A → C ⋆ B) (g : B → C ⋆ D) →
              ((t >>= f) >>= g) ≈⋆ (t >>= λ x → f x >>= g)
bind-assoc≈ {A = A} {B} {D} = bind-assoc (setoid A) (setoid B) (setoid D)

-- Two lowerings are equal when they lower every command to equal programs.
infix 4 _≈ˡ_

_≈ˡ_ : ∀ {C D : Container s p} → Lowering C D → Lowering C D → Set (s ⊔ p)
l ≈ˡ m = ∀ a → l a ≈⋆ m a

------------------------------------------------------------------------
-- Laws

module _ {C D : Container s p} where

  -- `lower` is a monad morphism: it preserves bind (and `pure`, on the nose).
  lower-bind : ∀ {X : Set a} {Y : Set b} (l : Lowering C D) (t : C ⋆ X) (f : X → C ⋆ Y) →
               lower l (t >>= f) ≈⋆ (lower l t >>= λ x → lower l (f x))
  lower-bind l (pure x)         f = refl≈ _
  lower-bind l (impure (a , k)) f =
    trans≈ (bind-cong≈ (refl≈ (l a)) (λ q → lower-bind l (k q) f))
           (sym≈ (bind-assoc≈ (l a) (λ q → lower l (k q)) (λ x → lower l (f x))))

  -- Lowering respects equality of programs and of lowerings.
  lower-cong : ∀ {X : Set c} {l m : Lowering C D} → l ≈ˡ m → {t u : C ⋆ X} → t ≈⋆ u →
               lower l t ≈⋆ lower m u
  lower-cong l≈m {pure _}         {pure _}         e        = e
  lower-cong l≈m {pure _}         {impure _}       ()
  lower-cong l≈m {impure _}       {pure _}         ()
  lower-cong l≈m {impure (a , k)} {impure (.a , k′)} (refl , e) =
    bind-cong≈ (l≈m a) (λ q → lower-cong l≈m (e q))

module _ {C : Container s p} {X : Set c} where

  lower-ret : (t : C ⋆ X) → lower ret t ≈⋆ t
  lower-ret (pure _)         = lift refl
  lower-ret (impure (a , k)) = refl , λ q → lower-ret (k q)

module _ {C D E : Container s p} {X : Set c} where

  lower-⋙ : (l : Lowering C D) (m : Lowering D E) (t : C ⋆ X) →
            lower (l ⋙ m) t ≈⋆ lower m (lower l t)
  lower-⋙ l m (pure _)         = lift refl
  lower-⋙ l m (impure (a , k)) =
    trans≈ (bind-cong≈ (refl≈ (lower m (l a))) (λ q → lower-⋙ l m (k q)))
           (sym≈ (lower-bind m (l a) (λ q → lower l (k q))))

lower-embed : ∀ {C D : Container s p} {X : Set c} (m : C ⇒ D) (t : C ⋆ X) →
              lower (embed m) t ≈⋆ translate m t
lower-embed m (pure _)         = lift refl
lower-embed m (impure (a , k)) = refl , λ q → lower-embed m (k (position m q))

------------------------------------------------------------------------
-- Fusion

module FoldLemmas {s p} (c ℓ : Level) (C : Container s p) where
  open Alg c ℓ C

  -- Folds with pointwise equal leaves agree.
  fold-ext : (A : F-Algebra F) {X : Setoid c′ ℓ′} {f g : Func X (F-Algebra.A A)} →
             (∀ x → Setoid._≈_ (F-Algebra.A A) (f ⟨$⟩ x) (g ⟨$⟩ x)) →
             ∀ t → Setoid._≈_ (F-Algebra.A A) (fold A f t) (fold A g t)
  fold-ext A h (pure x)         = h x
  fold-ext A h (impure (_ , k)) =
    Func.cong (F-Algebra.α A) (refl ,ₚ λ q → fold-ext A h (k q))

  -- The fold of a bind is the fold of the head with the folded tails.
  fold-bind-alg : (A : F-Algebra F) {X Y : Setoid c′ ℓ′}
                  (f : Func Y (F-Algebra.A A)) (h : Func X (F-Algebra.A A))
                  (g : Setoid.Carrier X → C ⋆ Setoid.Carrier Y) →
                  (∀ x → Setoid._≈_ (F-Algebra.A A) (fold A f (g x)) (h ⟨$⟩ x)) →
                  ∀ t → Setoid._≈_ (F-Algebra.A A) (fold A f (t >>= g)) (fold A h t)
  fold-bind-alg A f h g hyp (pure x)         = hyp x
  fold-bind-alg A f h g hyp (impure (_ , k)) =
    Func.cong (F-Algebra.α A) (refl ,ₚ λ q → fold-bind-alg A f h g hyp (k q))

module Fusion (C D : Container 0ℓ 0ℓ) (l : Lowering C D) where
  module AC = Alg 0ℓ 0ℓ C
  module AD = Alg 0ℓ 0ℓ D
  open FoldLemmas 0ℓ 0ℓ D using (fold-ext; fold-bind-alg)

  -- A function out of the positions of a command is a map of setoids.
  fromPos : ∀ {a} (B : F-Algebra AD.F) →
            (Position C a → Setoid.Carrier (F-Algebra.A B)) →
            Func (setoid (Position C a)) (F-Algebra.A B)
  fromPos B k = record
    { to   = k
    ; cong = λ { refl → Setoid.refl (F-Algebra.A B) }
    }

  -- The algebra for `C` that interprets each command by interpreting its
  -- lowering.
  pullback : F-Algebra AD.F → F-Algebra AC.F
  pullback B = record
    { A = F-Algebra.A B
    ; α = record
        { to   = λ { (a , k) → AD.fold B (fromPos B k) (l a) }
        ; cong = λ { {a , _} {.a , _} (refl ,ₚ k≈) → fold-ext B k≈ (l a) }
        }
    }

  -- Interpreting the lowered program equals interpreting the original with
  -- the pulled-back algebra.
  lower-fusion : ∀ (B : F-Algebra AD.F) {X : Setoid 0ℓ 0ℓ}
                 (f : Func X (F-Algebra.A B)) (t : C ⋆ Setoid.Carrier X) →
                 Setoid._≈_ (F-Algebra.A B)
                   (AD.fold B f (lower l t)) (AC.fold (pullback B) f t)
  lower-fusion B f (pure _)         = Setoid.refl (F-Algebra.A B)
  lower-fusion B f (impure (a , k)) =
    fold-bind-alg B f (fromPos B (λ q → AC.fold (pullback B) f (k q)))
      (λ q → lower l (k q)) (λ q → lower-fusion B f (k q)) (l a)
