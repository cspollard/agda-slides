{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- Lists of frames as partial functions of the tick: `nth xs j` is the frame at tick `j`, if there is
-- one.  The timeline is the tabulation of a timed function (`nth-applyUpTo`), `++` is "first, then
-- the second with the tick shifted" (`nth-++`).  Used where a statement is about shipped lists
-- (`Slides.Anim.Param.Properties`).

module Slides.Anim.Nth where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; map; applyUpTo)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc j) = nth xs j

nth-++ : ∀ {A : Set} (xs ys : List A) j →
         nth (xs ++ ys) j ≡ (if j <ᵇ length xs then nth xs j else nth ys (j ∸ length xs))
nth-++ []       ys j       = refl
nth-++ (x ∷ xs) ys zero    = refl
nth-++ (x ∷ xs) ys (suc j) = nth-++ xs ys j

nth-applyUpTo : ∀ {A : Set} (f : ℕ → A) n j →
                nth (applyUpTo f n) j ≡ (if j <ᵇ n then just (f j) else nothing)
nth-applyUpTo f zero    j       = refl
nth-applyUpTo f (suc n) zero    = refl
nth-applyUpTo f (suc n) (suc j) = nth-applyUpTo (λ i → f (suc i)) n j

nth-map : ∀ {A B : Set} (g : A → B) xs j → nth (map g xs) j ≡ Maybe.map g (nth xs j)
nth-map g []       j       = refl
nth-map g (x ∷ xs) zero    = refl
nth-map g (x ∷ xs) (suc j) = nth-map g xs j

-- `++` of lists is `++`, with the tick of the second part shifted by the length of the first
nth-++′ : ∀ {A : Set} (xs ys : List A) j n → length xs ≡ n →
          nth (xs ++ ys) j ≡ (if j <ᵇ n then nth xs j else nth ys (j ∸ n))
nth-++′ xs ys j n refl = nth-++ xs ys j

nth-in : ∀ {A : Set} (xs : List A) j → (j <ᵇ length xs) ≡ true → ∃ λ x → nth xs j ≡ just x
nth-in []       j       ()
nth-in (x ∷ xs) zero    h = x , refl
nth-in (x ∷ xs) (suc j) h = nth-in xs j h

-- the `Maybe` bind that succeeds has a successful first part (inverting `place`-like traversals)
bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y} → (m Maybe.>>= f) ≡ just y →
            ∃ λ x → m ≡ just x × f x ≡ just y
bind-just (just x) f eq = x , refl , eq
bind-just nothing  f ()
