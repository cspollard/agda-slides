{-# OPTIONS --safe --without-K #-}

-- Lists of frames as partial functions of the tick.
--
-- `nth xs j` is the frame at tick `j`, if there is one.  The operations on animations are read
-- through it: `++` (one segment after another) is "first, then the second with the tick shifted"
-- (`nth-++`), `merge` (`Par`) is the pointwise `mergeM` (`nth-merge`), the same algebra the
-- continuous semantics uses (`Slides.Anim.Continuous.parAt`), and the frames of one segment are
-- its body at the samples of its track (`nth-frames`).  Shared by the assembly proofs of the
-- continuous templates (`Slides.Anim.Param.Properties`) and of the discrete ones
-- (`Slides.Anim.DParam.Properties`).

module Slides.Anim.Nth where

open import Data.Bool using (true; false; if_then_else_; T)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map; applyUpTo)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Slides.Diagram.Scalar using (Ops)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (merge; frames; mergeM)


------------------------------------------------------------------------
-- Lists of frames as partial functions of the tick

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc j) = nth xs j

nth-++ : ∀ {A : Set} (xs ys : List A) j →
         nth (xs ++ ys) j ≡ (if j <ᵇ length xs then nth xs j else nth ys (j ∸ length xs))
nth-++ []       ys j       = refl
nth-++ (x ∷ xs) ys zero    = refl
nth-++ (x ∷ xs) ys (suc j) = nth-++ xs ys j

private
  mergeM-nothingʳ : ∀ {F : Set} (_⊙_ : F → F → F) m → mergeM _⊙_ m nothing ≡ m
  mergeM-nothingʳ _⊙_ nothing  = refl
  mergeM-nothingʳ _⊙_ (just x) = refl

nth-merge : ∀ {F : Set} (_⊙_ : F → F → F) (xs ys : List F) j →
            nth (merge _⊙_ xs ys) j ≡ mergeM _⊙_ (nth xs j) (nth ys j)
nth-merge _⊙_ []       ys       j       = refl
nth-merge _⊙_ (x ∷ xs) []       j       = sym (mergeM-nothingʳ _⊙_ (nth (x ∷ xs) j))
nth-merge _⊙_ (x ∷ xs) (y ∷ ys) zero    = refl
nth-merge _⊙_ (x ∷ xs) (y ∷ ys) (suc j) = nth-merge _⊙_ xs ys j

nth-replicate : ∀ {A : Set} n (y : A) j → nth (replicate n y) j ≡ (if j <ᵇ n then just y else nothing)
nth-replicate zero    y j       = refl
nth-replicate (suc n) y zero    = refl
nth-replicate (suc n) y (suc j) = nth-replicate n y j

nth-applyUpTo : ∀ {A : Set} (f : ℕ → A) n j →
                nth (applyUpTo f n) j ≡ (if j <ᵇ n then just (f j) else nothing)
nth-applyUpTo f zero    j       = refl
nth-applyUpTo f (suc n) zero    = refl
nth-applyUpTo f (suc n) (suc j) = nth-applyUpTo (λ i → f (suc i)) n j

nth-map : ∀ {A B : Set} (g : A → B) xs j → nth (map g xs) j ≡ Maybe.map g (nth xs j)
nth-map g []       j       = refl
nth-map g (x ∷ xs) zero    = refl
nth-map g (x ∷ xs) (suc j) = nth-map g xs j

private
  map-if : ∀ {A B : Set} (g : A → B) b (x : A) →
           Maybe.map g (if b then just x else nothing) ≡ (if b then just (g x) else nothing)
  map-if g true  x = refl
  map-if g false x = refl

-- the frames of a segment, tick by tick
nth-frames : ∀ {S} (O : Ops S) (s : Seg S) j →
             nth (frames O s) j
             ≡ (if j <ᵇ proj₁ (T.sample T.ℚLerp (track s))
                then just (body O s (proj₂ (T.sample T.ℚLerp (track s)) j)) else nothing)
nth-frames O s j =
  trans (nth-map (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t))
                 (applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))) j)
  (trans (cong (Maybe.map (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t)))
               (nth-applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s))) j))
         (map-if (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t)) (j <ᵇ proj₁ (T.sample T.ℚLerp (track s))) j))


-- `++` of lists is `++`, with the tick of the second part shifted by the length of the first
nth-++′ : ∀ {A : Set} (xs ys : List A) j n → length xs ≡ n →
          nth (xs ++ ys) j ≡ (if j <ᵇ n then nth xs j else nth ys (j ∸ n))
nth-++′ xs ys j n refl = nth-++ xs ys j

nth-in : ∀ {A : Set} (xs : List A) j → (j <ᵇ length xs) ≡ true → ∃ λ x → nth xs j ≡ just x
nth-in []       j       ()
nth-in (x ∷ xs) zero    h = x , refl
nth-in (x ∷ xs) (suc j) h = nth-in xs j h

-- the `Maybe` bind that succeeds has a successful first part (inverting `leaves`-like traversals)
bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y} → (m Maybe.>>= f) ≡ just y →
            ∃ λ x → m ≡ just x × f x ≡ just y
bind-just (just x) f eq = x , refl , eq
bind-just nothing  f ()
