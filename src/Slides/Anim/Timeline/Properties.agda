{-# OPTIONS --safe --without-K #-}

-- Laws of the timeline: `merge` is associative and commutative when the overlay is, the swap law of
-- `Seq` and `Par`, and the length of a timeline is the duration of the animation.
module Slides.Anim.Timeline.Properties where

open import Data.List using (List; []; _∷_; _++_; length; map; applyUpTo)
import Slides.Anim.Track as T
import Slides.Anim.Track.Properties as TP
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_; _⊔_; suc)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Slides.Diagram.Syntax using (Dia; atop)
open import Slides.Diagram.Scalar using (Ops)
open import Slides.Anim.Syntax

open import Slides.Anim.Timeline hiding (merge; timeline)
import Slides.Anim.Timeline as TL

module _ {F : Set} (_⊙_ : F → F → F) where

  private
    merge : List F → List F → List F
    merge = TL.merge _⊙_

    timeline : ∀ {T} → (T → List F) → AnimC ⋆ T → List F
    timeline = TL.timeline _⊙_

  merge-unitʳ : ∀ xs → merge xs [] ≡ xs
  merge-unitʳ []       = refl
  merge-unitʳ (x ∷ xs) = refl

  merge-assoc : (∀ x y z → (x ⊙ y) ⊙ z ≡ x ⊙ (y ⊙ z)) →
                ∀ xs ys zs → merge (merge xs ys) zs ≡ merge xs (merge ys zs)
  merge-assoc assoc []       ys       zs       = refl
  merge-assoc assoc (x ∷ xs) []       zs       = refl
  merge-assoc assoc (x ∷ xs) (y ∷ ys) []       =
    trans (merge-unitʳ (merge (x ∷ xs) (y ∷ ys))) (sym (cong (merge (x ∷ xs)) (merge-unitʳ (y ∷ ys))))
  merge-assoc assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (assoc x y z) (merge-assoc assoc xs ys zs)

  merge-comm : (∀ x y → x ⊙ y ≡ y ⊙ x) → ∀ xs ys → merge xs ys ≡ merge ys xs
  merge-comm comm []       []       = refl
  merge-comm comm []       (y ∷ ys) = refl
  merge-comm comm (x ∷ xs) []       = refl
  merge-comm comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (comm x y) (merge-comm comm xs ys)

  -- the swap law, at the level of lists
  merge-swap : ∀ as bs cs ds → length as ≡ length cs →
               merge (as ++ bs) (cs ++ ds) ≡ merge as cs ++ merge bs ds
  merge-swap []       bs []       ds _ = refl
  merge-swap []       bs (c ∷ cs) ds ()
  merge-swap (a ∷ as) bs []       ds ()
  merge-swap (a ∷ as) bs (c ∷ cs) ds h =
    cong ((a ⊙ c) ∷_) (merge-swap as bs cs ds (ℕP.suc-injective h))

  length-merge : ∀ xs ys → length (merge xs ys) ≡ length xs ⊔ length ys
  length-merge []       ys       = refl
  length-merge (x ∷ xs) []       = refl
  length-merge (x ∷ xs) (y ∷ ys) = cong suc (length-merge xs ys)

  timeline-⨾ : ∀ {T} (leaf : T → List F) a b →
               timeline leaf (a ⨾ b) ≡ timeline leaf a ++ timeline leaf b
  timeline-⨾ leaf a b = refl

  timeline-∥ : ∀ {T} (leaf : T → List F) a b →
               timeline leaf (a ∥ᵃ b) ≡ merge (timeline leaf a) (timeline leaf b)
  timeline-∥ leaf a b = refl

  -- the serial/parallel swap, for animations
  timeline-swap : ∀ {T} (leaf : T → List F) a b c d →
                  length (timeline leaf a) ≡ length (timeline leaf c) →
                  timeline leaf ((a ⨾ b) ∥ᵃ (c ⨾ d)) ≡ timeline leaf ((a ∥ᵃ c) ⨾ (b ∥ᵃ d))
  timeline-swap leaf a b c d h = merge-swap (timeline leaf a) (timeline leaf b) (timeline leaf c) (timeline leaf d) h

  -- the length of a timeline is the fold of the leaves' lengths
  length-timeline : ∀ {T} (leaf : T → List F) (m : AnimC ⋆ T) →
                    length (timeline leaf m) ≡ foldA (λ t → length (leaf t)) _+_ _⊔_ m
  length-timeline leaf (pure t) = refl
  length-timeline leaf (impure (Seq , k)) =
    trans (LP.length-++ (timeline leaf (k zero)))
          (cong₂ _+_ (length-timeline leaf (k zero)) (length-timeline leaf (k (suc zero))))
  length-timeline leaf (impure (Par , k)) =
    trans (length-merge (timeline leaf (k zero)) (timeline leaf (k (suc zero))))
          (cong₂ _⊔_ (length-timeline leaf (k zero)) (length-timeline leaf (k (suc zero))))


frames-length : ∀ {S} (O : Ops S) (s : Seg S) → length (frames O s) ≡ ticks s
frames-length O s =
  trans (trans (LP.length-map _ (applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))))
               (LP.length-applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))))
        (TP.sample-dur T.ℚLerp (track s))

-- the length of the timeline is the duration
length-dur : ∀ {S} (O : Ops S) (m : Anim S (Seg S)) → length (TL.timeline atop (frames O) m) ≡ dur m
length-dur {S} O m = trans (length-timeline atop (frames O) m) (foldA-ext m)
  where
    foldA-ext : (m : Anim S (Seg S)) →
                foldA (λ t → length (frames O t)) _+_ _⊔_ m ≡ dur m
    foldA-ext (pure t)               = frames-length O t
    foldA-ext (impure (Seq , k))     = cong₂ _+_ (foldA-ext (k zero)) (foldA-ext (k (suc zero)))
    foldA-ext (impure (Par , k))     = cong₂ _⊔_ (foldA-ext (k zero)) (foldA-ext (k (suc zero)))
