{-# OPTIONS --safe --without-K #-}

-- The frame-by-frame reading of an animation, and its laws.
--
-- A timeline is a list of frames, one per tick.  Over any frame type `F` with a
-- way `_⊙_` of putting two frames on top of each other:
--
--   * `Seq` is concatenation (`++`);
--   * `Par` is `merge`, which overlays frame by frame and lets the longer side run
--     on alone once the shorter has ended.  Running on alone is padding with a
--     unit, without needing one: `merge [] ys = ys`.
--
-- So `timeline` is `foldA` into `(List F, ++, merge)`.  For the diagram language
-- take `F = Dia S` and `_⊙_ = atop`; the laws of `atop` (`Slides.Diagram.Laws`)
-- then transfer to the laws of `Par` once the frames are laid out.
--
-- Laws, with `_≡_` unless the frame operation is involved:
--   * `++` is associative with unit `[]`; `merge` has unit `[]` on both sides
--   * `merge` is associative when `_⊙_` is, commutative when `_⊙_` is
--   * the swap law: `(a ⨾ b) ∥ (c ⨾ d) = (a ∥ c) ⨾ (b ∥ d)` when `a` and `c` last
--     equally long (needs nothing of `_⊙_`)
--   * `length (merge a b) = max`, so `length ∘ timeline = dur` (`dur` is the
--     timeline's length: both are `foldA`s, and the leaf agrees)

module Slides.Anim.Timeline where

open import Data.List using (List; []; _∷_; _++_; length; map; applyUpTo)
import Slides.Anim.Track as T
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

-- what is shown when at most one of two parts is running, or both: they go over each other
mergeM : ∀ {F : Set} → (F → F → F) → Maybe F → Maybe F → Maybe F
mergeM _⊙_ nothing  y        = y
mergeM _⊙_ x        nothing  = x
mergeM _⊙_ (just x) (just y) = just (x ⊙ y)

module _ {F : Set} (_⊙_ : F → F → F) where

  merge : List F → List F → List F
  merge []       ys       = ys
  merge (x ∷ xs) []       = x ∷ xs
  merge (x ∷ xs) (y ∷ ys) = (x ⊙ y) ∷ merge xs ys

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

  -- the timeline of an animation, from the frames of each leaf
  timeline : ∀ {T} → (T → List F) → AnimC ⋆ T → List F
  timeline leaf = foldA leaf _++_ merge

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

-- the diagram language: a segment shows its body at the parameter's value on each tick, frames overlay by `atop`
frames : ∀ {S} → Ops S → Seg S → List (Dia S)
frames O s = map (λ t → body O s (proj₂ sampled t)) (applyUpTo (λ i → i) (proj₁ sampled))
  where sampled = T.sample T.ℚLerp (track s)

frames-length : ∀ {S} (O : Ops S) (s : Seg S) → length (frames O s) ≡ ticks s
frames-length O s =
  trans (trans (LP.length-map _ (applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))))
               (LP.length-applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))))
        (T.sample-dur T.ℚLerp (track s))

-- the length of the timeline is the duration
length-dur : ∀ {S} (O : Ops S) (m : Anim S (Seg S)) → length (timeline atop (frames O) m) ≡ dur m
length-dur {S} O m = trans (length-timeline atop (frames O) m) (foldA-ext m)
  where
    foldA-ext : (m : Anim S (Seg S)) →
                foldA (λ t → length (frames O t)) _+_ _⊔_ m ≡ dur m
    foldA-ext (pure t)               = frames-length O t
    foldA-ext (impure (Seq , k))     = cong₂ _+_ (foldA-ext (k zero)) (foldA-ext (k (suc zero)))
    foldA-ext (impure (Par , k))     = cong₂ _⊔_ (foldA-ext (k zero)) (foldA-ext (k (suc zero)))
