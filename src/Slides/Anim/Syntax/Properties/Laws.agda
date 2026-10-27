{-# OPTIONS --safe --without-K #-}

-- Laws of `Par` once frames are laid out (`Slides.Diagram.Place.Properties.Laws`, `Commute`).
--
--   * `Par` is associative: merging laid-out frames is associative up to `≈ᴸ`
--     (`mergeL-assoc`, from `⊙-assoc`; the unit laws of `merge` hold on the nose)
--   * `par`, which pads the shorter side with empty frames, lays out like the
--     unpadded `Par` on frames of non-negative size (`par-layout`): padding by
--     `none` is invisible.  This is the place where the unit laws of `atop` are
--     needed, and with them the `Valid` hypothesis.

module Slides.Anim.Syntax.Properties.Laws where

open import Data.List using (List; []; _∷_; _++_; length; replicate; map; applyUpTo)
import Data.List.Properties as LP
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; _∷_; [])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_; _≤_; suc)
import Data.Nat.Properties as ℕP
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (true; false; T)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Scalar using (Ops; intOps; ratOps)
import Slides.Diagram.Syntax as DS
open import Slides.Diagram.Place.Properties.Laws using (IsLawful; module Proofs; lawfulℤ; lawfulℚ)
import Slides.Diagram.Place.Properties.Commute as Commute
open import Slides.Anim.Syntax
open import Slides.Anim.Syntax.Properties
open import Slides.Anim.Timeline

open import Slides.Anim.Timeline.Properties
module For {S : Set} (O : Ops S) (L : IsLawful O) where
  open Ops O using (0#)
  open Proofs O L
  open Commute.For O L using (mergeL; layout-merge)
  open import Slides.Diagram.Equality R.isEquivalence

  private
    ≈ᴸ-refl : ∀ {l} → l ≈ᴸ l
    ≈ᴸ-refl = IsEquivalence.refl ≈ᴸ-isEquivalence

    reflᴸ : ∀ xs → Pointwise _≈ᴸ_ xs xs
    reflᴸ xs = PW.refl ≈ᴸ-refl

  ----------------------------------------------------------------------
  -- Associativity

  mergeL-assoc : ∀ xs ys zs → Pointwise _≈ᴸ_ (mergeL (mergeL xs ys) zs) (mergeL xs (mergeL ys zs))
  mergeL-assoc []       ys       zs       = reflᴸ _
  mergeL-assoc (x ∷ xs) []       zs       = reflᴸ _
  mergeL-assoc (x ∷ xs) (y ∷ ys) []       = reflᴸ _
  mergeL-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    IsEquivalence.sym ≈ᴸ-isEquivalence (⊙-assoc x y z) ∷ mergeL-assoc xs ys zs

  ----------------------------------------------------------------------
  -- Padding with empty frames is invisible

  -- `k` empty frames after the shorter operand
  padˡ : ∀ xs ys k → length xs + k ≡ length ys → All Valid ys →
         Pointwise _≈ᴸ_ (mergeL (xs ++ replicate k empty) ys) (mergeL xs ys)
  padˡ []       []       ℕ.zero    _  _         = []
  padˡ []       (y ∷ ys) (suc k)   eq (v ∷ vs)  =
    ⊙-unitˡ y v ∷ padˡ [] ys k (ℕP.suc-injective eq) vs
  padˡ (x ∷ xs) (y ∷ ys) k         eq (v ∷ vs)  =
    ≈ᴸ-refl ∷ padˡ xs ys k (ℕP.suc-injective eq) vs
  padˡ (x ∷ xs) []       k         ()  _
  padˡ []       []       (suc k)   ()  _
  padˡ []       (y ∷ ys) ℕ.zero    ()  _

  padʳ₀ : ∀ xs k → k ≡ length xs → All Valid xs → Pointwise _≈ᴸ_ (mergeL xs (replicate k empty)) xs
  padʳ₀ []       ℕ.zero    _  _        = []
  padʳ₀ (x ∷ xs) (suc k)   eq (v ∷ vs) = ⊙-unitʳ x v ∷ padʳ₀ xs k (ℕP.suc-injective eq) vs
  padʳ₀ []       (suc k)   ()  _
  padʳ₀ (x ∷ xs) ℕ.zero    ()  _

  padʳ : ∀ xs ys k → length ys + k ≡ length xs → All Valid xs →
         Pointwise _≈ᴸ_ (mergeL xs (ys ++ replicate k empty)) (mergeL xs ys)
  padʳ []       []       ℕ.zero    _  _         = []
  padʳ (x ∷ xs) []       (suc k)   eq (v ∷ vs)  =
    ⊙-unitʳ x v ∷ padʳ₀ xs k (ℕP.suc-injective eq) vs
  padʳ (x ∷ xs) (y ∷ ys) k         eq (v ∷ vs)  =
    ≈ᴸ-refl ∷ padʳ xs ys k (ℕP.suc-injective eq) vs
  padʳ []       (y ∷ ys) k         ()  _
  padʳ (x ∷ xs) []       ℕ.zero    ()  _
  padʳ []       []       (suc k)   ()  _

  ----------------------------------------------------------------------
  -- The timeline of a padded animation

  ε : DS.Dia S
  ε = DS.spacer 0# 0#

  private
    map-const : ∀ {A B : Set} (c : B) (xs : List A) → map (λ _ → c) xs ≡ replicate (length xs) c
    map-const c []       = refl
    map-const c (x ∷ xs) = cong (c ∷_) (map-const c xs)

  timeline-none : ∀ m → timeline DS.atop (frames O) (none O m) ≡ replicate m ε
  timeline-none m =
    trans (map-const ε (applyUpTo (λ i → i) m)) (cong (λ n → replicate n ε) (LP.length-applyUpTo (λ i → i) m))

  -- pad: the frames of `a`, then empty frames up to `n`
  timeline-pad : ∀ n (a : Anim S (Seg S)) →
                 timeline DS.atop (frames O) (pad O n a) ≡ timeline DS.atop (frames O) a ++ replicate (n ∸ dur a) ε
  timeline-pad n a with dur a <ᵇ n in eq
  ... | true  = cong (timeline DS.atop (frames O) a ++_) (timeline-none (n ∸ dur a))
  ... | false = trans (sym (LP.++-identityʳ _)) (cong (λ k → timeline DS.atop (frames O) a ++ replicate k ε) (sym (le⇒∸0 eq)))
    where
      le⇒∸0 : (dur a <ᵇ n) ≡ false → n ∸ dur a ≡ 0
      le⇒∸0 e = ℕP.m≤n⇒m∸n≡0 (ℕP.≮⇒≥ {dur a} {n} (λ h → subst T e (ℕP.<⇒<ᵇ {dur a} {n} h)))

  ----------------------------------------------------------------------
  -- `par` lays out like the unpadded `Par`

  private
    lay : List (DS.Dia S) → List (Layout S)
    lay = map LW.layout

    lay-pad : ∀ (xs : List (DS.Dia S)) k → lay (xs ++ replicate k ε) ≡ lay xs ++ replicate k empty
    lay-pad xs k = trans (LP.map-++ LW.layout xs (replicate k ε)) (cong (lay xs ++_) (LP.map-replicate LW.layout k ε))

    -- the timeline of `par` and of the unpadded `Par`, laid out
    lay-par : ∀ (a b : Anim S (Seg S)) →
              lay (timeline DS.atop (frames O) (par O a b))
              ≡ mergeL (lay (timeline DS.atop (frames O) a) ++ replicate (dur b ∸ dur a) empty)
                       (lay (timeline DS.atop (frames O) b) ++ replicate (dur a ∸ dur b) empty)
    lay-par a b =
      trans (cong lay (cong₂ (merge DS.atop) (timeline-pad (dur b) a) (timeline-pad (dur a) b)))
      (trans (layout-merge (timeline DS.atop (frames O) a ++ replicate (dur b ∸ dur a) ε) (timeline DS.atop (frames O) b ++ replicate (dur a ∸ dur b) ε))
             (cong₂ mergeL (lay-pad (timeline DS.atop (frames O) a) (dur b ∸ dur a)) (lay-pad (timeline DS.atop (frames O) b) (dur a ∸ dur b))))

    lay-∥ : ∀ (a b : Anim S (Seg S)) →
            lay (timeline DS.atop (frames O) (a ∥ᵃ b)) ≡ mergeL (lay (timeline DS.atop (frames O) a)) (lay (timeline DS.atop (frames O) b))
    lay-∥ a b = layout-merge (timeline DS.atop (frames O) a) (timeline DS.atop (frames O) b)

    len : ∀ (a : Anim S (Seg S)) → length (lay (timeline DS.atop (frames O) a)) ≡ dur a
    len a = trans (LP.length-map LW.layout (timeline DS.atop (frames O) a)) (length-dur O a)

  par-layout : ∀ (a b : Anim S (Seg S)) →
               All Valid (lay (timeline DS.atop (frames O) a)) → All Valid (lay (timeline DS.atop (frames O) b)) →
               Pointwise _≈ᴸ_ (lay (timeline DS.atop (frames O) (par O a b))) (lay (timeline DS.atop (frames O) (a ∥ᵃ b)))
  par-layout a b va vb with ℕP.≤-total (dur a) (dur b)
  ... | inj₁ le rewrite lay-par a b | lay-∥ a b | ℕP.m≤n⇒m∸n≡0 le | LP.++-identityʳ (lay (timeline DS.atop (frames O) b)) =
        padˡ (lay (timeline DS.atop (frames O) a)) (lay (timeline DS.atop (frames O) b)) (dur b ∸ dur a)
             (trans (cong (_+ (dur b ∸ dur a)) (len a)) (trans (ℕP.m+[n∸m]≡n le) (sym (len b)))) vb
  ... | inj₂ ge rewrite lay-par a b | lay-∥ a b | ℕP.m≤n⇒m∸n≡0 ge | LP.++-identityʳ (lay (timeline DS.atop (frames O) a)) =
        padʳ (lay (timeline DS.atop (frames O) a)) (lay (timeline DS.atop (frames O) b)) (dur a ∸ dur b)
             (trans (cong (_+ (dur a ∸ dur b)) (len b)) (trans (ℕP.m+[n∸m]≡n ge) (sym (len a)))) va

module ForInts = For intOps lawfulℤ
module ForRats = For ratOps lawfulℚ
