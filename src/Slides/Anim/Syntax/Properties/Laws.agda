{-# OPTIONS --safe --without-K #-}

-- Laws of `Par` once frames are laid out (`Slides.Diagram.Place.Properties.Laws`, `Commute`), in any
-- clock `K` whose scalar is lawful.
--
--   * `Par` is associative: at every time, overlaying laid-out frames is associative up to `≈ᴸ`
--     (`par-assoc`, from `⊙-assoc`)
--   * `Par` is commutative up to a permutation of draws and anchors (`par-comm`, `Commute`)
--   * absence is the unit of `Par`, on the nose (`par-gap`): a gap is `Delay k (Hold 0 _)`, which shows
--     nothing at any time, so the old padding with empty frames and its law (`par-layout`: padded
--     `par` lays out like the unpadded `Par` on frames of non-negative size, which needed the unit
--     laws of `atop` and the `Valid` hypothesis) have no analogue: `par` is `∥ᵃ`.

module Slides.Anim.Syntax.Properties.Laws where

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
import Data.Maybe.Relation.Binary.Pointwise as MP
open import Data.Product using (proj₂)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Ordered using (OOps)
import Slides.Diagram.Syntax as DS
open import Slides.Diagram.Place.Properties.Laws using (IsLawful; module Proofs; lawfulℚ)
import Slides.Diagram.Place.Properties.Commute as Commute
open import Slides.Time using (Clock; ClockLaws; mergeM)
open import Slides.Time.Properties using (ratLaws)
open import Slides.Time.Rat using (ratClock)
import Slides.Anim.Track as Tr
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Sample.Properties using (frames-par; gap-absent)

module For (K : Clock) (LK : ClockLaws K) (L : IsLawful (OOps.ops (Clock.O K))) where
  private
    O = OOps.ops (Clock.O K)
    S = Clock.T K
  open Proofs O L
  open Commute.For O L using (mergeM-comm; _≈ᵖ_)
  open import Slides.Diagram.Equality R.isEquivalence

  -- the laid-out frame at a time
  private
    lay : Maybe (DS.Dia S) → Maybe (Layout S)
    lay = Maybe.map LW.layout

    ≈ᴸ-sym : ∀ {a b} → a ≈ᴸ b → b ≈ᴸ a
    ≈ᴸ-sym = IsEquivalence.sym ≈ᴸ-isEquivalence

    ≈ᴸ-refl : ∀ {a} → a ≈ᴸ a
    ≈ᴸ-refl = IsEquivalence.refl ≈ᴸ-isEquivalence

  ----------------------------------------------------------------------
  -- Associativity

  mergeM-assoc : ∀ (x y z : Maybe (DS.Dia S)) →
                 MP.Pointwise _≈ᴸ_ (lay (mergeM DS.atop (mergeM DS.atop x y) z)) (lay (mergeM DS.atop x (mergeM DS.atop y z)))
  mergeM-assoc nothing  nothing  nothing  = MP.nothing
  mergeM-assoc nothing  nothing  (just z) = MP.just ≈ᴸ-refl
  mergeM-assoc nothing  (just y) nothing  = MP.just ≈ᴸ-refl
  mergeM-assoc nothing  (just y) (just z) = MP.just ≈ᴸ-refl
  mergeM-assoc (just x) nothing  nothing  = MP.just ≈ᴸ-refl
  mergeM-assoc (just x) nothing  (just z) = MP.just ≈ᴸ-refl
  mergeM-assoc (just x) (just y) nothing  = MP.just ≈ᴸ-refl
  mergeM-assoc (just x) (just y) (just z) = MP.just (≈ᴸ-sym (⊙-assoc (LW.layout x) (LW.layout y) (LW.layout z)))

  par-assoc : ∀ val (a b c : Anim) τ →
              MP.Pointwise _≈ᴸ_ (lay (proj₂ (frames K val ((a ∥ᵃ b) ∥ᵃ c)) τ)) (lay (proj₂ (frames K val (a ∥ᵃ (b ∥ᵃ c))) τ))
  par-assoc val a b c τ
    rewrite frames-par K val (a ∥ᵃ b) c τ | frames-par K val a b τ
          | frames-par K val a (b ∥ᵃ c) τ | frames-par K val b c τ =
    mergeM-assoc (proj₂ (frames K val a) τ) (proj₂ (frames K val b) τ) (proj₂ (frames K val c) τ)

  ----------------------------------------------------------------------
  -- Commutativity

  par-comm : ∀ val (a b : Anim) τ →
             MP.Pointwise _≈ᵖ_ (lay (proj₂ (frames K val (a ∥ᵃ b)) τ)) (lay (proj₂ (frames K val (b ∥ᵃ a)) τ))
  par-comm val a b τ rewrite frames-par K val a b τ | frames-par K val b a τ =
    mergeM-comm (proj₂ (frames K val a) τ) (proj₂ (frames K val b) τ)

  ----------------------------------------------------------------------
  -- Absence is the unit of `Par`

  par-gap : ∀ val (a : Anim) τ n → proj₂ (frames K val (a ∥ᵃ gap n)) τ ≡ proj₂ (frames K val a) τ
  par-gap val a τ n rewrite frames-par K val a (gap n) τ | gap-absent K LK val n τ = mergeM-nothing (proj₂ (frames K val a) τ)
    where mergeM-nothing : ∀ {A : Set} {f : A → A → A} (m : Maybe A) → mergeM f m nothing ≡ m
          mergeM-nothing nothing  = refl
          mergeM-nothing (just _) = refl

module ForRats = For ratClock ratLaws lawfulℚ
