{-# OPTIONS --safe --without-K #-}

-- `atop` is commutative up to a permutation of its drawing commands and anchors.
--
-- Centring is symmetric (the offsets are `W - wa` and `W - wb`, and `⊔` is
-- commutative), so `atop a b` and `atop b a` have equal size and contain the
-- same drawing commands and anchors; only the order of the lists, which decides
-- what is painted on top, differs.  `_≈ᵖ_` is layout equality with lists compared
-- up to permutation (stdlib's setoid permutation, so entries may also differ by
-- the scalar's equality).
--
-- This is what makes `Par` of independent animations commutative
-- (`Slides.Anim.Footprint`): independent parts share no name, so the order of
-- anchors does not change which box a `connect` finds, and parts that do not
-- overlap paint the same pixels in either order.  `≈ᵖ` is strictly coarser than
-- `≈ᴸ` when parts overlap, which is why `Par` asks for independence.

module Slides.Diagram.Commute where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; _∷_; [])
import Data.List.Relation.Binary.Permutation.Setoid as Perm
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Slides.Diagram.Draw
open import Slides.Diagram.Scalar
open import Slides.Diagram.Laws using (IsLawful; module Proofs; lawfulℤ; lawfulℚ)

module For {S : Set} (O : Ops S) (L : IsLawful O) where
  open Ops O
  open IsLawful L
  open Proofs O L
  open import Slides.Diagram.Place O

  open import Slides.Diagram.Equality R.isEquivalence

  drawSetoid : Setoid 0ℓ 0ℓ
  drawSetoid = record { Carrier = Draw S ; _≈_ = _≈ᵈ_ ; isEquivalence = ≈ᵈ-isEquivalence }

  anchorSetoid : Setoid 0ℓ 0ℓ
  anchorSetoid = record { Carrier = String × Box S ; _≈_ = _≈ᵃ_ ; isEquivalence = ≈ᵃ-isEquivalence }

  private
    module PD = Perm drawSetoid
    module PA = Perm anchorSetoid

  -- layouts, with draws and anchors up to permutation
  record _≈ᵖ_ (l l′ : Layout S) : Set where
    constructor layout≈ᵖ
    field
      width≈   : Layout.width l ≈ Layout.width l′
      height≈  : Layout.height l ≈ Layout.height l′
      draws↭   : Layout.draws l PD.↭ Layout.draws l′
      anchors↭ : Layout.anchors l PA.↭ Layout.anchors l′

  -- equal offsets move a list the same way
  map-cong : ∀ {X : Set} {_≈ₓ_ : Rel X 0ℓ} (act : S × S → X → X) →
             (∀ {p p′} → p ≈ₚ p′ → ∀ x → _≈ₓ_ (act p x) (act p′ x)) →
             ∀ {p p′} → p ≈ₚ p′ → ∀ xs → Pointwise _≈ₓ_ (map (act p) xs) (map (act p′) xs)
  map-cong act cong e []       = []
  map-cong act cong e (x ∷ xs) = cong e x ∷ map-cong act cong e xs

  atop-comm : ∀ a b → atop a b ≈ᵖ atop b a
  atop-comm a b = record
    { width≈   = ⊔-comm (width a) (width b)
    ; height≈  = ⊔-comm (height a) (height b)
    ; draws↭   = PD.↭-trans (PermP.++-comm drawSetoid (map (shiftDraw′ qa) (Layout.draws a)) (map (shiftDraw′ qb) (Layout.draws b)))
                   (PD.↭-reflexive-≋ (PW.++⁺ (map-cong shiftDraw′ shiftDraw-cong pb (Layout.draws b))
                                              (map-cong shiftDraw′ shiftDraw-cong pa (Layout.draws a))))
    ; anchors↭ = PA.↭-trans (PermP.++-comm anchorSetoid (map (shiftAnchor′ qa) (Layout.anchors a)) (map (shiftAnchor′ qb) (Layout.anchors b)))
                   (PA.↭-reflexive-≋ (PW.++⁺ (map-cong shiftAnchor′ shiftAnchor-cong pb (Layout.anchors b))
                                              (map-cong shiftAnchor′ shiftAnchor-cong pa (Layout.anchors a))))
    }
    where
      ew = ⊔-comm (width a) (width b)
      eh = ⊔-comm (height a) (height b)
      qa = width a ⊔ width b - width a , height a ⊔ height b - height a
      qb = width a ⊔ width b - width b , height a ⊔ height b - height b
      pa = sub-congˡ (width a) ew , sub-congˡ (height a) eh
      pb = sub-congˡ (width b) ew , sub-congˡ (height b) eh

module ForInts = For intOps lawfulℤ
module ForRats = For ratOps lawfulℚ
