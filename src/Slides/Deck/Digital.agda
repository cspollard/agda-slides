{-# OPTIONS --safe --without-K #-}

-- A deck's steps are its ℕ-tick reading, and the ℚ clock agrees: this is `tick-hom`
-- (`Slides.Scene.Tick`) at the identity on leaves, since decks have no drivers and `Flow`
-- leaves overlay by `++` on any clock.
--   `deck-digital`           mapped along `ι : ℕ → ℚ`, the scene shows at `ι n` what `visible` shows at `n`
--   `deck-digital-duration`  the duration maps by `ι` too

module Slides.Deck.Digital where

open import Data.Empty using (⊥)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scalar.Model.Rat using (ratMon; ratSub; ι)
open import Slides.Scalar.Hom using (ι-hom)
open import Slides.Scene.Syntax using (Scene; mapScene)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Read using (ℓ; visible)

open import Slides.Diagram.Overlay using (listOverlay)
import Slides.Scene.Sample {ℕ} {⊥} {Flow} natMon natSub (λ ()) listOverlay as SN
import Slides.Scene.Sample {ℚ} {⊥} {Flow} ratMon ratSub (λ ()) listOverlay as SQ

open import Slides.Scene.Tick {ℕ} {ℚ} {⊥} {⊥} {Flow} {Flow} natMon natSub ratMon ratSub ι ι-hom
  (λ ()) (λ ()) (λ x → x) (λ ()) listOverlay listOverlay (λ x → x) (record { F-⊙ = λ _ _ → refl })
  using (tick-hom)

ℓQ : Flow → ℚ → Flow
ℓQ a _ = a

-- the ℚ clock: what is visible at the instant `ι n`
visibleQ : Scene ℚ ⊥ Flow → ℕ → Maybe Flow
visibleQ s n = proj₂ (SQ.sample ℓQ s) (ι n) nothing

private
  map-id : ∀ {A : Set} (m : Maybe A) → Maybe.map (λ x → x) m ≡ m
  map-id nothing  = refl
  map-id (just _) = refl

deck-digital : ∀ (s : Scene ℕ ⊥ Flow) n → visibleQ (mapScene ι (λ ()) s) n ≡ visible s n
deck-digital s n = trans (proj₂ (tick-hom ℓ ℓQ (λ a p → refl) s) n nothing) (map-id _)

deck-digital-duration : ∀ (s : Scene ℕ ⊥ Flow) →
  proj₁ (SQ.sample ℓQ (mapScene ι (λ ()) s)) ≡ ι (proj₁ (SN.sample ℓ s))
deck-digital-duration s = proj₁ (tick-hom ℓ ℓQ (λ a p → refl) s)
