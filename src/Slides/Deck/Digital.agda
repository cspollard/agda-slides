{-# OPTIONS --safe --without-K #-}

-- Steps are the ℕ-tick reading of a deck.
--
-- A deck is authored on the whole-tick clock ℕ (one tick per pause, `Slides.Deck.Syntax`) and
-- presented by reading it at tick `n` (`Slides.Deck.Read.visible`): that is its steps.  Mapped
-- to the ℚ clock along `ι : ℕ → ℚ` (all durations `ι d`, `Slides.Scene.Tick`) it shows the same
-- at the instant `ι n`: `deck-digital`.  Decks have no drivers (`D = ⊥`) and `Flow` leaves
-- overlay by concatenation whatever the clock, so this is `tick-hom` with the identity on leaves;
-- no lowering of scalars is needed (contrast `Slides.Scene.Digital`, with its percentages).
--
-- `deck-digital-duration`: the duration maps by `ι` too.

module Slides.Deck.Digital where

open import Data.Empty using (⊥)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import Data.List.Properties as ListP

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scalar.Model.Rat using (ratMon; ratSub; ι)
open import Slides.Scalar.Hom using (ι-hom)
open import Slides.Scene.Syntax using (Scene)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Read using (ℓ; visible)

import Slides.Scene.Sample {ℕ} {⊥} {Flow} natMon natSub (λ ()) _++_ ListP.++-assoc as SN
import Slides.Scene.Sample {ℚ} {⊥} {Flow} ratMon ratSub (λ ()) _++_ ListP.++-assoc as SQ

open import Slides.Scene.Tick {ℕ} {ℚ} {⊥} {⊥} {Flow} {Flow} natMon natSub ratMon ratSub ι ι-hom
  (λ ()) (λ ()) (λ x → x) (λ ()) _++_ ListP.++-assoc _++_ ListP.++-assoc (λ x → x) (λ _ _ → refl)
  using (mapScene; tick-hom)

-- leaves are read as themselves on the ℚ clock too
ℓQ : Flow → ℚ → Flow
ℓQ a _ = a

-- the ℚ clock: what is visible at the instant `ι n`
visibleQ : Scene ℚ ⊥ Flow → ℕ → Maybe Flow
visibleQ s n = proj₂ (SQ.sample ℓQ s) (ι n) nothing

private
  map-id : ∀ {A : Set} (m : Maybe A) → Maybe.map (λ x → x) m ≡ m
  map-id nothing  = refl
  map-id (just _) = refl

deck-digital : ∀ (s : Scene ℕ ⊥ Flow) n → visibleQ (mapScene s) n ≡ visible s n
deck-digital s n = trans (proj₂ (tick-hom ℓ ℓQ (λ a p → refl) s) n nothing) (map-id _)

deck-digital-duration : ∀ (s : Scene ℕ ⊥ Flow) →
  proj₁ (SQ.sample ℓQ (mapScene s)) ≡ ι (proj₁ (SN.sample ℓ s))
deck-digital-duration s = proj₁ (tick-hom ℓ ℓQ (λ a p → refl) s)
