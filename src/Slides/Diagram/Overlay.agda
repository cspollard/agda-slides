{-# OPTIONS --safe --without-K #-}

-- Overlay: an associative operation on what a frame shows, with absence as unit, stated once.
--
-- `Overlays X` is a semigroup; `Absent` lifts it to `Maybe X`, where `nothing` is the unit, so a
-- reading "time to maybe-value" overlays what is present.  Layouts overlay by `ovl`
-- (`Slides.Diagram.Laws`), event lists by concatenation.  `IsOverlayHom` is a semigroup
-- homomorphism, and it commutes with the lift.  The scene readings and their laws
-- (`Slides.Scene.Sample`, `Laws`, `Tick`) take an `Overlays` and derive everything else.

module Slides.Diagram.Overlay where

open import Data.List using (List; _++_)
import Data.List.Properties as ListP
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

record Overlays (X : Set) : Set where
  infixr 6 _⊙_
  field
    _⊙_    : X → X → X
    ⊙-assoc : ∀ a b c → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)

listOverlay : ∀ {A : Set} → Overlays (List A)
listOverlay = record { _⊙_ = _++_ ; ⊙-assoc = ListP.++-assoc }

module Absent {X} (O : Overlays X) where
  open Overlays O

  merge : Maybe X → Maybe X → Maybe X
  merge nothing  y        = y
  merge (just a) nothing  = just a
  merge (just a) (just b) = just (a ⊙ b)

  merge-nothing : ∀ x → merge x nothing ≡ x
  merge-nothing nothing  = refl
  merge-nothing (just _) = refl

  merge-assoc : ∀ x y z → merge (merge x y) z ≡ merge x (merge y z)
  merge-assoc nothing  y        z        = refl
  merge-assoc (just a) nothing  z        = refl
  merge-assoc (just a) (just b) nothing  = refl
  merge-assoc (just a) (just b) (just c) = cong just (⊙-assoc a b c)

record IsOverlayHom {X Y} (O : Overlays X) (P : Overlays Y) (F : X → Y) : Set where
  field F-⊙ : ∀ x y → F (Overlays._⊙_ O x y) ≡ Overlays._⊙_ P (F x) (F y)

  merge-map : ∀ x y → Maybe.map F (Absent.merge O x y) ≡ Absent.merge P (Maybe.map F x) (Maybe.map F y)
  merge-map nothing  y        = refl
  merge-map (just a) nothing  = refl
  merge-map (just a) (just b) = cong just (F-⊙ a b)
