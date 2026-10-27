{-# OPTIONS --safe --without-K #-}

-- STAGE 4 SPIKE: how today's decks sit in the scene signature.
--
-- (1) A slide body that awaits, `Prog (Nav ⊎ C) ⊤` over scene vocabulary `V`, is a scene on the
--     step clock: `show v` is `Par` with a leaf, `await next` (= `pause`) is `Delay 1` of the rest,
--     labels and other awaited commands are control, not scene.  The scene's duration is the
--     number of pauses (`dur-toScene`); everything after the j-th pause is present from step j.
-- (2) `Body⁺ X` and `Prog X ⊤` over `Shape BlockC` are the same container up to a definitional
--     isomorphism (`toProgC` is the identity on shapes and positions): `Collapse` shows that the
--     `Steps.Input` pass (`goBy`) typechecks unchanged on `Prog`, so `Body⁺` can be a synonym.

module Slides.Spike.Stage4.Embed where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Slides.Spike.Stage4.Clock
open import Slides.Spike.Stage4.QClock using (QClock)
open Sem QClock

module Prog⇒Scene (V : Set) where
  open import Slides.Input V using (Nav; next; Prog)

  isNext : ∀ {C : Set} → Nav ⊎ C → Bool
  isNext (inj₁ next) = true
  isNext _           = false

  weight : Bool → ℕ
  weight true  = 1
  weight false = 0

  delayB : ∀ {A : Set} → Bool → Scene A → Scene A
  delayB true  s = impure (Delay 1 , λ _ → s)
  delayB false s = s

  toScene : ∀ {C : Set} → Prog (Nav ⊎ C) ⊤ → Scene (Maybe V)
  toScene (pure _)                = pure nothing
  toScene (impure (inj₁ v , k))   = parS (pure (just v)) (toScene (k tt))
  toScene (impure (inj₂ (inj₁ x) , k)) = delayB (isNext x) (toScene (k tt))
  toScene (impure (inj₂ (inj₂ _) , k)) = toScene (k tt)    -- a label shows nothing

  pauses : ∀ {C : Set} → Prog (Nav ⊎ C) ⊤ → ℕ
  pauses (pure _)                = 0
  pauses (impure (inj₁ _ , k))   = pauses (k tt)
  pauses (impure (inj₂ (inj₁ x) , k)) = weight (isNext x) ℕ.+ pauses (k tt)
  pauses (impure (inj₂ (inj₂ _) , k)) = pauses (k tt)

  -- eternal leaves: a shown piece is constant, an empty body is absent
  leaf : Maybe V → TM V
  leaf m = 0 , λ _ → m

  dur-delayB : ∀ b (s : Scene (Maybe V)) → proj₁ (sample leaf (delayB b s)) ≡ weight b ℕ.+ proj₁ (sample leaf s)
  dur-delayB true  s = refl
  dur-delayB false s = refl

  dur-toScene : ∀ {C : Set} (p : Prog (Nav ⊎ C) ⊤) → proj₁ (sample leaf (toScene p)) ≡ pauses p
  dur-toScene (pure _)                = refl
  dur-toScene (impure (inj₁ _ , k))   = dur-toScene (k tt)
  dur-toScene (impure (inj₂ (inj₁ x) , k)) =
    trans (dur-delayB (isNext x) (toScene (k tt))) (cong (weight (isNext x) ℕ.+_) (dur-toScene (k tt)))
  dur-toScene (impure (inj₂ (inj₂ _) , k)) = dur-toScene (k tt)
