{-# OPTIONS --safe --without-K #-}

-- Laws of the lowerings.
--
-- Content lowerings: `finalFrame` of a loop, and of an animation with no steps, is the
-- first frame.
--
-- Command lowerings (a body that awaits is a `Slides.Input` program, lowered by
-- `Slides.Input.Supports.lowerDeck`):
--
--   scene-lowered                              a backend that supports `next` gives the lowered body the scene
--                                              of the source (the pull-back `isNextS` of `isNext`)
--   steps-pipeline                             `elab`, `lowerDeck`, `stepsBy` is `steps`

module Slides.Lower.Properties where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Container.Lowering.Properties using (_≈⋆_; lower-bind)
open import Slides.Core
open import Slides.Input.Deck
import Slides.Input.Supports (Shape BlockC) as Sup
open Sup using (Supports)
open Supports

open import Slides.Lower
open import Slides.Steps
open import Slides.Steps.Properties using (scene-elab)
open import Slides.Anim.Syntax using (_∥ᵃ_)

finalFrame-looping : ∀ d ds → finalFrame d ds looping ≡ d
finalFrame-looping d ds = refl

finalFrame-no-steps : ∀ d ds → finalFrame d ds (onSteps []) ≡ d
finalFrame-no-steps d []        = refl
finalFrame-no-steps d (f ∷ fs)  = refl

------------------------------------------------------------------------
-- Command lowerings

module _ {C : Set} (b : Supports C) where

  -- A backend that supports `next` keeps every step: the lowered body is stepped as the source.
  module _ (ns : Σ[ s ∈ S b ] inj b (inj₁ next) ≡ just s) where

    isNextS-supported : ∀ c s → inj b c ≡ just s → isNextS b s ≡ isNext c
    isNextS-supported (inj₁ next) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₁ prev) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₁ first) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₁ last) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₁ (goto _)) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₁ (gotoLabel _)) s e rewrite dec-inj b e = refl
    isNextS-supported (inj₂ _) s e rewrite dec-inj b e = refl

    unsupported-not-next : ∀ c → inj b c ≡ nothing → isNext c ≡ false
    unsupported-not-next (inj₁ next) e with trans (sym e) (proj₂ ns)
    ... | ()
    unsupported-not-next (inj₁ prev) _ = refl
    unsupported-not-next (inj₁ first) _ = refl
    unsupported-not-next (inj₁ last) _ = refl
    unsupported-not-next (inj₁ (goto _)) _ = refl
    unsupported-not-next (inj₁ (gotoLabel _)) _ = refl
    unsupported-not-next (inj₂ _) _ = refl

    -- the pull-back `isNextS` of `isNext` gives the scene of the source
    scene-lowered : ∀ (x : Body⁺ (Nav ⊎ C)) → sceneBy (isNextS b) (Sup.lowerDeck b x) ≡ sceneBy isNext x
    scene-lowered (pure _) = refl
    scene-lowered (impure (inj₁ c , k)) = cong (pure _ ∥ᵃ_) (scene-lowered (k tt))
    scene-lowered (impure (inj₂ (inj₂ _) , k)) = scene-lowered (k tt)
    scene-lowered (impure (inj₂ (inj₁ c) , k)) with inj b c in e
    ... | just s  rewrite e =
      trans (cong (λ t → later t (sceneBy (isNextS b) (Sup.lowerDeck b (k tt)))) (isNextS-supported c s e))
            (cong (later (isNext c)) (scene-lowered (k tt)))
    ... | nothing rewrite e =
      trans (scene-lowered (k tt)) (sym (cong (λ t → later t (sceneBy isNext (k tt))) (unsupported-not-next c e)))

    -- `elab`, the command lowering, then the page: `steps`.
    steps-pipeline : ∀ (body : Body) → stepsBy (isNextS b) (Sup.lowerDeck b (elab body)) ≡ steps body
    steps-pipeline body = cong page (trans (scene-lowered (elab body)) (scene-elab body))
