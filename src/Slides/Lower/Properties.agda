{-# OPTIONS --safe --without-K #-}

-- Laws of the lowerings.
--
-- Content lowerings: `finalFrame` of a loop, and of an animation with no steps, is the
-- first frame.
--
-- Command lowerings (`lowerCmd`, `lowerCmdBody`):
--
--   lowerCmd-supported, lowerCmd-unsupported   a supported command is renamed, an unsupported one skipped
--   lowerCmdBody-bind                          the lowering of a body is a monad morphism (`lower-bind`)
--   lowerCmdBody-lowerDeck                     on a body seen as a `Slides.Input` program it *is*
--                                              `Slides.Input.Supports.lowerDeck`
--   steps-lowered                              a backend that supports `next` steps the lowered body
--                                              exactly as the source (the pull-back `isNextS` of `isNext`)
--   steps-pipeline                             `elab`, `lowerCmdBody`, `stepsBy` is `steps`

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
open import Slides.Steps using (stepL; wrapC; steps)
open import Slides.Steps.Input
open import Slides.Steps.Properties using (stepsBy-elab)

finalFrame-looping : ∀ d ds → finalFrame d ds looping ≡ d
finalFrame-looping d ds = refl

finalFrame-no-steps : ∀ d ds → finalFrame d ds (onSteps []) ≡ d
finalFrame-no-steps d []        = refl
finalFrame-no-steps d (f ∷ fs)  = refl

------------------------------------------------------------------------
-- Command lowerings

module _ {C : Set} (b : Supports C) where

  lowerCmd-supported : ∀ k s → inj b k ≡ just s → lowerCmd b k ≡ impure (s , pure)
  lowerCmd-supported k s e rewrite e = refl

  lowerCmd-unsupported : ∀ k → inj b k ≡ nothing → lowerCmd b k ≡ pure tt
  lowerCmd-unsupported k e rewrite e = refl

  -- The lowering of a sequence is the sequence of the lowerings.
  lowerCmdBody-bind : ∀ (x : Body⁺ (Nav ⊎ C)) (f : ⊤ → Body⁺ (Nav ⊎ C)) →
    lowerCmdBody b (x >>= f) ≈⋆ (lowerCmdBody b x >>= λ q → lowerCmdBody b (f q))
  lowerCmdBody-bind = lower-bind (lowerCmdBlock b)

  -- It is `Slides.Input.Supports.lowerDeck` on the program a body denotes.
  lowerCmdBody-lowerDeck : ∀ (x : Body⁺ (Nav ⊎ C)) →
    toProg (lowerCmdBody b x) ≡ Sup.lowerDeck b (toProg x)
  lowerCmdBody-lowerDeck (pure _) = refl
  lowerCmdBody-lowerDeck (impure (inj₁ (inj₁ c) , k)) =
    cong (λ w → impure (inj₁ (inj₁ c) , λ _ → w)) (lowerCmdBody-lowerDeck (k tt))
  lowerCmdBody-lowerDeck (impure (inj₁ (inj₂ l) , k)) =
    cong (λ w → impure (inj₁ (inj₂ l) , λ _ → w)) (lowerCmdBody-lowerDeck (k tt))
  lowerCmdBody-lowerDeck (impure (inj₂ c , k)) with inj b c in e
  ... | just s  rewrite e =
    cong (λ w → impure (inj₂ (inj₁ s) , λ _ → w)) (lowerCmdBody-lowerDeck (k tt))
  ... | nothing rewrite e = lowerCmdBody-lowerDeck (k tt)

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

    steps-lowered : ∀ m (x : Body⁺ (Nav ⊎ C)) →
      goBy (isNextS b) m (lowerCmdBody b x) ≡ goBy isNext m x
    steps-lowered m (pure _) = refl
    steps-lowered m (impure (inj₁ (inj₁ c) , k)) =
      cong (λ w → wrapC m c >>= λ _ → w) (steps-lowered m (k tt))
    steps-lowered m (impure (inj₁ (inj₂ l) , k)) =
      cong (λ w → proj₂ (stepL m l) >>= λ _ → w) (steps-lowered (proj₁ (stepL m l)) (k tt))
    steps-lowered m (impure (inj₂ c , k)) with inj b c in e
    ... | just s  rewrite e =
      trans (steps-lowered (m ∨ isNextS b s) (k tt))
            (cong (λ n → goBy isNext n (k tt)) (cong (m ∨_) (isNextS-supported c s e)))
    ... | nothing rewrite e =
      trans (steps-lowered m (k tt))
            (cong (λ n → goBy isNext n (k tt)) (trans (sym (∨-identityʳ m)) (cong (m ∨_) (sym (unsupported-not-next c e)))))

    -- `elab`, the command lowering, then the second pass: `steps`.
    steps-pipeline : ∀ (body : Body) → stepsBy (isNextS b) (lowerCmdBody b (elab body)) ≡ steps body
    steps-pipeline body = trans (steps-lowered false (elab body)) (stepsBy-elab body)
