{-# OPTIONS --safe --without-K #-}

-- Programs parametric in the commands they await (docs/Input.md).
--
--   SceneC V  = V ▷ ⊤        show a piece of scene `v`
--   AwaitC C  = C ▷ ⊤        `await c`: one continuation, taken when `c` arrives
--   LabelC    = String ▷ ⊤   name this position (target of `gotoLabel`); no effect on the view
--   Prog C A  = (SceneC ⊎ AwaitC C ⊎ LabelC) ⋆ A
--
-- One sequential control program: no parallel node (deferred, plan/Unify.md section 3).
-- `V` is the scene vocabulary with a single continuation; for `Slides.Core` take
-- `V = Shape BlockC` (every position of `BlockC` is `⊤`).  A deck is a
-- `Prog (Nav ⊎ C)`: it requires the navigation vocabulary, and may await extras `C`.
-- A map of commands `C → D` is a container morphism (`mapC`), so programs are lifted
-- into a larger vocabulary by `Container.Lowering.translate` (`mapP`).

module Slides.Input (V : Set) where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Container; _▷_; _⇒_)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎C_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
import Data.Container.Core as CC

open import Container.Lowering using (translate)
open import Slides.Input.Nav public

SceneC : Container _ _
SceneC = V ▷ λ _ → ⊤

AwaitC : Set → Container _ _
AwaitC C = C ▷ λ _ → ⊤

LabelC : Container _ _
LabelC = String ▷ λ _ → ⊤

ProgC : Set → Container _ _
ProgC C = SceneC ⊎C (AwaitC C ⊎C LabelC)

Prog : Set → Set → Set
Prog C A = ProgC C ⋆ A

Deck : Set → Set → Set
Deck C A = Prog (Nav ⊎ C) A

------------------------------------------------------------------------
-- Smart constructors

show : ∀ {C} → V → Prog C ⊤
show v = impure (inj₁ v , λ _ → pure tt)

await : ∀ {C} → C → Prog C ⊤
await c = impure (inj₂ (inj₁ c) , λ _ → pure tt)

label : ∀ {C} → String → Prog C ⊤
label l = impure (inj₂ (inj₂ l) , λ _ → pure tt)

-- `pause` is `await next`.
pause : ∀ {C} → Deck C ⊤
pause = await (inj₁ next)

infixr 5 _⨾_
_⨾_ : ∀ {C A B} → Prog C A → Prog C B → Prog C B
p ⨾ q = p >>= λ _ → q

------------------------------------------------------------------------
-- Changing the command vocabulary is a container morphism

mapC : ∀ {C D} → (C → D) → ProgC C ⇒ ProgC D
CC._⇒_.shape (mapC f) (inj₁ v)         = inj₁ v
CC._⇒_.shape (mapC f) (inj₂ (inj₁ c))  = inj₂ (inj₁ (f c))
CC._⇒_.shape (mapC f) (inj₂ (inj₂ l))  = inj₂ (inj₂ l)
CC._⇒_.position (mapC f) {inj₁ _}         p = p
CC._⇒_.position (mapC f) {inj₂ (inj₁ _)}  p = p
CC._⇒_.position (mapC f) {inj₂ (inj₂ _)}  p = p

mapP : ∀ {C D A} → (C → D) → Prog C A → Prog D A
mapP f = translate (mapC f)
