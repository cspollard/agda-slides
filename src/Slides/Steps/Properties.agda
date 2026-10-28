{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  Laws of the scene of a body (`Slides.Steps`).
--
--   scene-elab   the scene of an elaborated body does not depend on the extra commands `C`
--   dur-sceneBy  the duration of the scene of a program is its number of steps
--   chunks       a body cut at its pauses: the commands shown from the start, then one chunk per pause
--   shown-chunks step `j` shows the first `j + 1` chunks: the scene sampled at tick `j` of the ℕ clock
--   events-bound the fragment indices of a page are ticks, between 1 and the number of steps
--   machine-shown  the state of the deck machine after `j` `next`s views exactly that
--
-- The page gives a command that starts at tick `k > 0` the fragment index `k` (`Slides.Steps.emit`), so a
-- chunk is one reveal.js click.

module Slides.Steps.Properties where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; concat; take)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary.Decidable using (⌊_⌋; dec-true; isYes≗does)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Core
open import Slides.Input.Deck
open import Slides.Input.Machine (Shape BlockC)
open import Slides.Time.Nat using (natClock)
open import Slides.Input.Navigation (Shape BlockC) using (replay)
open import Slides.Anim.Syntax using (Scene; dur; _∥ᵃ_; delay)
open import Slides.Anim.Sample using (sample; TM)
open import Slides.Anim.Perform using (perform)
open import Slides.Steps

------------------------------------------------------------------------
-- The bridge: `pause` is `await next`

module _ {C C′ : Set} where

  -- the scene of the elaborated body does not depend on the extra commands `C`
  scene-elab : ∀ (b : Body) → sceneBy (isNext {C}) (elab b) ≡ sceneBy (isNext {C′}) (elab b)
  scene-elab (pure _)                          = refl
  scene-elab (impure (inj₁ c , k))             = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ pause , k))         = cong (delay 1) (scene-elab (k tt))
  scene-elab (impure (inj₂ (columns _) , k))   = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (box _ _) , k))     = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (fragment _ _) , k)) = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (classed _ _) , k)) = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (placed _ _ _ _ _) , k)) = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (stepped _ _) , k)) = cong (pure _ ∥ᵃ_) (scene-elab (k tt))
  scene-elab (impure (inj₂ (late _ _) , k)) = cong (pure _ ∥ᵃ_) (scene-elab (k tt))

------------------------------------------------------------------------
-- Ticks

module _ {X : Set} (step? : X → Bool) where

  -- the number of steps
  ticks : Body⁺ X → ℕ
  ticks (pure _)                      = 0
  ticks (impure (inj₁ _ , k))         = ticks (k tt)
  ticks (impure (inj₂ (inj₁ x) , k))  = (if step? x then 1 else 0) + ticks (k tt)
  ticks (impure (inj₂ (inj₂ _) , k))  = ticks (k tt)

  dur-sceneBy : ∀ p → dur (sceneBy step? p) ≡ ticks p
  dur-sceneBy (pure _)                     = refl
  dur-sceneBy (impure (inj₁ _ , k))        = dur-sceneBy (k tt)
  dur-sceneBy (impure (inj₂ (inj₁ x) , k)) with step? x
  ... | true  = cong suc (dur-sceneBy (k tt))
  ... | false = dur-sceneBy (k tt)
  dur-sceneBy (impure (inj₂ (inj₂ _) , k)) = dur-sceneBy (k tt)

  -- a program cut at its steps: what is shown from the start, and one chunk per step
  chunks : Body⁺ X → List Leaf × List (List Leaf)
  chunks (pure _)                      = [] , []
  chunks (impure (inj₁ c , k))         = let (h , t) = chunks (k tt) in (c ∷ h) , t
  chunks (impure (inj₂ (inj₁ x) , k))  = let (h , t) = chunks (k tt) in
                                         if step? x then [] , h ∷ t else h , t
  chunks (impure (inj₂ (inj₂ _) , k))  = chunks (k tt)

-- what the scene shows at tick `j`: its leaves under the ℕ clock (`Slides.Time.Nat`)
tickT : Scene (Maybe Leaf) → TM natClock (List Leaf)
tickT = sample natClock _++_ (λ _ x → x) (λ _ τ → τ) (maybe′ (λ l → l ∷ []) [])

shown : ℕ → Scene (Maybe Leaf) → List Leaf
shown j a = maybe′ (λ x → x) [] (proj₂ (tickT a) j)

-- a command shown from the start is shown at every tick
shown-leaf : ∀ c a j → shown j (pure (just c) ∥ᵃ a) ≡ c ∷ shown j a
shown-leaf c a j with proj₂ (tickT a) j
... | nothing = refl
... | just _  = refl

module _ {X : Set} (step? : X → Bool) where

  -- step `j` shows the first `j + 1` chunks
  shown-chunks : ∀ p j → shown j (sceneBy step? p) ≡ proj₁ (chunks step? p) ++ concat (take j (proj₂ (chunks step? p)))
  shown-chunks (pure _)                     zero    = refl
  shown-chunks (pure _)                     (suc j) = refl
  shown-chunks (impure (inj₁ c , k))        j       = trans (shown-leaf c (sceneBy step? (k tt)) j) (cong (c ∷_) (shown-chunks (k tt) j))
  shown-chunks (impure (inj₂ (inj₁ x) , k)) j with step? x
  shown-chunks (impure (inj₂ (inj₁ x) , k)) zero    | true  = refl
  shown-chunks (impure (inj₂ (inj₁ x) , k)) (suc j) | true  = shown-chunks (k tt) j
  ... | false = shown-chunks (k tt) j
  shown-chunks (impure (inj₂ (inj₂ _) , k)) j       = shown-chunks (k tt) j

------------------------------------------------------------------------
-- The deck machine: its states are ticks

open Machine

module _ {C : Set} (_≟_ : DecidableEquality (Nav ⊎ C)) where

  private
    M₀ : Body → Machine (Nav ⊎ C)
    M₀ b = machine _≟_ (elab b)

    replay-show : ∀ v (M : Machine (Nav ⊎ C)) j → replay (showM v M) j ≡ replay M j
    replay-show v M zero    = refl
    replay-show v M (suc j) = cong (λ q → step M q (inj₁ next)) (replay-show v M j)

    -- after one `next`, the machine that waits for it is the rest, replayed
    replay-await : ∀ (M : Machine (Nav ⊎ C)) j → replay (awaitM _≟_ (inj₁ next) M) (suc j) ≡ inj₂ (replay M j)
    replay-await M zero    = cong (λ t → if t then inj₂ (init M) else inj₁ tt) (trans (isYes≗does (inj₁ next ≟ inj₁ next)) (dec-true (inj₁ next ≟ inj₁ next) refl))
    replay-await M (suc j) = trans (cong (λ q → step (awaitM _≟_ (inj₁ next) M) q (inj₁ next)) (replay-await M j))
                                   (cong inj₂ refl)

    -- a shown command is shown at every tick
    show-case : ∀ v b j → view (M₀ b) (replay (M₀ b) j) ≡ shown j (sceneBy (isNext {C}) (elab {C} b)) →
      view (showM v (M₀ b)) (replay (showM v (M₀ b)) j) ≡ shown j (pure (just v) ∥ᵃ sceneBy (isNext {C}) (elab {C} b))
    show-case v b j ih = trans (cong (v ∷_) (trans (cong (view (M₀ b)) (replay-show v (M₀ b) j)) ih)) (sym (shown-leaf v (sceneBy (isNext {C}) (elab {C} b)) j))

  -- the state after `j` `next`s views what the scene shows at tick `j`
  machine-shown : ∀ b j → view (M₀ b) (replay (M₀ b) j) ≡ shown j (sceneBy (isNext {C}) (elab {C} b))
  machine-shown (pure _)                         j = refl
  machine-shown (impure (inj₁ c , k))            j = show-case (inj₁ c) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ pause , k))        zero    = refl
  machine-shown (impure (inj₂ pause , k))        (suc j) =
    trans (cong (view (awaitM _≟_ (inj₁ next) (M₀ (k tt)))) (replay-await (M₀ (k tt)) j)) (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (columns cs) , k))  j = show-case (inj₂ (columns cs)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (box t c) , k))   j = show-case (inj₂ (box t c)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (fragment st c) , k)) j = show-case (inj₂ (fragment st c)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (classed cl c) , k)) j = show-case (inj₂ (classed cl c)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (placed x y w h c) , k)) j = show-case (inj₂ (placed x y w h c)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (stepped st l) , k)) j = show-case (inj₂ (stepped st l)) (k tt) j (machine-shown (k tt) j)
  machine-shown (impure (inj₂ (late st c) , k)) j = show-case (inj₂ (late st c)) (k tt) j (machine-shown (k tt) j)

------------------------------------------------------------------------
-- The page: fragment indices are ticks

-- Every command starts at a tick of the scene, between 0 and the number of steps.  The page gives a
-- command that starts at tick `k > 0` the fragment index `k` (`Slides.Steps.emit`), so the indices of
-- a slide's fragments are among `1 … ticks`: at most one per pause, the commands of a chunk sharing
-- theirs.  (Every index is used when every chunk has a command that is shown; an empty chunk, or one
-- of only notes, leaves its index out, and reveal.js shows the others in order.)
module _ {X : Set} (step? : X → Bool) where

  events-bound : ∀ p → All (λ e → proj₁ e ≤ ticks step? p) (proj₂ (perform (sceneBy step? p)))
  events-bound (pure _)                     = z≤n ∷ []
  events-bound (impure (inj₁ c , k))        = z≤n ∷ events-bound (k tt)
  events-bound (impure (inj₂ (inj₁ x) , k)) with step? x
  ... | true  = map⁺ (All.map s≤s (events-bound (k tt)))
  ... | false = events-bound (k tt)
  events-bound (impure (inj₂ (inj₂ _) , k)) = events-bound (k tt)
