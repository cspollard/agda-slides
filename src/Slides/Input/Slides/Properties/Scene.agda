{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  A deck is a scene (docs/Stage4.md): `Deck A = Scene (Scene A)`.
--
-- The slides of a deck are the leaves of an outer scene, in sequence (`Seq`: a slide hides the
-- earlier ones), and each slide is a scene of its commands whose steps are ticks (`Slides.Steps`).  A
-- slide is shown for its `pauses + 1` positions, so the start of slide `i` is the sum of the lengths
-- before it, which is `startOf` (the table the labels resolve to).  The flat reading is the
-- substitution `join` (`Slides.Anim.Sample.Properties.Nested.nested-flat`):
--
--   startOf-prefix   slide `i` of a deck starts after the total length of the slides before it
--   deck-nested      reading the deck slide by slide is reading the flat deck
--   deck-shown       at the position `startOf + j`, the flat deck shows what slide `i` shows at step `j`
--
-- The position of the deck machine (`Slides.Input.Navigation`) is the tick of the flat scene.

module Slides.Input.Slides.Properties.Scene where

open import Data.List.Base using (List; []; _∷_; _++_; length; foldr)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-monoʳ-<; m≤m+n; <-≤-trans)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; _>>=_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym; subst)

open import Slides.Input.Slides using (Slide)
open import Slides.Input.Slides.Properties using (pauses; startOf)
open import Relation.Binary.Bundles using (Setoid)
open import Slides.Anim.Syntax using (Scene; _⨾_; hold′; foldS)
open import Slides.Anim.Sample.Properties.Nested using (TMS; nested-flat)
open import Slides.Anim.Sample.Properties.Nat using (seq-left; seq-right; hold-in)
open import Slides.Anim.Sample using (timeAlg)
open import Slides.Time.Nat using (natClock)
open import Slides.Steps
open import Slides.Steps.Properties using (tickT; shown)

-- a slide is shown for its `pauses + 1` positions
slideS : Slide → Scene (Maybe Leaf)
slideS (_ , b) = hold′ (suc (pauses b)) (sceneBy (isNext {⊤}) (elab b))

deckS : List Slide → Scene (Scene (Maybe Leaf))
deckS []       = pure (pure nothing)
deckS (s ∷ ss) = pure (slideS s) ⨾ deckS ss

-- the flat reading: substitute each slide for its leaf
flat : List Slide → Scene (Maybe Leaf)
flat ss = deckS ss >>= λ x → x

-- the length of a deck, in positions
total : List Slide → ℕ
total = foldr (λ s n → suc (pauses (proj₂ s)) + n) 0

-- slide `i` of a deck starts after the slides before it
startOf-prefix : ∀ st ss₁ s ss₂ → startOf st (ss₁ ++ s ∷ ss₂) (length ss₁) ≡ st + total ss₁
startOf-prefix st []        s ss₂ = sym (+-identityʳ st)
startOf-prefix st (t ∷ ss₁) s ss₂ =
  trans (startOf-prefix (st + pauses (proj₂ t) + 1) ss₁ s ss₂)
        (solve 3 (λ x p y → (x :+ p :+ con 1) :+ y := x :+ (con 1 :+ p :+ y)) refl st (pauses (proj₂ t)) (total ss₁))

-- the flat deck lasts as long as its slides
dur-flat : ∀ ss → proj₁ (tickT (flat ss)) ≡ total ss
dur-flat []        = refl
dur-flat (s ∷ ss)  = cong (suc (pauses (proj₂ s)) +_) (dur-flat ss)

total-++ : ∀ ss₁ ss₂ → total (ss₁ ++ ss₂) ≡ total ss₁ + total ss₂
total-++ []        ss₂ = refl
total-++ (s ∷ ss₁) ss₂ = trans (cong (suc (pauses (proj₂ s)) +_) (total-++ ss₁ ss₂)) (sym (+-assoc (suc (pauses (proj₂ s))) _ _))

-- reading the deck slide by slide (the leaf of the outer scene is the reading of a slide) is
-- reading the flat deck: `nested-flat`
deck-nested : ∀ ss → Setoid._≈_ (TMS natClock (List Leaf)) (tickT (flat ss))
  (foldS tickT (timeAlg natClock _++_ (λ _ x → x) (λ _ τ → τ)) (deckS ss))
deck-nested ss = nested-flat natClock _++_ (λ _ x → x) (λ _ τ → τ) _ (deckS ss) (λ x → x)

-- at the position `startOf + j` the flat deck shows what the slide shows at step `j`
deck-shown : ∀ ss₁ s ss₂ j → j < suc (pauses (proj₂ s)) →
  shown (total ss₁ + j) (flat (ss₁ ++ s ∷ ss₂)) ≡ shown j (sceneBy (isNext {⊤}) (elab (proj₂ s)))
deck-shown [] s ss₂ j lt =
  cong (maybe′ (λ x → x) [])
       (trans (seq-left (tickT (slideS s)) (tickT (flat ss₂)) j lt)
              (hold-in (suc (pauses (proj₂ s))) (tickT (sceneBy (isNext {⊤}) (elab (proj₂ s)))) j lt))
deck-shown (t ∷ ss₁) s ss₂ j lt =
  trans (cong (maybe′ (λ x → x) []) (trans (cong (proj₂ (tickT (flat (t ∷ ss₁ ++ s ∷ ss₂)))) (+-assoc (suc (pauses (proj₂ t))) (total ss₁) j))
                                           (seq-right (tickT (slideS t)) (tickT (flat (ss₁ ++ s ∷ ss₂))) (total ss₁ + j) bound)))
        (deck-shown ss₁ s ss₂ j lt)
  where
    bound : total ss₁ + j < proj₁ (tickT (flat (ss₁ ++ s ∷ ss₂)))
    bound = subst (total ss₁ + j <_) (sym (trans (dur-flat (ss₁ ++ s ∷ ss₂)) (total-++ ss₁ (s ∷ ss₂))))
                  (+-monoʳ-< (total ss₁) (<-≤-trans lt (m≤m+n (suc (pauses (proj₂ s))) (total ss₂))))
