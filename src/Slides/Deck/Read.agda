{-# OPTIONS --safe --without-K #-}

-- Reading a deck: what the audience sees at each tick.
--
-- The deck is read by `Slides.Scene.Sample` on the tick clock ℕ with `Flow` leaves overlaid by
-- concatenation.  `visible s n` is the slide the audience sees at tick `n` (`nothing` before the
-- start or after the end); the *machine view* of a deck (`Slides.Deck.Machine`) is this.
--
--   chunk-visible    on tick `k < ticks` a slide shows chunks `0..k` (the chunks so far)
--   index            fragment index = start tick: the events of a slide's scene are its chunks,
--                    each at the tick equal to the number of pauses before it
--   deck-visible     at tick `n` a deck shows the slide it is in, at its local tick
--   steps            the slides' ticks add up: the machine has `duration` states
--
-- Everything is proved from the laws of the scene readings (`Slides.Scene.Sample`) at the ℕ
-- clock, whose arithmetic reduces; the model facts used are named lemmas below.

module Slides.Deck.Read where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
import Data.List.NonEmpty as L⁺
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import Data.List.Properties as ListP

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scene.Syntax
open import Slides.Deck.Content
open import Slides.Deck.Syntax

import Slides.Scene.Events {ℕ} {⊥} natMon natSub as E
import Slides.Scene.Sample {ℕ} {⊥} {Flow} natMon natSub (λ ()) _++_ ListP.++-assoc as S

-- leaves are read as themselves, at any local time
ℓ : Flow → ℕ → Flow
ℓ a _ = a

-- what is visible at tick `n`
visible : Scene ℕ ⊥ Flow → ℕ → Maybe Flow
visible s n = proj₂ (S.sample ℓ s) n nothing

-- the chunks so far: 0..k of the chunks `c ∷ cs`
accumL : Flow → List Flow → ℕ → Flow
accumL c []       k       = c
accumL c (d ∷ ds) zero    = c
accumL c (d ∷ ds) (suc k) = c ++ accumL d ds k

accum : List⁺ Flow → ℕ → Flow
accum (c ∷ cs) = accumL c cs

------------------------------------------------------------------------
-- One slide

go-visible : ∀ c cs t → t < suc (length cs) → visible (chunkFrom c cs) t ≡ just (accumL c cs t)
go-visible c []       zero     _ = refl
go-visible c []       (suc t) (s≤s ())
go-visible c (d ∷ ds) zero     _ = refl
go-visible c (d ∷ ds) (suc t)  (s≤s lt) rewrite go-visible d ds t lt = refl

-- a held scene is itself inside its window
hold-visible : ∀ s w t → t < w → visible (hold w s) t ≡ visible s t
hold-visible s w t lt rewrite dec-false (w ℕP.≤? t) (ℕP.<⇒≱ lt) = refl

chunk-inner : ∀ s k → k < ticks s → visible (chunkScene (Slide.chunkL s)) k ≡ just (accum (Slide.chunkL s) k)
chunk-inner (slide l (c ∷ cs)) k lt = go-visible c cs k lt

chunk-visible : ∀ s k → k < ticks s → visible (slideScene s) k ≡ just (accum (Slide.chunkL s) k)
chunk-visible s k lt = trans (hold-visible (chunkScene (Slide.chunkL s)) _ k lt) (chunk-inner s k lt)

------------------------------------------------------------------------
-- Fragment index = start tick

ol : E.Event Flow → ℕ × Flow
ol e = E.onset e , E.leaf e

-- the chunk `i` of a slide starts at tick `i`
index : Flow → List Flow → List (ℕ × Flow)
index c []       = (0 , c) ∷ []
index c (d ∷ ds) = (0 , c) ∷ map (λ x → suc (proj₁ x) , proj₂ x) (index d ds)

fragment-index : ∀ c cs → map ol (E.events (chunkFrom c cs)) ≡ index c cs
fragment-index c []       = refl
fragment-index c (d ∷ ds) =
  cong ((0 , c) ∷_)
    (trans (sym (ListP.map-∘ (E.events (chunkFrom d ds))))
           (trans (ListP.map-cong (λ e → refl) (E.events (chunkFrom d ds)))
                  (trans (ListP.map-∘ (E.events (chunkFrom d ds)))
                         (cong (map (λ x → suc (proj₁ x) , proj₂ x)) (fragment-index d ds)))))

------------------------------------------------------------------------
-- A deck: the slide the audience is in

-- a slide read in its own time
slideT : Slide → S.Timed
slideT s = S.sample ℓ (slideScene s)

-- the deck read as a scene of scenes: each slide leaf is read as its own scene
nested : Deck → ℕ → Maybe Flow
nested d n = proj₂ (S.timed slideT d) n nothing

-- the nested reading is the reading of the flat scene (nesting by substitution)
flat-visible : ∀ d n → visible (flat d) n ≡ nested d n
flat-visible d n = cong (λ x → proj₂ x n nothing) (L.sample-bind (S.leafT ℓ) slideScene d)
  where import Slides.Scene.Laws {ℕ} {⊥} {Flow} natMon natSub (λ ()) _++_ ListP.++-assoc as L

-- the ticks of the slides add up
total : Slide → List Slide → ℕ
total s []       = ticks s
total s (t ∷ ts) = ticks s + total t ts

-- the slide containing the tick, and the tick inside it
locate : Slide → List Slide → ℕ → Maybe (Slide × ℕ)
locate s []       n with n ℕP.<? ticks s
... | yes _ = just (s , n)
... | no _  = nothing
locate s (t ∷ ts) n with n ℕP.<? ticks s
... | yes _ = just (s , n)
... | no _  = locate t ts (n ∸ ticks s)

show : Maybe (Slide × ℕ) → Maybe Flow
show = Maybe.map (λ x → accum (Slide.chunkL (proj₁ x)) (proj₂ x))

steps-deck : ∀ s ss → proj₁ (S.timed slideT (deckFrom s ss)) ≡ total s ss
steps-deck s []       = refl
steps-deck s (t ∷ ts) = cong (ticks s +_) (steps-deck t ts)

locate-out : ∀ s ss n → total s ss ≤ n → locate s ss n ≡ nothing
locate-out s [] n le with n ℕP.<? ticks s
... | yes lt = ⊥-elim (ℕP.<⇒≱ lt le)
... | no _   = refl
locate-out s (t ∷ ts) n le with n ℕP.<? ticks s
... | yes lt = ⊥-elim (ℕP.<⇒≱ lt (ℕP.≤-trans (ℕP.m≤m+n _ _) le))
... | no ¬lt = locate-out t ts (n ∸ ticks s) (ℕP.m+n≤o⇒m≤o∸n (total t ts) (subst (_≤ n) (ℕP.+-comm (ticks s) (total t ts)) le))

hold-out : ∀ s w t → w ≤ t → visible (hold w s) t ≡ nothing
hold-out s w t le rewrite dec-true (w ℕP.≤? t) le = refl

slide-read : ∀ s n → proj₂ (slideT s) n nothing ≡ show (locate s [] n)
slide-read s n with n ℕP.<? ticks s
... | yes lt = chunk-visible s n lt
... | no ¬lt = hold-out (chunkScene (Slide.chunkL s)) (ticks s) n (ℕP.≮⇒≥ ¬lt)

deck-read : ∀ s ss n → nested (deckFrom s ss) n ≡ show (locate s ss n)
deck-read s []       n = slide-read s n
deck-read s (t ∷ ts) n with n ℕP.<? ticks s
... | yes lt rewrite dec-false (ticks s ℕP.≤? n) (ℕP.<⇒≱ lt) = trans (S.merge-nothing _) (chunk-inner s n lt)
... | no ¬lt rewrite dec-true (ticks s ℕP.≤? n) (ℕP.≮⇒≥ ¬lt) | steps-deck t ts
  with (n ∸ ticks s) ℕP.<? total t ts
...   | yes lt′ rewrite dec-false (total t ts ℕP.≤? (n ∸ ticks s)) (ℕP.<⇒≱ lt′) = deck-read t ts (n ∸ ticks s)
...   | no ¬lt′ rewrite dec-true (total t ts ℕP.≤? (n ∸ ticks s)) (ℕP.≮⇒≥ ¬lt′)
                      | locate-out t ts (n ∸ ticks s) (ℕP.≮⇒≥ ¬lt′) = refl

-- At tick `n` a deck shows the slide it is in, at its local tick: the chunks so far.
deck-visible : ∀ s ss n → visible (flat (deckFrom s ss)) n ≡ show (locate s ss n)
deck-visible s ss n = trans (flat-visible (deckFrom s ss) n) (deck-read s ss n)
