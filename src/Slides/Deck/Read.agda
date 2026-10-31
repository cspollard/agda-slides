{-# OPTIONS --safe --without-K #-}

-- Reading a deck: `visible s n`, the `Flow` the audience sees at tick `n` (`nothing` outside
-- the deck), by `Slides.Scene.Sample` on the ℕ clock with leaves overlaid by `++`.
-- `Slides.Deck.Machine` runs on this reading.
-- A tick is a page step, a fragment (`Slides.Deck.Steps`).  `visible` is at chunk granularity:
-- at tick t a slide shows the chunks whose own fragment has appeared (`accumL`), whole; the
-- fragments inside a chunk (bullets, `fragment` blocks, animation acts) are not modelled, so
-- those blocks are present from the tick their chunk is.
--   `chunk-visible`   at tick t < ticks a slide shows the chunks revealed by t
--   `fragment-index`  the events of a slide's scene are its chunks, each at its step (`gap`)
--   `steps-deck`      the slides' ticks add up
--   `deck-visible`    at tick n a deck shows the slide it is in, at its local tick

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
open import Relation.Nullary using (yes; no; Dec; does; ¬_)
open import Data.Bool.Base using (if_then_else_)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import Data.List.Properties as ListP

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scene.Syntax
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Steps using (gap)

open import Slides.Deck.Clock using (module E; module S)
open import Slides.Diagram.Overlay using (listOverlay)

ℓ : Flow → ℕ → Flow
ℓ a _ = a

-- what is visible at tick `n`
visible : Scene ℕ ⊥ Flow → ℕ → Maybe Flow
visible s n = proj₂ (S.sample ℓ s) n nothing

-- a comparison that is decided
sel-yes : ∀ {A : Set} {P : Set} (d : Dec P) → P → (x y : A) → (if does d then x else y) ≡ x
sel-yes d p x y = cong (λ b → if b then x else y) (dec-true d p)

sel-no : ∀ {A : Set} {P : Set} (d : Dec P) → ¬ P → (x y : A) → (if does d then x else y) ≡ y
sel-no d p x y = cong (λ b → if b then x else y) (dec-false d p)

-- The chunks revealed by tick `t`: chunk `d` after chunk `c` appears at `gap c d` ticks after `c`
-- (`Slides.Deck.Steps`).  Inner fragments (bullets, `fragment` blocks, animation acts) are
-- not modelled: a chunk is shown whole once its own fragment is.
accumL : Flow → List Flow → ℕ → Flow
accumL c []       t = c
accumL c (d ∷ ds) t = if does (gap c d ℕP.≤? t) then c ++ accumL d ds (t ∸ gap c d) else c

accum : List⁺ Flow → ℕ → Flow
accum (c ∷ cs) = accumL c cs

-- One slide

-- overlaying a leaf with what a window shows
merge-if : ∀ {P : Set} (d : Dec P) c (y : Maybe Flow) z → y ≡ just z →
           S.merge (just c) (if does d then y else nothing) ≡ just (if does d then c ++ z else c)
merge-if (yes _) c y z e = cong (S.merge (just c)) e
merge-if (no _)  c y z e = refl

go-visible : ∀ c cs t → visible (chunkFrom c cs) t ≡ just (accumL c cs t)
go-visible c []       t = refl
go-visible c (d ∷ ds) t = merge-if (gap c d ℕP.≤? t) c _ _ (go-visible d ds (t ∸ gap c d))

-- a held scene is itself inside its window
hold-visible : ∀ s w t → t < w → visible (hold w s) t ≡ visible s t
hold-visible s w t lt = sel-no (w ℕP.≤? t) (ℕP.<⇒≱ lt) nothing _

chunk-inner : ∀ s k → visible (chunkScene (Slide.chunkL s)) k ≡ just (accum (Slide.chunkL s) k)
chunk-inner (slide l (c ∷ cs)) k = go-visible c cs k

chunk-visible : ∀ s k → k < ticks s → visible (slideScene s) k ≡ just (accum (Slide.chunkL s) k)
chunk-visible s k lt = trans (hold-visible (chunkScene (Slide.chunkL s)) _ k lt) (chunk-inner s k)

-- Fragment index = start tick

ol : ∀ {A} → E.Event A → ℕ × A
ol e = E.onset e , E.leaf e

-- chunk `d` after `c` starts `gap c d` ticks after `c`
index : Flow → List Flow → List (ℕ × Flow)
index c []       = (0 , c) ∷ []
index c (d ∷ ds) = (0 , c) ∷ map (λ x → gap c d + proj₁ x , proj₂ x) (index d ds)

fragment-index : ∀ c cs → map ol (E.events (chunkFrom c cs)) ≡ index c cs
fragment-index c []       = refl
fragment-index c (d ∷ ds) =
  cong ((0 , c) ∷_)
    (trans (sym (ListP.map-∘ (E.events (chunkFrom d ds))))
           (trans (ListP.map-cong (λ e → refl) (E.events (chunkFrom d ds)))
                  (trans (ListP.map-∘ (E.events (chunkFrom d ds)))
                         (cong (map (λ x → gap c d + proj₁ x , proj₂ x)) (fragment-index d ds)))))

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
  where import Slides.Scene.Laws {ℕ} {⊥} {Flow} natMon natSub (λ ()) listOverlay as L

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
hold-out s w t le = sel-yes (w ℕP.≤? t) le nothing _

slide-read : ∀ s n → proj₂ (slideT s) n nothing ≡ show (locate s [] n)
slide-read s n with n ℕP.<? ticks s
... | yes lt = chunk-visible s n lt
... | no ¬lt = hold-out (chunkScene (Slide.chunkL s)) (ticks s) n (ℕP.≮⇒≥ ¬lt)

-- a slide, then the rest: the slide is read inside its window, the rest shifted past it and
-- inside its own
seq-nested : ∀ s (X : Deck) n → nested (pure s ⨾ X) n ≡
  S.merge (if does (ticks s ℕP.≤? n) then nothing else proj₂ (slideT s) n nothing)
          (if does (ticks s ℕP.≤? n)
             then (if does (proj₁ (S.timed slideT X) ℕP.≤? (n ∸ ticks s)) then nothing else nested X (n ∸ ticks s))
             else nothing)
seq-nested s X n = refl

deck-read : ∀ s ss n → nested (deckFrom s ss) n ≡ show (locate s ss n)
deck-read s []       n = slide-read s n
deck-read s (t ∷ ts) n with n ℕP.<? ticks s
... | yes lt =
  trans (seq-nested s (deckFrom t ts) n)
        (trans (cong₂ S.merge (sel-no (ticks s ℕP.≤? n) (ℕP.<⇒≱ lt) _ _) (sel-no (ticks s ℕP.≤? n) (ℕP.<⇒≱ lt) _ _))
               (trans (S.merge-nothing _) (chunk-visible s n lt)))
... | no ¬lt =
  trans (seq-nested s (deckFrom t ts) n)
        (trans (cong₂ S.merge (sel-yes (ticks s ℕP.≤? n) le _ _) (sel-yes (ticks s ℕP.≤? n) le _ _))
               (inner (n ∸ ticks s)))
  where
    le = ℕP.≮⇒≥ ¬lt
    inner : ∀ m → (if does (proj₁ (S.timed slideT (deckFrom t ts)) ℕP.≤? m) then nothing else nested (deckFrom t ts) m)
                  ≡ show (locate t ts m)
    inner m = trans (cong (λ k → if does (k ℕP.≤? m) then nothing else nested (deckFrom t ts) m) (steps-deck t ts))
                    (by (m ℕP.<? total t ts))
      where
        by : Dec (m < total t ts) → (if does (total t ts ℕP.≤? m) then nothing else nested (deckFrom t ts) m) ≡ show (locate t ts m)
        by (yes lt′) = trans (sel-no (total t ts ℕP.≤? m) (ℕP.<⇒≱ lt′) _ _) (deck-read t ts m)
        by (no ¬lt′) = trans (sel-yes (total t ts ℕP.≤? m) (ℕP.≮⇒≥ ¬lt′) _ _)
                             (sym (cong show (locate-out t ts m (ℕP.≮⇒≥ ¬lt′))))

-- At tick `n` a deck shows the slide it is in, at its local tick: the chunks so far.
deck-visible : ∀ s ss n → visible (flat (deckFrom s ss)) n ≡ show (locate s ss n)
deck-visible s ss n = trans (flat-visible (deckFrom s ss) n) (deck-read s ss n)
