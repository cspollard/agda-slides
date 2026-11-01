{-# OPTIONS --safe --without-K #-}

-- What a deck does, stated once in the vocabulary of `Semantics.Behaviour`.
--
--   stream d     the deck's meaning is a stream on the step clock: `Beh ⊤ O`, and `List ⊤ ≅ ℕ`
--   deckBeh d    its interactive behaviour: that stream reindexed along the position map
--   deckM-beh    the deck's machine (`Slides.Deck.Machine.deckM`) has exactly that behaviour
--   deckM-unique ... and any coalgebra map out of the machine sends its initial state to `deckBeh d`
--
-- Per slide, the program of a slide (`slideP`) given `t` nexts shows, at its start, the slide's stream at `t`:
--   `slide-beh`  `now` after `slideP`, reindexed along `map (λ _ → next)`, is `slideStream`
-- Per deck this does not hold syntactically (it would need preemption): the deck is a reindexing
-- of the step stream, not a sub-object of the programs.
--
-- A slide's stream is the deck's, shifted to where the slide starts:
--   `before ps`       the ticks of the slides ps, the step at which the next slide begins
--   `slide-shift`     for t < ticks u: the deck's stream at `before ps + t` is the slide's stream at `t`
--   `slide-shift-beh` the same in `Behaviour` terms: the deck's stream reindexed along
--                     `replicate (before ps) tt ++_` agrees with `slideStream` on the slide's range
--   `slideStream-sat` past its last step the slide saturates: its stream stays at the full slide;
--                     the deck does not, at `before ps + ticks u` it is in the next slide (`deck-visible`)

module Slides.Deck.Behaviour where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_; map; length; replicate)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _<_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_,_)
open import Relation.Nullary using (yes; no)
open import Data.Maybe.Base using (just)
open import Data.List.NonEmpty using (_∷_)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import Relation.Binary.PropositionalEquality as ≡
import Data.List.Properties as ListP

open import Categories.Functor.Coalgebra using (F-Coalgebra-Morphism)

open import Semantics.Behaviour using (Beh; reindex; mapO; obs-unique; behCoalg)
import Slides.Program.Machine as Machine
open import Slides.Program.Navigation using (Nav; next)
open import Slides.Deck.Syntax using (Deck; flat; chunkFrom; Slide; slide; ticks; deckFrom)
open import Slides.Deck.Steps using (chunkSteps; chunkSteps-gap; gap)
open import Slides.Deck.Content
open import Slides.Deck.Read using (visible; accumL; go-visible; locate; deck-visible; show; sel-yes)
open import Slides.Deck.Machine using (deckM; pos; feed-deckM)
open import Slides.Deck.Program using (slideP; now; nowF; pause-visible)

-- what is seen: the flow shown, or nothing
O : Setoid 0ℓ 0ℓ
O = ≡.setoid (Maybe Flow)

-- a stream on the step clock: the reading after `n` ticks, `n` the length of the word of ticks
stream : Deck → Setoid.Carrier (Beh ⊤ O)
stream d ts = visible (flat d) (length ts)

-- a position as a word of ticks
ticks⋆ : ℕ → List ⊤
ticks⋆ n = replicate n tt

-- the behaviour of a deck: the stream, reindexed along where the commands leave the position
deckBeh : Deck → Setoid.Carrier (Beh Nav O)
deckBeh d = reindex {O = O} (λ cs → ticks⋆ (pos d cs)) ⟨$⟩ stream d

-- the machine of the deck behaves as `deckBeh d`
deckM-beh : ∀ d cs → Machine.feed O (deckM d) cs ≡ deckBeh d cs
deckM-beh d cs = trans (feed-deckM d cs) (cong (visible (flat d)) (sym (ListP.length-replicate (pos d cs))))

-- uniqueness: any coalgebra map out of the machine, from its initial state, is `deckBeh d`
deckM-unique : ∀ d (h : F-Coalgebra-Morphism (Machine.coalg O (deckM d)) (behCoalg Nav O)) cs →
               (F-Coalgebra-Morphism.f h ⟨$⟩ Machine.init (deckM d)) cs ≡ deckBeh d cs
deckM-unique d h cs = trans (sym (obs-unique Nav O (Machine.coalg O (deckM d)) h cs)) (deckM-beh d cs)

-- A slide

-- the stream of a slide on its own step clock
slideStream : Flow → List Flow → Setoid.Carrier (Beh ⊤ O)
slideStream c cs ts = visible (chunkFrom c cs) (length ts)

-- the slide's program, read at its start, as a behaviour in the commands
slideNow : Flow → List Flow → Setoid.Carrier (Beh Nav O)
slideNow c cs = mapO nowF ⟨$⟩ slideP c cs

-- a word of ticks, as that many `next`s
nexts : List ⊤ → List Nav
nexts = map (λ _ → next)

nexts-replicate : ∀ ts → nexts ts ≡ replicate (length ts) next
nexts-replicate []       = refl
nexts-replicate (_ ∷ ts) = cong (next ∷_) (nexts-replicate ts)

-- the program of a slide, driven by `t` `next`s and read at its start, is the slide's stream at `t`
slide-beh : ∀ c cs ts → (reindex {O = O} nexts ⟨$⟩ slideNow c cs) ts ≡ slideStream c cs ts
slide-beh c cs ts = trans (cong (λ z → now (slideP c cs z)) (nexts-replicate ts)) (pause-visible c cs (length ts))

-- A slide in its deck

-- the ticks of the slides before: the step at which the next slide begins
before : List Slide → ℕ
before []       = 0
before (p ∷ ps) = ticks p + before ps

-- the deck whose slides are `ps ++ u ∷ us`, `u` the slide of interest
deckOf : List Slide → Slide → List Slide → Deck
deckOf []       u us = deckFrom u us
deckOf (p ∷ ps) u us = deckFrom p (ps ++ u ∷ us)

private
  locate-in : ∀ u us t → t < ticks u → locate u us t ≡ just (u , t)
  locate-in u []       t lt with t ℕP.<? ticks u
  ... | yes _  = refl
  ... | no ¬lt = ⊥-elim (¬lt lt)
  locate-in u (_ ∷ _)  t lt with t ℕP.<? ticks u
  ... | yes _  = refl
  ... | no ¬lt = ⊥-elim (¬lt lt)

  -- a slide that is over is skipped
  locate-skip : ∀ p q qs n → ticks p ≤ n → locate p (q ∷ qs) n ≡ locate q qs (n ∸ ticks p)
  locate-skip p q qs n le with n ℕP.<? ticks p
  ... | yes lt = ⊥-elim (ℕP.<⇒≱ lt le)
  ... | no _   = refl

  locate-at : ∀ p ps u us t → t < ticks u → locate p (ps ++ u ∷ us) (ticks p + (before ps + t)) ≡ just (u , t)
  locate-at p []       u us t lt =
    trans (locate-skip p u us _ (ℕP.m≤m+n _ _)) (trans (cong (locate u us) (ℕP.m+n∸m≡n (ticks p) t)) (locate-in u us t lt))
  locate-at p (q ∷ qs) u us t lt =
    trans (locate-skip p q (qs ++ u ∷ us) _ (ℕP.m≤m+n _ _))
          (trans (cong (locate q (qs ++ u ∷ us)) (ℕP.m+n∸m≡n (ticks p) _))
                 (trans (cong (locate q (qs ++ u ∷ us)) (ℕP.+-assoc (ticks q) (before qs) t)) (locate-at q qs u us t lt)))

-- the deck at `before ps + t` shows what the slide shows at `t`
slide-shift : ∀ ps l c cs us t → t < ticks (slide l (c ∷ cs)) →
              visible (flat (deckOf ps (slide l (c ∷ cs)) us)) (before ps + t) ≡ visible (chunkFrom c cs) t
slide-shift [] l c cs us t lt =
  trans (deck-visible (slide l (c ∷ cs)) us t) (trans (cong show (locate-in _ us t lt)) (sym (go-visible c cs t)))
slide-shift (p ∷ ps) l c cs us t lt =
  trans (cong (visible (flat (deckFrom p (ps ++ slide l (c ∷ cs) ∷ us)))) (ℕP.+-assoc (ticks p) (before ps) t))
        (trans (deck-visible p (ps ++ slide l (c ∷ cs) ∷ us) (ticks p + (before ps + t)))
               (trans (cong show (locate-at p ps _ us t lt)) (sym (go-visible c cs t))))

-- as behaviours: the deck's stream, started `before ps` ticks late, is the slide's on its range
shift : List Slide → List ⊤ → List ⊤
shift ps = replicate (before ps) tt ++_

slide-shift-beh : ∀ ps l c cs us ts → length ts < ticks (slide l (c ∷ cs)) →
                  (reindex {O = O} (shift ps) ⟨$⟩ stream (deckOf ps (slide l (c ∷ cs)) us)) ts ≡ slideStream c cs ts
slide-shift-beh ps l c cs us ts lt =
  trans (cong (visible (flat (deckOf ps (slide l (c ∷ cs)) us)))
              (trans (ListP.length-++ (replicate (before ps) tt) {ts}) (cong (_+ length ts) (ListP.length-replicate (before ps)))))
        (slide-shift ps l c cs us (length ts) lt)

-- past its last step the slide saturates: it stays at the whole slide
slideStream-sat : ∀ c cs t → chunkSteps (c ∷ cs) ≤ t → accumL c cs t ≡ accumL c cs (chunkSteps (c ∷ cs))
slideStream-sat c []       t le = refl
slideStream-sat c (d ∷ ds) t le =
  trans (sel-yes (gap c d ℕP.≤? t) g _ _)
        (trans (cong (c ++_) (slideStream-sat d ds (t ∸ gap c d) (ℕP.m+n≤o⇒m≤o∸n (chunkSteps (d ∷ ds)) (subst (_≤ t) (ℕP.+-comm (gap c d) _) le′))))
               (sym (trans (cong (accumL c (d ∷ ds)) e)
                           (trans (sel-yes (gap c d ℕP.≤? T′) (ℕP.m≤m+n _ _) _ _)
                                  (cong (λ n → c ++ accumL d ds n) (ℕP.m+n∸m≡n (gap c d) _))))))
  where
    e   = chunkSteps-gap c d ds
    T′  = gap c d + chunkSteps (d ∷ ds)
    le′ = subst (_≤ t) e le
    g   = ℕP.≤-trans (ℕP.m≤m+n _ _) le′
