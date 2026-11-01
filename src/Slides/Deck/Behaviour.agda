{-# OPTIONS --safe --without-K #-}

-- What a deck does, stated once in the vocabulary of `Semantics.Behaviour`.
--
--   stream d     the deck's meaning is a stream on the step clock: `Beh ⊤ O`, and `List ⊤ ≅ ℕ`
--   deckBeh d    its interactive behaviour: that stream reindexed along the position map
--   deckM-beh    the deck's machine (`Slides.Deck.Machine.deckM`) has exactly that behaviour
--   deckM-hom    ... and `deckBeh d` is the image of the machine under the unique map to the final machine
--
-- Per slide, the program of a slide (`slideP`) given `t` nexts shows, at its start, the slide's stream at `t`:
--   `slide-beh`  `now` after `slideP`, reindexed along `map (λ _ → next)`, is `slideStream`
-- Per deck this does not hold syntactically (it would need preemption): the deck is a reindexing
-- of the step stream, not a sub-object of the programs.

module Slides.Deck.Behaviour where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; map; length; replicate)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Relation.Binary.PropositionalEquality as ≡
import Data.List.Properties as ListP

open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Functor.Coalgebra using (F-Coalgebra-Morphism)

open import Semantics.Behaviour using (Beh; reindex; mapO; obs-unique; behCoalg)
import Slides.Program.Machine as Machine
open import Slides.Program.Navigation using (Nav; next)
open import Slides.Deck.Syntax using (Deck; flat; chunkFrom)
open import Slides.Deck.Content
open import Slides.Deck.Read using (visible)
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
