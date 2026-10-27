{-# OPTIONS --safe --without-K #-}

-- Laws of `revealSupports` and the facts the browser tests found (tests/browser/nav.mjs).
--
--   revealKinds-disjoint   the key kinds of each mode are pairwise disjoint (decided)
--   revealKeys-kind        no kind is shadowed: a key of a kind decodes to that kind's command
--   reveal-render          the canonical input of each command reads back as that command
--   reveal-command         ... and through `Supports.dec`: supported commands round-trip
--   shiftSpace-prev, ctrl-ignored, arrowDown-*, hashchange-*, hash-flat-zero-based:
--                          what reveal does, as theorems (plain's differences are in
--                          `Slides.Backend.Conformance.Properties`)

module Slides.Backend.Reveal.Supports.Properties (V : Set) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder; Disjoint)
open import Slides.Input.Supports V
open Supports
open import Slides.Backend.Input
open import Slides.Backend.Input.Properties
open import Slides.Backend.Command V
open import Slides.Backend.Command.Properties V
open import Slides.Backend.Reveal.Supports

------------------------------------------------------------------------
-- The key table

kinds : Mode → List (Decoder Key RCmd)
kinds linear  = linearKinds
kinds stacked = stackedKinds

kinds-disjoint : ∀ m → AllPairs Disjoint (kinds m)
kinds-disjoint linear  = toWitness {a? = disjoint*? keys keys-cover linearKinds} tt
kinds-disjoint stacked = toWitness {a? = disjoint*? keys keys-cover stackedKinds} tt

revealKeys-kind : ∀ m {d : Decoder Key RCmd} {i s} → d ∈ kinds m → d i ≡ just s →
                  revealKeys m i ≡ just s
revealKeys-kind linear  mem e = choice-∈ (kinds-disjoint linear) mem _ e
revealKeys-kind stacked mem e = choice-∈ (kinds-disjoint stacked) mem _ e

------------------------------------------------------------------------
-- Round trips

reveal-render : ∀ m s {e} → revealRender m s ≡ just e → revealRead m e ≡ just s
reveal-render linear  (nav next)  refl = refl
reveal-render stacked (nav next)  refl = refl
reveal-render linear  (nav prev)  refl = refl
reveal-render stacked (nav prev)  refl = refl
reveal-render linear  (nav first) refl = refl
reveal-render stacked (nav first) refl = refl
reveal-render linear  (nav last)  refl = refl
reveal-render stacked (nav last)  refl = refl
reveal-render linear  (nav (goto n)) refl = refl
reveal-render stacked (nav (goto n)) refl = refl
reveal-render linear  (nav (gotoLabel _)) ()
reveal-render stacked (nav (gotoLabel _)) ()
reveal-render linear  (ext overview) refl = refl
reveal-render stacked (ext overview) refl = refl
reveal-render linear  (ext tick) ()
reveal-render stacked (ext tick) ()
reveal-render linear  (move _) ()
reveal-render stacked (move right) refl = refl
reveal-render stacked (move left)  refl = refl
reveal-render stacked (move down)  refl = refl
reveal-render stacked (move up)    refl = refl
reveal-render linear  (slideV _ zero) ()
reveal-render stacked (slideV _ zero) ()
reveal-render linear  (slideV _ (suc _)) refl = refl
reveal-render stacked (slideV _ (suc _)) refl = refl

reveal-command : ∀ m {k s e} → inj (revealSupports V) k ≡ just s → revealRender m s ≡ just e →
                 command (revealSupports V) (revealRead m) e ≡ just k
reveal-command m = command-render (revealSupports V) (revealRead m) (revealRender m)
                     (λ s _ → reveal-render m s)

------------------------------------------------------------------------
-- What reveal does

-- Shift+Space is `prev`.
shiftSpace-prev : ∀ m → revealKeys m (space , shift) ≡ just (nav prev)
shiftSpace-prev linear  = refl
shiftSpace-prev stacked = refl

-- Ctrl and meta disable every key.
ctrl-ignored : ∀ m n → revealKeys m (n , ctrl) ≡ nothing
ctrl-ignored linear  = ∀-names (λ n → isNothing? (revealKeys linear (n , ctrl))) tt
ctrl-ignored stacked = ∀-names (λ n → isNothing? (revealKeys stacked (n , ctrl))) tt

-- ArrowDown moves one step in a linear deck and down the grid in a stacked deck, where it
-- is no `Nav` command (on a horizontal slide it does nothing).
arrowDown-linear : revealKeys linear (arrowDown , bare) ≡ just (nav next)
arrowDown-linear = refl

arrowDown-stacked : revealKeys stacked (arrowDown , bare) ≡ just (move down)
arrowDown-stacked = refl

arrowDown-stacked-no-nav : command (revealSupports V) (revealRead stacked) (keydown (arrowDown , bare)) ≡ nothing
arrowDown-stacked-no-nav = refl

-- `hashchange` is read like the hash on load; `#n` is `#/n` (zero-based).
hashchange-load : ∀ m h → revealRead m (hashChange h) ≡ revealRead m (hashLoad h)
hashchange-load _ _ = refl

hash-flat-grid : ∀ n → revealHash (flat n) ≡ revealHash (grid n 0)
hash-flat-grid _ = refl

-- Reveal can present every deck: it supports all of `Nav` (and the extras).
revealSupports-total : NavTotal (revealSupports V)
revealSupports-total n = nav n , refl
