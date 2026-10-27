{-# OPTIONS --safe --without-K #-}

-- Laws of `plainSupports`.
--
--   plainKinds-disjoint   the key kinds are pairwise disjoint (decided)
--   plainKeys-kind        no kind is shadowed
--   plain-render          the canonical input of each command reads back as that command
--   plain-command         ... and through `Supports.dec`
--   plainSupports-total   plain supports all of `Nav`
--
-- What plain.js does with modifiers and hashes is a table in docs/Input.md, pinned by
-- tests/browser/nav.mjs, not theorems: nothing depends on it.

module Slides.Backend.Plain.Supports.Properties (V : Set) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
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
open import Slides.Backend.Plain.Supports

plainKinds-disjoint : AllPairs Disjoint plainKinds
plainKinds-disjoint = toWitness {a? = disjoint*? names names-cover plainKinds} tt

plainKeys-kind : ∀ {d : Decoder KeyName PCmd} {n s} → d ∈ plainKinds → d n ≡ just s →
                 plainKeys n ≡ just s
plainKeys-kind mem e = choice-∈ plainKinds-disjoint mem _ e

plain-render : ∀ s {e} → plainRender s ≡ just e → plainRead e ≡ just s
plain-render (nav next)  refl = refl
plain-render (nav prev)  refl = refl
plain-render (nav first) refl = refl
plain-render (nav last)  refl = refl
plain-render (nav (goto n)) refl = refl
plain-render (nav (gotoLabel _)) ()
plain-render clock ()

plain-command : ∀ {k s e} → inj (plainSupports V) k ≡ just s → plainRender s ≡ just e →
                command (plainSupports V) plainRead e ≡ just k
plain-command = command-render (plainSupports V) plainRead plainRender (λ s _ → plain-render s)

-- Plain can present every deck (an `await overview` is skipped: it has no overview).
plainSupports-total : NavTotal (plainSupports V)
plainSupports-total n = nav n , refl
