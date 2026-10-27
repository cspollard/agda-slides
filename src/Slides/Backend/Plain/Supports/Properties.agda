{-# OPTIONS --safe --without-K #-}

-- Laws of `plainSupports`.
--
--   plainKeys-kind       the key kinds are pairwise disjoint (checked when `plainKeys` is
--                        defined) and none is shadowed
--   plain-render         the canonical input of each command reads back as that command
--   plain-command        ... and through `Supports.dec`
--
-- What plain.js does with modifiers and hashes is a table in docs/Input.md, pinned by
-- tests/browser/nav.mjs, not theorems: nothing depends on it.

module Slides.Backend.Plain.Supports.Properties (V : Set) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Input.Binding.Properties using (bind-kind)
open import Slides.Input.Supports V
open Supports
open import Slides.Input.Supports.Properties V using (command-render)
open import Slides.Backend.Input
open import Slides.Backend.Plain.Supports

plainKeys-kind : ∀ {d : Decoder KeyName PCmd} {n s} → d ∈ plainKinds → d n ≡ just s →
                 plainKeys n ≡ just s
plainKeys-kind = bind-kind names names-cover plainKinds tt

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
