{-# OPTIONS --safe --without-K #-}

-- Laws of `plainSupports` and the facts the browser tests found for `assets/plain.js`.
--
--   plainKinds-disjoint   the key kinds are pairwise disjoint (decided)
--   plainKeys-kind        no kind is shadowed
--   plain-render          the canonical input of each command reads back as that command
--   plain-command         ... and through `Supports.dec`
--   plain-ignores-mods    modifiers do not matter (Shift+Space and Ctrl+ArrowRight are `next`)
--   plain-no-hashchange   a hash change after load is not read
--   plain-hash-*          `#n` is one-based and flat; there is no two-dimensional hash

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

------------------------------------------------------------------------
-- What plain.js does

plain-ignores-mods : ∀ n m m′ → plainKey (n , m) ≡ plainKey (n , m′)
plain-ignores-mods _ _ _ = refl

shiftSpace-next : plainKey (space , shift) ≡ just (nav next)
shiftSpace-next = refl

ctrlRight-next : plainKey (arrowRight , ctrl) ≡ just (nav next)
ctrlRight-next = refl

-- ArrowDown is `next` whatever the deck.
arrowDown-next : ∀ m → plainKey (arrowDown , m) ≡ just (nav next)
arrowDown-next _ = refl

plain-no-hashchange : ∀ h → plainRead (hashChange h) ≡ nothing
plain-no-hashchange _ = refl

-- One-based and flat.
plain-hash-one-based : ∀ n → plainHash (flat (suc n)) ≡ just (nav (goto n))
plain-hash-one-based _ = refl

plain-hash-clamp : plainHash (flat zero) ≡ just (nav (goto zero))
plain-hash-clamp = refl

plain-no-grid : ∀ h v → plainHash (grid h v) ≡ nothing
plain-no-grid _ _ = refl

-- Plain can present every deck; an `await overview` is skipped (it has no overview).
plainSupports-total : NavTotal (plainSupports V)
plainSupports-total n = nav n , refl

plain-skips-overview : inj (plainSupports V) (inj₂ overview) ≡ nothing
plain-skips-overview = refl
