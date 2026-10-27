{-# OPTIONS --safe --without-K #-}

-- Spike: the navigation vocabulary.
--
-- `Nav` has decidable equality, so decks (`Prog (Nav ⊎ C)`) have a machine
-- (`Slides.Spike.Input.Machine`) in which `next` is the awaited command.  The
-- remaining commands (`prev`, `goto`, `gotoLabel`, `first`, `last`) are not awaited
-- by the program: they are interpreted by `navM`, which keeps a *position* and
-- shows the deck machine replayed by that many `next`s.  This is the history
-- model (replay), so going back needs no inverse of `step`.

module Slides.Spike.Input.Nav (V : Set) where

open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; zero; suc; _⊓_; _≤_; s≤s)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m; _≟_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
import Data.String.Properties as Str

open import Slides.Spike.Input.Prog V
open import Slides.Spike.Input.Machine V
open Machine

_≟N_ : DecidableEquality Nav
next ≟N next = yes refl
prev ≟N prev = yes refl
first ≟N first = yes refl
last ≟N last = yes refl
goto m ≟N goto n = map′ (cong goto) (λ { refl → refl }) (m ≟ n)
gotoLabel a ≟N gotoLabel b = map′ (cong gotoLabel) (λ { refl → refl }) (a Str.≟ b)
next ≟N prev = no λ ()
next ≟N first = no λ ()
next ≟N last = no λ ()
next ≟N goto _ = no λ ()
next ≟N gotoLabel _ = no λ ()
prev ≟N next = no λ ()
prev ≟N first = no λ ()
prev ≟N last = no λ ()
prev ≟N goto _ = no λ ()
prev ≟N gotoLabel _ = no λ ()
first ≟N next = no λ ()
first ≟N prev = no λ ()
first ≟N last = no λ ()
first ≟N goto _ = no λ ()
first ≟N gotoLabel _ = no λ ()
last ≟N next = no λ ()
last ≟N prev = no λ ()
last ≟N first = no λ ()
last ≟N goto _ = no λ ()
last ≟N gotoLabel _ = no λ ()
goto _ ≟N next = no λ ()
goto _ ≟N prev = no λ ()
goto _ ≟N first = no λ ()
goto _ ≟N last = no λ ()
goto _ ≟N gotoLabel _ = no λ ()
gotoLabel _ ≟N next = no λ ()
gotoLabel _ ≟N prev = no λ ()
gotoLabel _ ≟N first = no λ ()
gotoLabel _ ≟N last = no λ ()
gotoLabel _ ≟N goto _ = no λ ()

module _ {C : Set} (M : Machine (Nav ⊎ C)) (len : ℕ) (labels : String → Maybe ℕ) where

  replay : ℕ → State M
  replay zero    = init M
  replay (suc n) = step M (replay n) (inj₁ next)

  navStep : ℕ → Nav → ℕ
  navStep n next          = suc n ⊓ len
  navStep zero    prev    = zero
  navStep (suc n) prev    = n
  navStep n first         = zero
  navStep n last          = len
  navStep n (goto k)      = k ⊓ len
  navStep n (gotoLabel l) = maybe′ (_⊓ len) n (labels l)

  -- The machine a navigating backend runs: position and replay.
  navM : Machine Nav
  navM = record { State = ℕ ; init = zero ; step = navStep ; view = λ n → view M (replay n) }

  -- Replay is the deck machine on `next`s.
  view-next : ∀ n → suc n ≤ len → view navM (navStep n next) ≡ view M (step M (replay n) (inj₁ next))
  view-next n le = cong (λ k → view M (replay k)) (m≤n⇒m⊓n≡m le)

  -- `prev` undoes `next` (inside the deck).
  prev-next : ∀ n → suc n ≤ len → navStep (navStep n next) prev ≡ n
  prev-next n le rewrite m≤n⇒m⊓n≡m le = refl
