{-# OPTIONS --safe --without-K #-}

-- The two browser backends against the specification and against each other
-- (docs/Input.md, "Conformance"; every fact is pinned by tests/browser/nav.mjs).
--
-- Fragments of the target slide (`Slides.Backend.Conformance`):
--   plain-conforms          plain.js enters every slide as `navM` does
--   reveal-steps-conform    reveal agrees on `next` and `prev`
--   reveal-conforms-off-jumps  reveal agrees except on jumps (`Jump`): the proposal is that
--                           the specification is *slide equality* for jumps, exact for steps
--   reveal-goto-back        the deviation, stated: after a backward goto reveal shows every
--                           fragment, the specification none
-- Commands (physical input to `Nav ⊎ Ext`):
--   agree-bare              Space, PageDown, PageUp, Home, End mean the same in both
--   shiftSpace-differs, arrowDown-differs, ctrl-differs, hash-differs, hashchange-differs

module Slides.Backend.Conformance.Properties (V : Set) where

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)

open import Slides.Input.Nav
open import Slides.Input.Supports V
open import Slides.Backend.Input
open import Slides.Backend.Command V
open import Slides.Backend.Conformance
import Slides.Backend.Reveal.Supports as R
import Slides.Backend.Plain.Supports as P

------------------------------------------------------------------------
-- Fragments after a jump

plain-conforms : ∀ n d → plainEntry n d ≡ specEntry n d
plain-conforms next          _ = refl
plain-conforms prev          _ = refl
plain-conforms first         _ = refl
plain-conforms last          _ = refl
plain-conforms (goto _)      _ = refl
plain-conforms (gotoLabel _) _ = refl

reveal-steps-conform : ∀ d → revealEntry next d ≡ specEntry next d × revealEntry prev d ≡ specEntry prev d
reveal-steps-conform _ = refl , refl

reveal-conforms-off-jumps : ∀ n d → revealEntry n d ≡ specEntry n d ⊎ Jump n
reveal-conforms-off-jumps next          _    = inj₁ refl
reveal-conforms-off-jumps prev          _    = inj₁ refl
reveal-conforms-off-jumps first         _    = inj₂ jfirst
reveal-conforms-off-jumps last          _    = inj₂ jlast
reveal-conforms-off-jumps (goto _)      _    = inj₂ jgoto
reveal-conforms-off-jumps (gotoLabel _) _    = inj₂ jlabel

fresh≢full : fresh ≢ full
fresh≢full ()

reveal-goto-back : ∀ k → revealEntry (goto k) back ≡ full × specEntry (goto k) back ≡ fresh
reveal-goto-back _ = refl , refl

-- Going forward, goto agrees.
reveal-goto-fwd : ∀ k → revealEntry (goto k) fwd ≡ specEntry (goto k) fwd
reveal-goto-fwd _ = refl

------------------------------------------------------------------------
-- Commands

revealCommand : Mode → Event → Maybe (Nav ⊎ Ext)
revealCommand m = command (R.revealSupports V) (R.revealRead m)

plainCommand : Event → Maybe (Nav ⊎ Ext)
plainCommand = command (P.plainSupports V) P.plainRead

private
  bare′ : KeyName → Event
  bare′ n = keydown (n , bare)

-- The keys both backends bind, with the same meaning.
agree-bare : ∀ m → (revealCommand m (bare′ space) ≡ plainCommand (bare′ space))
               × (revealCommand m (bare′ pageDown) ≡ plainCommand (bare′ pageDown))
               × (revealCommand m (bare′ pageUp) ≡ plainCommand (bare′ pageUp))
               × (revealCommand m (bare′ home) ≡ plainCommand (bare′ home))
               × (revealCommand m (bare′ end) ≡ plainCommand (bare′ end))
agree-bare linear  = refl , refl , refl , refl , refl
agree-bare stacked = refl , refl , refl , refl , refl

-- Plain ignores modifiers: Shift+Space is `next` there and `prev` in reveal.
shiftSpace-differs : ∀ m → revealCommand m (keydown (space , shift)) ≡ just (inj₁ prev)
                         × plainCommand (keydown (space , shift)) ≡ just (inj₁ next)
shiftSpace-differs linear  = refl , refl
shiftSpace-differs stacked = refl , refl

-- Ctrl+ArrowRight: reveal ignores it, plain takes it as `next`.
ctrl-differs : ∀ m → revealCommand m (keydown (arrowRight , ctrl)) ≡ nothing
                   × plainCommand (keydown (arrowRight , ctrl)) ≡ just (inj₁ next)
ctrl-differs linear  = refl , refl
ctrl-differs stacked = refl , refl

-- ArrowDown on a stacked deck: no `Nav` command in reveal (a no-op on a horizontal slide),
-- `next` in plain.  On a linear deck reveal agrees with plain.
arrowDown-differs : revealCommand stacked (bare′ arrowDown) ≡ nothing
                  × plainCommand (bare′ arrowDown) ≡ just (inj₁ next)
arrowDown-differs = refl , refl

arrowDown-linear-agrees : revealCommand linear (bare′ arrowDown) ≡ plainCommand (bare′ arrowDown)
arrowDown-linear-agrees = refl

-- `#3` is slide 3 (zero-based) in reveal and slide 3 (one-based, so position 2) in plain;
-- `#/h/v` is read by reveal only.
hash-differs : ∀ m → revealCommand m (hashLoad (flat 3)) ≡ just (inj₁ (goto 3))
                   × plainCommand (hashLoad (flat 3)) ≡ just (inj₁ (goto 2))
hash-differs linear  = refl , refl
hash-differs stacked = refl , refl

grid-hash-differs : ∀ m → revealCommand m (hashLoad (grid 2 0)) ≡ just (inj₁ (goto 2))
                        × plainCommand (hashLoad (grid 2 0)) ≡ nothing
grid-hash-differs linear  = refl , refl
grid-hash-differs stacked = refl , refl

-- A hash change after load: reveal navigates, plain does not.
hashchange-differs : ∀ m → revealCommand m (hashChange (grid 5 0)) ≡ just (inj₁ (goto 5))
                         × plainCommand (hashChange (grid 5 0)) ≡ nothing
hashchange-differs linear  = refl , refl
hashchange-differs stacked = refl , refl

-- Only reveal has the overview.
overview-only-reveal : ∀ m → revealCommand m (bare′ keyO) ≡ just (inj₂ overview)
                           × plainCommand (bare′ keyO) ≡ nothing
overview-only-reveal linear  = refl , refl
overview-only-reveal stacked = refl , refl
