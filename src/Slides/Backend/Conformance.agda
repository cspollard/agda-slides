{-# OPTIONS --safe --without-K #-}

-- How much of a slide's fragments a jump leaves shown, per backend (docs/Input.md,
-- "Conformance").  A table of observed behaviour, pinned by `tests/browser/nav.mjs`:
-- it is the vocabulary of the conformance statements in `Slides.Backend.Conformance.Properties`.
--
--   Dir      the target slide lies before (`back`) or after (`fwd`) the current one
--   Entry    the target slide shows none of its fragments (`fresh`) or all (`full`)
--   specEntry   `navM` (`Slides.Input.Navigation`) replays `next`s: `next` enters a slide
--               fresh, `prev` enters the previous slide full (the end of its replay), `goto`
--               and `gotoLabel` land at the position where the slide starts (fresh), `first`
--               is position 0 (fresh), `last` is position `len` (full)
--   plainEntry  assets/plain.js: `show(i, revealAll)` with `revealAll` true after `prev`, `End`
--   revealEntry reveal.js shows the fragments of every slide *before* the current one and hides
--               those after (`updateSlides`, `showFragmentsIn`): a jump back lands on a slide
--               that was shown full, a jump forward on one that was hidden.

module Slides.Backend.Conformance where

open import Slides.Input.Nav

data Dir : Set where
  back fwd : Dir

data Entry : Set where
  fresh full : Entry

specEntry plainEntry revealEntry : Nav → Dir → Entry

specEntry next          _ = fresh
specEntry prev          _ = full
specEntry first         _ = fresh
specEntry last          _ = full
specEntry (goto _)      _ = fresh
specEntry (gotoLabel _) _ = fresh

plainEntry next          _ = fresh
plainEntry prev          _ = full
plainEntry first         _ = fresh
plainEntry last          _ = full
plainEntry (goto _)      _ = fresh
plainEntry (gotoLabel _) _ = fresh

revealEntry next          _    = fresh
revealEntry prev          _    = full
revealEntry first         _    = full
revealEntry last          _    = fresh
revealEntry (goto _)      back = full
revealEntry (goto _)      fwd  = fresh
revealEntry (gotoLabel _) back = full
revealEntry (gotoLabel _) fwd  = fresh

-- The commands that jump.
data Jump : Nav → Set where
  jfirst : Jump first
  jlast  : Jump last
  jgoto  : ∀ {n} → Jump (goto n)
  jlabel : ∀ {s} → Jump (gotoLabel s)
