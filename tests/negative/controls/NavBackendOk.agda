{-# OPTIONS --safe --without-K #-}

-- Control for ../NoNavBackend.agda: MUST typecheck.  Programs are presented unchanged on a
-- backend that binds every command of `Nav` (reveal's vocabulary, and plain's).

module NavBackendOk where

open import Container.Lowering using (_≈⋆_)

open import Slides.Program.Navigation using (Nav)
open import Slides.Program.Supports using (skipU)
open import Slides.Program.Syntax using (Program)
open import Slides.Backend.Input.Properties

okReveal : ∀ {T D A} (p : Program T D Nav A) → skipU revealSupports p ≈⋆ p
okReveal = presents revealSupports reveal-total

okPlain : ∀ {T D A} (p : Program T D Nav A) → skipU plainSupports p ≈⋆ p
okPlain = presents plainSupports plain-total
