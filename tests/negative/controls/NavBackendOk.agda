{-# OPTIONS --safe --without-K #-}

-- Control for ../NoNavBackend.agda: MUST typecheck.  The same deck presented on a backend that
-- supports `Nav` (reveal's vocabulary).

module NavBackendOk where

open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Slides.Input ⊤
open import Slides.Input.Supports ⊤
open Supports
open import Slides.Backend.Input using (Ext)
open import Slides.Backend.Reveal.Supports using (revealSupports; nav)
open import Slides.Backend.Plain.Supports using (plainSupports) renaming (nav to pnav)

ok : Prog (S (revealSupports ⊤)) ⊤
ok = present (revealSupports ⊤) (λ n → nav n , refl) pause

okPlain : Prog (S (plainSupports ⊤)) ⊤
okPlain = present (plainSupports ⊤) (λ n → pnav n , refl) pause
