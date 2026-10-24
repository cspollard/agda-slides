{-# OPTIONS --safe --without-K #-}

-- Checks that both dependencies resolve; delete once real modules import them.
module Slides.Smoke where

open import Data.Container using (Container)
open import Data.Container.FreeMonad using (_⋆_)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Adjoint.Construction.EilenbergMoore using ()
