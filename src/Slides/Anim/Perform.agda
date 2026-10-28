{-# OPTIONS --safe --without-K #-}

-- The performance of a scene, after Hudak: its leaves with the tick each starts at, in order.
--
--     perform : Scene A → ℕ × List (ℕ × A)          (duration, events (onset, leaf))
--
-- A leaf starts at 0; `Seq` starts the second operand after the first's duration, `Par` shares the
-- start, `Delay n` starts `n` later, `Hold n` drops what starts outside its window, `Repeat n`
-- lays `n` copies end to end.  It is the algebra of `TimeC` into `ℕ × List (ℕ × –)` (`foldS`), so a
-- substitution of scenes is a fold of folds (`foldS-bind`).  It is the ℕ clock read once, without
-- the frames: `Slides.Steps` reads the fragments of a slide and `Slides.Input.Slides.Properties`
-- the starts of the slides of a deck from it.

module Slides.Anim.Perform where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁)

open import Slides.Anim.Syntax

Events : Set → Set
Events A = List (ℕ × A)

Perf : Set → Set
Perf A = ℕ × Events A

private
  shift : ∀ {A} → ℕ → Events A → Events A
  shift n = map (map₁ (n +_))

  copies : ∀ {A} → ℕ → ℕ → Events A → Events A
  copies zero    d l = []
  copies (suc m) d l = l ++ shift d (copies m d l)

performAlg : ∀ {A} → (s : TOp) → (tarity s → Perf A) → Perf A
performAlg Seq        k = proj₁ (k fz) + proj₁ (k (fs fz)) , proj₂ (k fz) ++ shift (proj₁ (k fz)) (proj₂ (k (fs fz)))
performAlg Par        k = proj₁ (k fz) ⊔ proj₁ (k (fs fz)) , proj₂ (k fz) ++ proj₂ (k (fs fz))
performAlg (Hold n)   k = n , filterᵇ (λ e → proj₁ e <ᵇ n) (proj₂ (k _))
performAlg (Delay n)  k = n + proj₁ (k _) , shift n (proj₂ (k _))
performAlg (Repeat n) k = n * proj₁ (k _) , copies n (proj₁ (k _)) (proj₂ (k _))
performAlg (Drive _)  k = k _

perform : ∀ {A} → Scene A → Perf A
perform = foldS (λ a → 0 , (0 , a) ∷ []) performAlg
