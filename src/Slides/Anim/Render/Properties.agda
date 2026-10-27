{-# OPTIONS --safe --without-K #-}

-- The length of the rests of an animation's acts.
module Slides.Anim.Render.Properties where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (_+_; suc)

open import Data.Maybe using (Maybe)
import Data.Maybe as Maybe
open import Slides.Anim.Syntax using (Anim)

open import Slides.Anim.Render

length-restsOf : ∀ acc ls → length (restsOf acc ls) ≡ length ls
length-restsOf acc []       = refl
length-restsOf acc (l ∷ ls) = cong suc (length-restsOf (acc + l) ls)
