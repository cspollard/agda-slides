{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: "Knuth85" is not a declared reference.

module MissingCitation where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Core using (Body)
open import Slides.DSL
open import Slides.Resources

resources : Resources
resources = record { figures = [] ; references = ("Knuth84" , "The TeXbook") ∷ [] }

open Checked resources

typo : Body
typo = paragraph ("see " ∷ cite "Knuth85" ∷ [])
