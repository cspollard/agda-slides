{-# OPTIONS --safe --without-K #-}

-- Control for ../MissingCitation.agda: MUST typecheck (the key is declared).

module CitationOk where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Deck.DSL

resources : Resources
resources = record { figures = [] ; references = ("Knuth84" , "The TeXbook") ∷ [] }

open Checked resources

ok : Body
ok = paragraph ("see " ∷ cite "Knuth84" ∷ [])
