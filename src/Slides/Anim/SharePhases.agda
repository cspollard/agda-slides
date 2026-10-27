{-# OPTIONS --safe --without-K #-}

-- What the backend ships for the phases of a parametric animation, with shared subformulas.
--
-- A phase (`Slides.Anim.Phases`) is a list of elements, each with the formulas of its numbers.
-- Here the formulas of *all the elements of a phase* are shared through one store
-- (`Slides.Anim.Share`): the phase ships its program (`prog`: the definitions, oldest first)
-- and, for each element, its base command and its numbers as nodes over those definitions
-- (`SElem`).  The page evaluates the program once per time step, in order, and then the numbers.
--
-- The base command of a shared element has the numbers that a formula overwrites zeroed
-- (`shareElem`), so that elements that differ only in those numbers ship the same `<svg>` string,
-- once (`Slides.Backend.Diagram`).  That sharing means what the unshared phases mean, for every
-- reading of formulas, is `Slides.Anim.SharePhases.Properties`.

module Slides.Anim.SharePhases where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Slides.Diagram.Draw using (Draw)
open import Slides.Anim.Formula using (Formula)
open import Slides.Anim.Phases using (Elem; Kind; nums; withNums)
open import Slides.Anim.Share

------------------------------------------------------------------------
-- Shared elements and phases

-- an element as shipped: its base command, and its numbers as nodes over the phase's program
record SElem : Set where
  constructor selem
  field
    base   : Draw ℕ
    coords : Maybe (List (Maybe Node))
open SElem

-- a phase as shipped: the program (the definitions, oldest first) and the elements
record SBody : Set where
  constructor sbody
  field
    prog  : List Node
    elems : List SElem
open SBody

shareCoords : Maybe (List (Maybe Formula)) → Sh (Maybe (List (Maybe Node)))
shareCoords = traverseM (traverseL (traverseM output))

entriesS : Maybe (List (Maybe Node)) → List (Maybe Node)
entriesS nothing   = []
entriesS (just cs) = cs

-- The numbers of an element's base command that a formula overwrites are never read by the page
-- (`pageNumsS` takes the base number only where there is no formula): they are shipped as 0,
-- which makes the base commands of elements that differ only in those numbers equal, so that
-- the printer ships each of them once (`zeroBase-sem`).
zeroAt : List (Kind × ℕ) → List (Maybe Node) → List ℕ
zeroAt []             _              = []
zeroAt ((k , n) ∷ bs) []             = n ∷ zeroAt bs []
zeroAt ((k , n) ∷ bs) (nothing ∷ es) = n ∷ zeroAt bs es
zeroAt ((k , n) ∷ bs) (just _  ∷ es) = 0 ∷ zeroAt bs es

zeroBase : Draw ℕ → Maybe (List (Maybe Node)) → Draw ℕ
zeroBase d cs = withNums d (zeroAt (nums d) (entriesS cs)) 0

shareElem : Elem → Sh SElem
shareElem e st = wrap (shareCoords (Elem.coords e) st)
  where wrap : _ → _
        wrap r = selem (zeroBase (Elem.base e) (proj₁ r)) (proj₁ r) , proj₂ r

-- the elements of a phase, through one store
shareBody : List Elem → SBody
shareBody es = wrap (traverseL shareElem es emptySt)
  where wrap : _ → _
        wrap r = sbody (program (proj₂ r)) (proj₁ r)

-- the phases, with the tick each starts at
sharePhases : List (ℕ × List Elem) → List (ℕ × SBody)
sharePhases = map (λ p → proj₁ p , shareBody (proj₂ p))
