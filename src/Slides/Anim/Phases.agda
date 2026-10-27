{-# OPTIONS --safe --without-K #-}

-- What the backend ships for a parametric animation, as data.  `Slides.Backend.Diagram` only
-- prints this data as JSON; what it means is `Slides.Anim.Phases.Properties`.
--
-- The shipped structure (`data-param`, see `Slides.Backend.Diagram`) is a list of *phases*.  A
-- phase starts at a tick and has, for each drawing command of the layout, an `Elem`: the
-- command with its numbers taken at the all-zero assignment (`base`, shipped as an SVG
-- string: the page takes the numbers it does not override from it) and, for each of its
-- numbers in the page's attribute order, a formula or `null` (`coords`; `null` for all of them
-- when every number is a constant).  Ticks whose layouts ship the same elements share a phase.
--
-- Nothing here depends on how a formula is read, nor on the expression language of the symbolic
-- layout: a command whose numbers are `E` is shipped by saying which formula each number has
-- (`slot`) and what its base number is (`bval`) (`encodeWith`, `phasesWith`).  The instance is
-- `phasesOf` (templates, `OExpr ℕ`).

module Slides.Anim.Phases where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; head; drop)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Nat.Properties as ℕP
import Data.Maybe.Properties as MP
import Data.List.Properties as LP
open import Slides.Diagram.DrawEq using (drawEq?)

open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label; mapDraw; Layout)
open import Slides.Diagram.Ordered using (OExpr; evalO; natO; weakenQ)
open import Slides.Anim.Formula

------------------------------------------------------------------------
-- The numbers of a drawing command

data Kind : Set where
  pos size : Kind        -- a position (half units) or a size (units)

-- in the player's attribute order (`NUMS`)
nums : ∀ {S} → Draw S → List (Kind × S)
nums (rect x y w h _)  = (pos , x) ∷ (pos , y) ∷ (size , w) ∷ (size , h) ∷ []
nums (circle x y r _)  = (pos , x) ∷ (pos , y) ∷ (size , r) ∷ []
nums (line a b c d _)  = (pos , a) ∷ (pos , b) ∷ (pos , c) ∷ (pos , d) ∷ []
nums (arrow a b c d _) = (pos , a) ∷ (pos , b) ∷ (pos , c) ∷ (pos , d) ∷ []
nums (label x y _ _ _) = (pos , x) ∷ (pos , y) ∷ []

private
  at : ∀ {T : Set} → List T → T → ℕ → T
  at ts d k = fromMaybe d (head (drop k ts))

-- the same command with its numbers (in order) from a list; `dflt` when it runs out
withNums : ∀ {S T : Set} → Draw S → List T → T → Draw T
withNums (rect _ _ _ _ s)  ts d = rect (at ts d 0) (at ts d 1) (at ts d 2) (at ts d 3) s
withNums (circle _ _ _ s)  ts d = circle (at ts d 0) (at ts d 1) (at ts d 2) s
withNums (line _ _ _ _ s)  ts d = line (at ts d 0) (at ts d 1) (at ts d 2) (at ts d 3) s
withNums (arrow _ _ _ _ s) ts d = arrow (at ts d 0) (at ts d 1) (at ts d 2) (at ts d 3) s
withNums (label _ _ n t s) ts d = label (at ts d 0) (at ts d 1) n t s

------------------------------------------------------------------------
-- One drawing command, as shipped

-- the base command (its numbers at the all-zero assignment) and the formulas of its numbers;
-- `coords = nothing` when every number is constant, else an entry for each number, `nothing`
-- for a constant
record Elem : Set where
  constructor elem
  field
    base   : Draw ℕ
    coords : Maybe (List (Maybe Formula))
open Elem

-- the formula of a number: positions are halved
slotF : Kind × OExpr ℕ → Formula
slotF (pos  , e) = half (enc (weakenQ e))
slotF (size , e) = enc (weakenQ e)

entry : Formula → Maybe Formula
entry (num _) = nothing
entry f       = just f

allNum : List Formula → Bool
allNum []       = true
allNum (f ∷ fs) = if isNum f then allNum fs else false

coordsOf : List Formula → Maybe (List (Maybe Formula))
coordsOf fs = if allNum fs then nothing else just (map entry fs)

-- the shipped element of a command whose numbers are `E`: `slot` is the formula of a number, `bval`
-- its base number
encodeWith : ∀ {E : Set} → (Kind × E → Formula) → (E → ℕ) → Draw E → Elem
encodeWith slot bval dr = elem (mapDraw bval dr) (coordsOf (map slot (nums dr)))

entries : Maybe (List (Maybe Formula)) → List (Maybe Formula)
entries nothing   = []
entries (just cs) = cs

------------------------------------------------------------------------
-- Equality of what is shipped

elemEq? : DecidableEquality Elem
elemEq? (elem b₁ c₁) (elem b₂ c₂) with drawEq? ℕP._≟_ b₁ b₂ | MP.≡-dec (LP.≡-dec (MP.≡-dec formulaEq?)) c₁ c₂
... | yes refl | yes refl = yes refl
... | no ¬p   | _        = no λ { refl → ¬p refl }
... | _       | no ¬q    = no λ { refl → ¬q refl }

elemsEq? : DecidableEquality (List Elem)
elemsEq? = LP.≡-dec elemEq?

------------------------------------------------------------------------
-- Grouping ticks into phases

-- `runs prev k xs`: the entries of `xs`, which start at tick `k`, that differ from the one
-- emitted before them (`prev`), with the tick they are at
module _ {A : Set} (_≟_ : DecidableEquality A) where

  runs : Maybe A → ℕ → List A → List (ℕ × A)
  runs prev k []       = []
  runs prev k (a ∷ as) with prev
  ... | nothing = (k , a) ∷ runs (just a) (suc k) as
  ... | just p  = if ⌊ a ≟ p ⌋ then runs prev (suc k) as else (k , a) ∷ runs (just a) (suc k) as

------------------------------------------------------------------------
-- The shipped phases of a list of symbolic layouts

tickElemsWith : ∀ {E : Set} → (Kind × E → Formula) → (E → ℕ) → Layout E → List Elem
tickElemsWith slot bval l = map (encodeWith slot bval) (Layout.draws l)

-- the phases of the symbolic frames, one layout per tick
phasesWith : ∀ {E : Set} → (Kind × E → Formula) → (E → ℕ) → List (Layout E) → List (ℕ × List Elem)
phasesWith slot bval ls = runs elemsEq? nothing 0 (map (tickElemsWith slot bval) ls)

phasesOf : List (Layout (OExpr ℕ)) → List (ℕ × List Elem)
phasesOf = phasesWith slotF (evalO natO (λ _ → 0))
