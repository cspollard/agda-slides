{-# OPTIONS --safe --without-K #-}

-- Differences between diagrams.
--
-- The frames of an animation share almost all their structure: a moving dot
-- changes two numbers.  `diffL old new` is the edit that turns the elements `old`
-- into `new`, and `patchL` applies it, with the round trip
--
--     patchL (diffL old new) old ≡ new
--
-- so an animation can be shipped as its first frame and an edit per later frame
-- (`deltas`, `replay`) rather than as every frame.  An element is edited at the
-- finest grain that is exact: not at all (`same`), only its numbers (`nums`: the
-- coordinates and sizes), wholesale (`new`), or, for a group, member by member.
-- Lists are edited position by position; the elements that remain once the shorter
-- list has run out are replaced as a whole (`done`).  The round trip needs no theory of
-- the elements beyond decidable equality: `diffE` only claims an edit when
-- re-applying it gives the new element back, which it checks.

module Slides.Diagram.Delta where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using ()
import Data.Maybe.Properties as MaybeP
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕP
import Data.Integer as ℤ
import Data.Integer.Properties as ℤP
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as ProdP
open import Data.String using (String)
import Data.String.Properties as StrP
import Data.Sum.Properties as SP
import Data.Unit.Properties as UP
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram
import Slides.Diagram.Draw as Dr
open import Slides.Diagram.DrawEq using (drawEq?; styleEq?)
open import Slides.DecEq

------------------------------------------------------------------------
-- Decidable equality of elements

-- An element is a rose tree (`Slides.DecEq`): the drawing commands (the same arguments as
-- `Slides.Diagram.Draw.Draw ℕ`, equal by `drawEq?`) and a path are leaves, a group has its
-- members as subtrees.  No clause for a pair of different constructors.
private
  Tok : Set
  Tok = Dr.Draw ℕ ⊎ ⊤ ⊎ (String × Style)

  mutual
    to : Element → Rose Tok
    to (rect x y w h s)  = node (inj₁ (Dr.rect x y w h s)) []
    to (circle x y r s)  = node (inj₁ (Dr.circle x y r s)) []
    to (line a b c d s)  = node (inj₁ (Dr.line a b c d s)) []
    to (arrow a b c d s) = node (inj₁ (Dr.arrow a b c d s)) []
    to (label x y n t s) = node (inj₁ (Dr.label x y n t s)) []
    to (group xs)        = node (inj₂ (inj₁ tt)) (toL xs)
    to (path d s)        = node (inj₂ (inj₂ (d , s))) []

    toL : List Element → List (Rose Tok)
    toL []       = []
    toL (x ∷ xs) = to x ∷ toL xs

  mutual
    from : Rose Tok → Element
    from (node (inj₁ (Dr.rect x y w h s))  _)  = rect x y w h s
    from (node (inj₁ (Dr.circle x y r s))  _)  = circle x y r s
    from (node (inj₁ (Dr.line a b c d s))  _)  = line a b c d s
    from (node (inj₁ (Dr.arrow a b c d s)) _)  = arrow a b c d s
    from (node (inj₁ (Dr.label x y n t s)) _)  = label x y n t s
    from (node (inj₂ (inj₁ _))             cs) = group (fromL cs)
    from (node (inj₂ (inj₂ (d , s)))       _)  = path d s

    fromL : List (Rose Tok) → List Element
    fromL []       = []
    fromL (c ∷ cs) = from c ∷ fromL cs

  mutual
    from-to : ∀ e → from (to e) ≡ e
    from-to (rect _ _ _ _ _)  = refl
    from-to (circle _ _ _ _)  = refl
    from-to (line _ _ _ _ _)  = refl
    from-to (arrow _ _ _ _ _) = refl
    from-to (label _ _ _ _ _) = refl
    from-to (group xs)        = cong group (fromL-toL xs)
    from-to (path _ _)        = refl

    fromL-toL : ∀ xs → fromL (toL xs) ≡ xs
    fromL-toL []       = refl
    fromL-toL (x ∷ xs) = cong₂ _∷_ (from-to x) (fromL-toL xs)

_≟ₑ_ : (a b : Element) → Dec (a ≡ b)
_≟ₑ_ = retract-dec to from from-to
  (roseEq? (SP.≡-dec (drawEq? ℕP._≟_) (SP.≡-dec UP._≟_ (ProdP.≡-dec StrP._≟_ styleEq?))))

------------------------------------------------------------------------
-- Edits

-- the numbers of an element that an animation changes: coordinates and sizes
-- (a label's font size is left alone: its sub- and superscripts depend on it)
numsOf : Element → List ℕ
numsOf (rect x y w h _)   = x ∷ y ∷ w ∷ h ∷ []
numsOf (circle x y r _)   = x ∷ y ∷ r ∷ []
numsOf (line a b c d _)   = a ∷ b ∷ c ∷ d ∷ []
numsOf (arrow a b c d _)  = a ∷ b ∷ c ∷ d ∷ []
numsOf (label x y _ _ _)  = x ∷ y ∷ []
numsOf (group _)          = []
numsOf (path v1 v2)         = []

-- put numbers back
setAll : List ℕ → Element → Element
setAll (x ∷ y ∷ w ∷ h ∷ _) (rect _ _ _ _ s)   = rect x y w h s
setAll (x ∷ y ∷ r ∷ _)     (circle _ _ _ s)   = circle x y r s
setAll (a ∷ b ∷ c ∷ d ∷ _) (line _ _ _ _ s)   = line a b c d s
setAll (a ∷ b ∷ c ∷ d ∷ _) (arrow _ _ _ _ s)  = arrow a b c d s
setAll (x ∷ y ∷ _)         (label _ _ z t s)  = label x y z t s
setAll _                   e                  = e

-- Numbers are edited by differences from the old ones (a moving dot changes its
-- coordinates by a few units): the first differences only, the rest are zero.
addNums : List ℤ → List ℕ → List ℕ
addNums []       ns       = ns
addNums (_ ∷ _)  []       = []
addNums (d ∷ ds) (n ∷ ns) = ℤ.∣ (ℤ.+ n) ℤ.+ d ∣ ∷ addNums ds ns

setNums : List ℤ → Element → Element
setNums ds e = setAll (addNums ds (numsOf e)) e

-- the differences from the old numbers to the new, without the trailing zeros
trimNums : List ℕ → List ℕ → List ℤ
trimNums (a ∷ as) (b ∷ bs) with trimNums as bs | (ℤ.+ b) ℤ.- (ℤ.+ a) ℤP.≟ ℤ.0ℤ
... | [] | yes _ = []
... | r  | _     = ((ℤ.+ b) ℤ.- (ℤ.+ a)) ∷ r
trimNums _ _ = []

mutual
  -- how to turn one element into another
  data Edit : Set where
    same : Edit
    nums : List ℤ → Edit      -- the same element, its numbers (`numsOf`) shifted by these
    new  : Element → Edit
    grp  : Edits → Edit       -- a group whose members are edited

  -- how to turn a list of elements into another, position by position
  data Edits : Set where
    done : List Element → Edits   -- replace whatever remains of the old list by these
    _∷_  : Edit → Edits → Edits

infixr 5 _∷_

-- the edit between two elements that are not both groups
diffN : Element → Element → Edit
diffN a b with a ≟ₑ b
... | yes _ = same
... | no _ with setNums (trimNums (numsOf a) (numsOf b)) a ≟ₑ b
...   | yes _ = nums (trimNums (numsOf a) (numsOf b))
...   | no _  = new b

mutual
  diffE : Element → Element → Edit
  diffE (group xs) b = diffG xs b
  diffE (rect v1 v2 v3 v4 v5) b = diffN (rect v1 v2 v3 v4 v5) b
  diffE (circle v1 v2 v3 v4) b = diffN (circle v1 v2 v3 v4) b
  diffE (line v1 v2 v3 v4 v5) b = diffN (line v1 v2 v3 v4 v5) b
  diffE (arrow v1 v2 v3 v4 v5) b = diffN (arrow v1 v2 v3 v4 v5) b
  diffE (label v1 v2 v3 v4 v5) b = diffN (label v1 v2 v3 v4 v5) b
  diffE (path v1 v2) b = diffN (path v1 v2) b

  -- `group xs` against something
  diffG : List Element → Element → Edit
  diffG xs (group ys) = grp (diffL xs ys)
  diffG xs (rect v1 v2 v3 v4 v5) = diffN (group xs) (rect v1 v2 v3 v4 v5)
  diffG xs (circle v1 v2 v3 v4) = diffN (group xs) (circle v1 v2 v3 v4)
  diffG xs (line v1 v2 v3 v4 v5) = diffN (group xs) (line v1 v2 v3 v4 v5)
  diffG xs (arrow v1 v2 v3 v4 v5) = diffN (group xs) (arrow v1 v2 v3 v4 v5)
  diffG xs (label v1 v2 v3 v4 v5) = diffN (group xs) (label v1 v2 v3 v4 v5)
  diffG xs (path v1 v2) = diffN (group xs) (path v1 v2)

  diffL : List Element → List Element → Edits
  diffL (x ∷ xs) (y ∷ ys) = diffE x y ∷ diffL xs ys
  diffL _        ys       = done ys

mutual
  patchE : Edit → Element → Element
  patchE same        a           = a
  patchE (nums ns)   a           = setNums ns a
  patchE (new b)     _           = b
  patchE (grp es)    (group xs)  = group (patchL es xs)
  patchE (grp es)    a           = a

  patchL : Edits → List Element → List Element
  patchL (done ys) _        = ys
  patchL (e ∷ es)  (x ∷ xs) = patchE e x ∷ patchL es xs
  patchL (_ ∷ _)   []       = []

------------------------------------------------------------------------
-- The round trip

patchE-diffN : ∀ a b → patchE (diffN a b) a ≡ b
patchE-diffN a b with a ≟ₑ b
... | yes eq = eq
... | no _ with setNums (trimNums (numsOf a) (numsOf b)) a ≟ₑ b
...   | yes eq = eq
...   | no _   = refl

mutual
  patchE-diffE : ∀ a b → patchE (diffE a b) a ≡ b
  patchE-diffE (group xs) b = patchE-diffG xs b
  patchE-diffE (rect v1 v2 v3 v4 v5) b = patchE-diffN (rect v1 v2 v3 v4 v5) b
  patchE-diffE (circle v1 v2 v3 v4) b = patchE-diffN (circle v1 v2 v3 v4) b
  patchE-diffE (line v1 v2 v3 v4 v5) b = patchE-diffN (line v1 v2 v3 v4 v5) b
  patchE-diffE (arrow v1 v2 v3 v4 v5) b = patchE-diffN (arrow v1 v2 v3 v4 v5) b
  patchE-diffE (label v1 v2 v3 v4 v5) b = patchE-diffN (label v1 v2 v3 v4 v5) b
  patchE-diffE (path v1 v2) b = patchE-diffN (path v1 v2) b

  patchE-diffG : ∀ xs b → patchE (diffG xs b) (group xs) ≡ b
  patchE-diffG xs (group ys) = cong group (patchL-diffL xs ys)
  patchE-diffG xs (rect v1 v2 v3 v4 v5) = patchE-diffN (group xs) (rect v1 v2 v3 v4 v5)
  patchE-diffG xs (circle v1 v2 v3 v4) = patchE-diffN (group xs) (circle v1 v2 v3 v4)
  patchE-diffG xs (line v1 v2 v3 v4 v5) = patchE-diffN (group xs) (line v1 v2 v3 v4 v5)
  patchE-diffG xs (arrow v1 v2 v3 v4 v5) = patchE-diffN (group xs) (arrow v1 v2 v3 v4 v5)
  patchE-diffG xs (label v1 v2 v3 v4 v5) = patchE-diffN (group xs) (label v1 v2 v3 v4 v5)
  patchE-diffG xs (path v1 v2) = patchE-diffN (group xs) (path v1 v2)

  patchL-diffL : ∀ xs ys → patchL (diffL xs ys) xs ≡ ys
  patchL-diffL (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (patchE-diffE x y) (patchL-diffL xs ys)
  patchL-diffL (x ∷ xs) []       = refl
  patchL-diffL []       ys       = refl

------------------------------------------------------------------------
-- A sequence of frames: the first and an edit from each frame to the next

deltas : List Element → List (List Element) → List Edits
deltas e []       = []
deltas e (f ∷ fs) = diffL e f ∷ deltas f fs

replay : List Element → List Edits → List (List Element)
replay e []       = []
replay e (d ∷ ds) = patchL d e ∷ replay (patchL d e) ds

-- shipping the first frame and `deltas` loses nothing
replay-deltas : ∀ e fs → replay e (deltas e fs) ≡ fs
replay-deltas e []       = refl
replay-deltas e (f ∷ fs) rewrite patchL-diffL e f = cong (f ∷_) (replay-deltas f fs)
