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

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeP
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as ProdP
open import Data.String using (String)
import Data.String.Properties as StrP
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Slides.Diagram

------------------------------------------------------------------------
-- Decidable equality of elements

-- a style is the tuple of its fields
styleT : Style → Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe ℕ × Maybe String
styleT s = Style.stroke s , Style.fill s , Style.strokeWidth s , Style.cls s , Style.ident s
         , Style.rx s , Style.dash s , Style.opacity s , Style.anchor s

private
  _≟ˢ_ = MaybeP.≡-dec StrP._≟_
  _≟ⁿ_ = MaybeP.≡-dec ℕP._≟_
  _≟₁_ = ℕP._≟_
  _≟₃_ = ProdP.≡-dec _≟₁_ (ProdP.≡-dec _≟₁_ _≟₁_)
  _≟₄_ = ProdP.≡-dec _≟₁_ (ProdP.≡-dec _≟₁_ (ProdP.≡-dec _≟₁_ _≟₁_))
  _≟₉_ = ProdP.≡-dec _≟ˢ_ (ProdP.≡-dec _≟ˢ_ (ProdP.≡-dec _≟ⁿ_ (ProdP.≡-dec _≟ˢ_ (ProdP.≡-dec _≟ˢ_
           (ProdP.≡-dec _≟ⁿ_ (ProdP.≡-dec _≟ˢ_ (ProdP.≡-dec _≟ⁿ_ _≟ˢ_)))))))

_≟ₛ_ : (s t : Style) → Dec (s ≡ t)
s ≟ₛ t with styleT s ≟₉ styleT t
... | yes eq = yes (back eq)
  where back : styleT s ≡ styleT t → s ≡ t
        back refl = refl
... | no ¬eq = no (λ { refl → ¬eq refl })

private
  _≟ₚ₄_ = ProdP.≡-dec _≟₄_ _≟ₛ_
  _≟ₚ₃_ = ProdP.≡-dec _≟₃_ _≟ₛ_
  _≟ₜ_  = ProdP.≡-dec _≟₃_ StrP._≟_

mutual
  _≟ₑ_ : (a b : Element) → Dec (a ≡ b)
  rect x y w h s ≟ₑ rect x′ y′ w′ h′ s′ with ((x , y , w , h) , s) ≟ₚ₄ ((x′ , y′ , w′ , h′) , s′)
  ... | yes refl = yes refl
  ... | no ¬eq   = no (λ { refl → ¬eq refl })
  circle x y r s ≟ₑ circle x′ y′ r′ s′ with ((x , y , r) , s) ≟ₚ₃ ((x′ , y′ , r′) , s′)
  ... | yes refl = yes refl
  ... | no ¬eq   = no (λ { refl → ¬eq refl })
  line a b c d s ≟ₑ line a′ b′ c′ d′ s′ with ((a , b , c , d) , s) ≟ₚ₄ ((a′ , b′ , c′ , d′) , s′)
  ... | yes refl = yes refl
  ... | no ¬eq   = no (λ { refl → ¬eq refl })
  arrow a b c d s ≟ₑ arrow a′ b′ c′ d′ s′ with ((a , b , c , d) , s) ≟ₚ₄ ((a′ , b′ , c′ , d′) , s′)
  ... | yes refl = yes refl
  ... | no ¬eq   = no (λ { refl → ¬eq refl })
  label x y z t s ≟ₑ label x′ y′ z′ t′ s′ with ((x , y , z) , t) ≟ₜ ((x′ , y′ , z′) , t′) | s ≟ₛ s′
  ... | yes refl | yes refl = yes refl
  ... | no ¬eq   | _        = no (λ { refl → ¬eq refl })
  ... | _        | no ¬eq   = no (λ { refl → ¬eq refl })
  group xs ≟ₑ group ys with xs ≟ₗ ys
  ... | yes refl = yes refl
  ... | no ¬eq   = no (λ { refl → ¬eq refl })
  path d s ≟ₑ path d′ s′ with d StrP.≟ d′ | s ≟ₛ s′
  ... | yes refl | yes refl = yes refl
  ... | no ¬eq   | _        = no (λ { refl → ¬eq refl })
  ... | _        | no ¬eq   = no (λ { refl → ¬eq refl })
  rect _ _ _ _ _ ≟ₑ circle _ _ _ _ = no (λ ())
  rect _ _ _ _ _ ≟ₑ line _ _ _ _ _ = no (λ ())
  rect _ _ _ _ _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  rect _ _ _ _ _ ≟ₑ label _ _ _ _ _ = no (λ ())
  rect _ _ _ _ _ ≟ₑ group _ = no (λ ())
  rect _ _ _ _ _ ≟ₑ path _ _ = no (λ ())
  circle _ _ _ _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  circle _ _ _ _ ≟ₑ line _ _ _ _ _ = no (λ ())
  circle _ _ _ _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  circle _ _ _ _ ≟ₑ label _ _ _ _ _ = no (λ ())
  circle _ _ _ _ ≟ₑ group _ = no (λ ())
  circle _ _ _ _ ≟ₑ path _ _ = no (λ ())
  line _ _ _ _ _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  line _ _ _ _ _ ≟ₑ circle _ _ _ _ = no (λ ())
  line _ _ _ _ _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  line _ _ _ _ _ ≟ₑ label _ _ _ _ _ = no (λ ())
  line _ _ _ _ _ ≟ₑ group _ = no (λ ())
  line _ _ _ _ _ ≟ₑ path _ _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ circle _ _ _ _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ line _ _ _ _ _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ label _ _ _ _ _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ group _ = no (λ ())
  arrow _ _ _ _ _ ≟ₑ path _ _ = no (λ ())
  label _ _ _ _ _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  label _ _ _ _ _ ≟ₑ circle _ _ _ _ = no (λ ())
  label _ _ _ _ _ ≟ₑ line _ _ _ _ _ = no (λ ())
  label _ _ _ _ _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  label _ _ _ _ _ ≟ₑ group _ = no (λ ())
  label _ _ _ _ _ ≟ₑ path _ _ = no (λ ())
  group _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  group _ ≟ₑ circle _ _ _ _ = no (λ ())
  group _ ≟ₑ line _ _ _ _ _ = no (λ ())
  group _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  group _ ≟ₑ label _ _ _ _ _ = no (λ ())
  group _ ≟ₑ path _ _ = no (λ ())
  path _ _ ≟ₑ rect _ _ _ _ _ = no (λ ())
  path _ _ ≟ₑ circle _ _ _ _ = no (λ ())
  path _ _ ≟ₑ line _ _ _ _ _ = no (λ ())
  path _ _ ≟ₑ arrow _ _ _ _ _ = no (λ ())
  path _ _ ≟ₑ label _ _ _ _ _ = no (λ ())
  path _ _ ≟ₑ group _ = no (λ ())

  _≟ₗ_ : (xs ys : List Element) → Dec (xs ≡ ys)
  []       ≟ₗ []       = yes refl
  []       ≟ₗ (_ ∷ _)  = no (λ ())
  (_ ∷ _)  ≟ₗ []       = no (λ ())
  (x ∷ xs) ≟ₗ (y ∷ ys) with x ≟ₑ y | xs ≟ₗ ys
  ... | yes refl | yes refl = yes refl
  ... | no ¬eq   | _        = no (λ { refl → ¬eq refl })
  ... | _        | no ¬eq   = no (λ { refl → ¬eq refl })

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

-- put numbers back (missing ones leave the old value)
setNums : List ℕ → Element → Element
setNums (x ∷ y ∷ w ∷ h ∷ _) (rect _ _ _ _ s)   = rect x y w h s
setNums (x ∷ y ∷ r ∷ _)     (circle _ _ _ s)   = circle x y r s
setNums (a ∷ b ∷ c ∷ d ∷ _) (line _ _ _ _ s)   = line a b c d s
setNums (a ∷ b ∷ c ∷ d ∷ _) (arrow _ _ _ _ s)  = arrow a b c d s
setNums (x ∷ y ∷ _)         (label _ _ z t s)  = label x y z t s
setNums _                   e                  = e

mutual
  -- how to turn one element into another
  data Edit : Set where
    same : Edit
    nums : List ℕ → Edit      -- the same element with these numbers (`numsOf`)
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
... | no _ with setNums (numsOf b) a ≟ₑ b
...   | yes _ = nums (numsOf b)
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
... | no _ with setNums (numsOf b) a ≟ₑ b
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
