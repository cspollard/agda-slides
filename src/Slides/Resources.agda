{-# OPTIONS --safe --without-K #-}

-- Resources a deck refers to, checked when the deck is typechecked.
--
-- A deck declares its `Resources`: the figure files it may include and its
-- bibliography.  `Checked R` then provides `figure` and `cite`, which take an
-- instance argument that the name is declared.  The argument has type `⊤` when
-- the name is in `R` (found by instance search, using `tt`, which
-- `Slides.DSL` re-exports) and the empty type `Missing kind name` when it is
-- not, so a typo is a type error that names the missing resource:
--
--   No instance of type
--   Found (figureDeclared "plto.png") "figure" "plto.png" was found in scope.
--
-- (Evaluating the `Found` shows `Missing "figure" "plto.png"`.)
--
-- Agda cannot look at the file system, so that the declared figures exist on
-- disk is checked separately (`make check-resources`).

module Slides.Resources where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; map)
open import Data.Product using (_×_; proj₁)
open import Data.String using (String; _==_)
open import Data.Unit using (⊤)

open import Slides.Core using (Text; Inline; Body; Content; K)
import Slides.Core as Core
open import Slides.DSL using (liftContent)
import Slides.DSL as DSL

record Resources : Set where
  field
    -- paths of the image files the deck may include
    figures    : List String
    -- bibliography: key and entry text
    references : List (String × Text)

open Resources public

-- No resource of this kind has this name.
data Missing (kind name : String) : Set where

Found : Bool → (kind name : String) → Set
Found true  _    _    = ⊤
Found false kind name = Missing kind name

private
  member : String → List String → Bool
  member x xs = any (x ==_) xs

module Checked (R : Resources) where

  figureDeclared : String → Bool
  figureDeclared src = member src (figures R)

  referenceDeclared : String → Bool
  referenceDeclared key = member key (map proj₁ (references R))

  module Content where
    figure : (src : String) {{ok : Found (figureDeclared src) "figure" src}} →
             Text → Core.Content
    figure src c = DSL.Content.figureUnchecked src c

    bibliography : Core.Content
    bibliography = DSL.Content.references (references R)

  figure : (src : String) {{ok : Found (figureDeclared src) "figure" src}} →
           Text → Body K
  figure src {{ok}} c = liftContent (Content.figure src {{ok}} c)

  bibliography : Body K
  bibliography = liftContent Content.bibliography

  cite : (key : String) {{ok : Found (referenceDeclared key) "reference" key}} → Inline
  cite key = Core.cite key
