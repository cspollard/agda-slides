{-# OPTIONS --safe --without-K #-}

-- Layout: the carrier of the placement fold, and the one drawing vocabulary.
--
-- A `Layout S` is a frame (`width` x `height`, the only thing a neighbour sees), what is drawn
-- in it, and the boxes that were given a name:
--
--   (0,0)+---------------+     drawn relative to the frame's top-left corner, in list order
--        | draws         |     (later is on top); the drawings may stick out of the frame
--        |   [name]      |     and are not counted in it; anchors are named sub-boxes
--        +---------------+
--
-- Half units: sizes (`width`, `height`, `w`, `h`, a radius) are in units, but positions (a
-- box's `left` and `top`, every coordinate of a drawing) are in half units, so centring is the
-- difference of two sizes with no division.  A printer halves them (`Slides.Diagram.Print`).
-- Everything is plain data over `S`, so a change of scalar is a map (`mapLayout`).

module Slides.Diagram.Draw where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)

open import Slides.Diagram.Style using (Style)
open import Slides.Text using (Inline)

record Box (S : Set) : Set where
  constructor box
  field left top width height : S

data Draw (S : Set) : Set where
  rect   : (x y w h : S) → Style → Draw S
  circle : (cx cy r : S) → Style → Draw S              -- by its centre
  ellipse : (cx cy rx ry : S) → Style → Draw S         -- by its centre
  poly   : (closed : Bool) → List (S × S) → Style → Draw S   -- absolute points; closed is a polygon
  line   : (x₁ y₁ x₂ y₂ : S) → Style → Draw S
  arrow  : (x₁ y₁ x₂ y₂ : S) → Style → Draw S          -- the head is at the second point
  label  : (x y : S) (size : ℕ) → List Inline → Style → Draw S   -- centred at a point
  path   : (x y : S) → String → Style → Draw S         -- `d` as in SVG, drawn from (x, y)
  group  : (x y : S) → List (Draw S) → Draw S          -- members drawn relative to (x, y)

record Layout (S : Set) : Set where
  constructor mkLayout
  field
    width height : S
    draws        : List (Draw S)
    anchors      : List (String × Box S)

------------------------------------------------------------------------
-- Change of scalar

mapBox : ∀ {S T} → (S → T) → Box S → Box T
mapBox f (box l t w h) = box (f l) (f t) (f w) (f h)

-- a map of scalars acts on both coordinates of a point
mapPt : ∀ {S T : Set} → (S → T) → S × S → T × T
mapPt f p = f (proj₁ p) , f (proj₂ p)

mutual
  mapDraw : ∀ {S T} → (S → T) → Draw S → Draw T
  mapDraw f (rect x y w h s)   = rect (f x) (f y) (f w) (f h) s
  mapDraw f (circle x y r s)   = circle (f x) (f y) (f r) s
  mapDraw f (ellipse x y a b s) = ellipse (f x) (f y) (f a) (f b) s
  mapDraw f (poly c ps s)      = poly c (map (mapPt f) ps) s
  mapDraw f (line a b c d s)   = line (f a) (f b) (f c) (f d) s
  mapDraw f (arrow a b c d s)  = arrow (f a) (f b) (f c) (f d) s
  mapDraw f (label x y n t s)  = label (f x) (f y) n t s
  mapDraw f (path x y d s)     = path (f x) (f y) d s
  mapDraw f (group x y ds)     = group (f x) (f y) (mapDraws f ds)

  mapDraws : ∀ {S T} → (S → T) → List (Draw S) → List (Draw T)
  mapDraws f []       = []
  mapDraws f (d ∷ ds) = mapDraw f d ∷ mapDraws f ds
  
mapAnchor : ∀ {S T} → (S → T) → String × Box S → String × Box T
mapAnchor f (n , b) = n , mapBox f b

mapLayout : ∀ {S T} → (S → T) → Layout S → Layout T
mapLayout f (mkLayout w h ds as) = mkLayout (f w) (f h) (mapDraws f ds) (map (mapAnchor f) as)
