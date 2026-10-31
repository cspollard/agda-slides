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
-- Sizes are in units, positions (`left`, `top`, every drawing coordinate) in half units, so
-- centring is a difference of sizes with no division; a printer halves them (`Print`).  It is
-- plain data over `S`, so a change of scalar is a map (`mapLayout`).

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

record Layout (S : Set) : Set where
  constructor mkLayout
  field
    width height : S
    draws        : List (Draw S)
    anchors      : List (String × Box S)

-- Change of scalar

mapBox : ∀ {S T} → (S → T) → Box S → Box T
mapBox f (box l t w h) = box (f l) (f t) (f w) (f h)

-- a map of scalars acts on both coordinates of a point
mapPt : ∀ {S T : Set} → (S → T) → S × S → T × T
mapPt f p = f (proj₁ p) , f (proj₂ p)

-- the one traversal of a drawing's scalars: `px`, `py` on the positions (x and y), `pd` on the
-- dimensions (sizes and radii).  A change of scalar is `mapXY f f f`; moving is `mapXY (_+ dx) (_+ dy) id`.
mapXY : ∀ {S T} → (S → T) → (S → T) → (S → T) → Draw S → Draw T
mapXY px py pd (rect x y w h s)   = rect (px x) (py y) (pd w) (pd h) s
mapXY px py pd (circle x y r s)   = circle (px x) (py y) (pd r) s
mapXY px py pd (ellipse x y a b s) = ellipse (px x) (py y) (pd a) (pd b) s
mapXY px py pd (poly c ps s)      = poly c (map (λ p → px (proj₁ p) , py (proj₂ p)) ps) s
mapXY px py pd (line a b c d s)   = line (px a) (py b) (px c) (py d) s
mapXY px py pd (arrow a b c d s)  = arrow (px a) (py b) (px c) (py d) s
mapXY px py pd (label x y n t s)  = label (px x) (py y) n t s
mapXY px py pd (path x y d s)     = path (px x) (py y) d s

mapDraw : ∀ {S T} → (S → T) → Draw S → Draw T
mapDraw f = mapXY f f f

mapAnchor : ∀ {S T} → (S → T) → String × Box S → String × Box T
mapAnchor f (n , b) = n , mapBox f b

mapLayout : ∀ {S T} → (S → T) → Layout S → Layout T
mapLayout f (mkLayout w h ds as) = mkLayout (f w) (f h) (map (mapDraw f) ds) (map (mapAnchor f) as)
