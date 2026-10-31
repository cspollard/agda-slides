{-# OPTIONS --safe --without-K #-}

-- The placement operations: what each node does to the layouts of its children, over any `Space`
-- (`Layout` assembles them into the algebra of the signature, `Laws` states their laws).
--
-- Combining layouts shifts the drawings and anchors of each part into a new frame.  The binary
-- connectives take a frame just large enough for both children, so offsets are never negative
-- (`-` is applied only to a larger minuend); `place` and `overlay` are given the frame and do
-- not grow it.  A child of size `inner` in a frame of size `outer` sits at `outer - inner` half
-- units, i.e. half the extra room, which gives the three alignments:
--
--     top:  0              middle:  outer - inner         bottom:  2 (outer - inner)
--     +--------+           +--------+                     +--------+
--     | inner  |           |        |                     |        |
--     +--------+           | inner  |                     |        |
--     |        |           +--------+                     +--------+
--     +--------+           +--------+                     | inner  |
--                                                         +--------+

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Place {S : Set} (Sp : Space S) where

open import Data.Bool using (if_then_else_)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map; _++_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram.Style using (Style)
open import Slides.Text using (Inline)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open Space Sp

dbl : S → S
dbl x = x + x

-- Shifting and framing

shiftPt : S → S → S × S → S × S
shiftPt dx dy p = proj₁ p + dx , proj₂ p + dy

shiftDraw : S → S → Draw S → Draw S
shiftDraw dx dy (rect x y w h s)   = rect (x + dx) (y + dy) w h s
shiftDraw dx dy (circle x y r s)   = circle (x + dx) (y + dy) r s
shiftDraw dx dy (ellipse x y a b s) = ellipse (x + dx) (y + dy) a b s
shiftDraw dx dy (poly c ps s)     = poly c (map (shiftPt dx dy) ps) s
shiftDraw dx dy (line a b c d s)   = line (a + dx) (b + dy) (c + dx) (d + dy) s
shiftDraw dx dy (arrow a b c d s)  = arrow (a + dx) (b + dy) (c + dx) (d + dy) s
shiftDraw dx dy (label x y n t s)  = label (x + dx) (y + dy) n t s
shiftDraw dx dy (path x y d s)     = path (x + dx) (y + dy) d s

shiftBox : S → S → Box S → Box S
shiftBox dx dy (box l t w h) = box (l + dx) (t + dy) w h

shiftAnchor : S → S → String × Box S → String × Box S
shiftAnchor dx dy (n , b) = n , shiftBox dx dy b

-- the layout moved by (dx, dy) (half units) into a frame of the given size; the frame is
-- declared, not computed, so a layout that does not fit sticks out
inFrame : S → S → S → S → Layout S → Layout S
inFrame w h dx dy (mkLayout _ _ ds as) = mkLayout w h (map (shiftDraw dx dy) ds) (map (shiftAnchor dx dy) as)

-- the same frame, moved content
shift : S → S → Layout S → Layout S
shift dx dy l@(mkLayout w h _ _) = inFrame w h dx dy l

-- at the absolute position (x, y) (units) of a frame of the given size; nothing is centred
place : S → S → S → S → Layout S → Layout S
place w h x y = inFrame w h (dbl x) (dbl y)

-- two layouts in one frame, neither moved, the second drawn over the first
overlay : S → S → Layout S → Layout S → Layout S
overlay w h (mkLayout _ _ d₁ a₁) (mkLayout _ _ d₂ a₂) = mkLayout w h (d₁ ++ d₂) (a₁ ++ a₂)

width height : Layout S → S
width  = Layout.width
height = Layout.height

-- Primitives

spacer : S → S → Layout S
spacer w h = mkLayout w h [] []

rectangle : S → S → Style → Layout S
rectangle w h s = mkLayout w h (rect 0# 0# w h s ∷ []) []

disc : S → Style → Layout S
disc r s = mkLayout (dbl r) (dbl r) (circle (dbl r) (dbl r) r s ∷ []) []

ellipseL : S → S → Style → Layout S
ellipseL a b s = mkLayout (dbl a) (dbl b) (ellipse (dbl a) (dbl b) a b s ∷ []) []

-- the extent of a list of coordinates from the origin: the empty list reaches nothing
extent : List S → S
extent = foldr _⊔_ 0#

dblPt : S × S → S × S
dblPt p = dbl (proj₁ p) , dbl (proj₂ p)

-- through the points (units, from the top-left), in the frame that reaches the largest x and y
polyline : Bool → List (S × S) → Style → Layout S
polyline c ps s =
  mkLayout (extent (map proj₁ ps)) (extent (map proj₂ ps)) (poly c (map dblPt ps) s ∷ []) []

-- from the top-left to the bottom-right corner
segment : S → S → Style → Layout S
segment w h s = mkLayout w h (line 0# 0# (dbl w) (dbl h) s ∷ []) []

-- the label's centre is the frame's centre (`w` half units is half the width)
text : S → S → ℕ → List Inline → Style → Layout S
text w h n t s = mkLayout w h (label w h n t s ∷ []) []

pathL : S → S → String → Style → Layout S
pathL w h d s = mkLayout w h (path 0# 0# d s ∷ []) []

-- Connectives

valignOffset : VAlign → S → S → S
valignOffset top    outer inner = 0#
valignOffset middle outer inner = outer - inner
valignOffset bottom outer inner = dbl (outer - inner)

alignOffset : Align → S → S → S
alignOffset left    outer inner = 0#
alignOffset centred outer inner = outer - inner
alignOffset right   outer inner = dbl (outer - inner)

-- a frame holding two layouts at given positions (half units), the second over the first:
-- every binary connective is one of these
combine : S → S → S × S → Layout S → S × S → Layout S → Layout S
combine w h p a q b = overlay w h (inFrame w h (proj₁ p) (proj₂ p) a) (inFrame w h (proj₁ q) (proj₂ q) b)

-- on top of one another, both centred in the larger frame
atop : Layout S → Layout S → Layout S
atop a b =
  let w = width a ⊔ width b ; h = height a ⊔ height b in
  combine w h (w - width a , h - height a) a (w - width b , h - height b) b

-- `b` right of `a`: `a` at x = 0, `b` at x = width a; widths add, heights join
besideA : VAlign → Layout S → Layout S → Layout S
besideA al a b =
  let h = height a ⊔ height b in
  combine (width a + width b) h (0# , valignOffset al h (height a)) a
          (dbl (width a) , valignOffset al h (height b)) b

-- `b` below `a`
aboveA : Align → Layout S → Layout S → Layout S
aboveA al a b =
  let w = width a ⊔ width b in
  combine w (height a + height b) (alignOffset al w (width a) , 0#) a
          (alignOffset al w (width b) , dbl (height a)) b

-- a caption, the diagram, and room of the caption's height on the other side, so the diagram
-- is at the centre of the frame: the height is two captions plus the diagram
labelAbove labelBelow : Layout S → Layout S → Layout S
labelAbove l d =
  let w = width l ⊔ width d in
  combine w (height l + (height d + height l)) (alignOffset centred w (width l) , 0#) l
          (alignOffset centred w (width d) , dbl (height l)) d
labelBelow l d =
  let w = width l ⊔ width d in
  combine w (height l + (height d + height l)) (alignOffset centred w (width d) , dbl (height l)) d
          (alignOffset centred w (width l) , dbl (height l + height d)) l

-- Names and connections

-- the frame of the layout under a name, in front of its anchors (so, when a name occurs twice,
-- the first is the outermost `named`, and the first child of two)
named : String → Layout S → Layout S
named n (mkLayout w h ds as) = mkLayout w h ds ((n , box 0# 0# w h) ∷ as)

findAnchor : String → List (String × Box S) → Maybe (Box S)
findAnchor n []             = nothing
findAnchor n ((m , b) ∷ bs) = if ⌊ n ≟ m ⌋ then just b else findAnchor n bs

-- the point a port names, in half units: the midpoint of an edge, `at` a percentage along it
portPoint : Port → Box S → S × S
portPoint (side north)  (box l t w h) = l + w , t
portPoint (side south)  (box l t w h) = l + w , t + dbl h
portPoint (side east)   (box l t w h) = l + dbl w , t + h
portPoint (side west)   (box l t w h) = l , t + h
portPoint (side middle) (box l t w h) = l + w , t + h
portPoint (at north p)  (box l t w h) = l + pct p (dbl w) , t
portPoint (at south p)  (box l t w h) = l + pct p (dbl w) , t + dbl h
portPoint (at east p)   (box l t w h) = l + dbl w , t + pct p (dbl h)
portPoint (at west p)   (box l t w h) = l , t + pct p (dbl h)
portPoint (at middle p) b             = portPoint (side middle) b

-- the arrow between two found boxes, with the head at the second; nothing if either is missing
connectArrow : Port → Port → Style → Maybe (Box S) → Maybe (Box S) → List (Draw S)
connectArrow pa pb s (just ba) (just bb) =
  arrow (proj₁ (portPoint pa ba)) (proj₂ (portPoint pa ba))
        (proj₁ (portPoint pb bb)) (proj₂ (portPoint pb bb)) s ∷ []
connectArrow _  _  _ _ _ = []

-- an arrow from one named box to another, over everything; a missing name draws nothing
-- (`Slides.Diagram.Names` reports it).  The frame and the anchors are the child's.
connectP : String → Port → String → Port → Style → Layout S → Layout S
connectP a pa b pb s (mkLayout w h ds as) =
  mkLayout w h (ds ++ connectArrow pa pb s (findAnchor a as) (findAnchor b as)) as
