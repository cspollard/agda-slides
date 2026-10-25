{-# OPTIONS --safe --without-K #-}

-- The layout operations: the semantics of the connectives of
-- `Slides.Diagram.Syntax`, over any scalar `Ops S`.  `Slides.Diagram.Layout`
-- assembles them into an algebra, and `Slides.Diagram.Laws` states and proves
-- their laws.
--
-- A `Layout` is a rectangle of known size, the drawing commands that fill it
-- (relative to its top-left corner) and the named sub-rectangles inside it.
-- Combining layouts shifts the drawing commands and the anchors of each part;
-- every operation grows its frame to fit, so offsets are never negative.
--
-- Positions are in half units and sizes in units (see `Slides.Diagram.Draw`).
-- That is what makes centring exact: a child of size `inner` in a frame of
-- size `outer` is at position `outer - inner` (that is, half of it in units).
-- `-` is only applied to a larger minuend, so ℕ's monus never truncates.

open import Slides.Diagram.Scalar using (Ops)

module Slides.Diagram.Place {S : Set} (O : Ops S) where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _*_; _/_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram using (Style; Element; rect; circle; line; arrow; label)
import Slides.Diagram as D
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open import Slides.Diagram.TextMetrics using (textWidth)

open Ops O

------------------------------------------------------------------------
-- Shifting

shiftDraw : S → S → Draw S → Draw S
shiftDraw dx dy (rect x y w h s)       = rect (x + dx) (y + dy) w h s
shiftDraw dx dy (circle x y r s)       = circle (x + dx) (y + dy) r s
shiftDraw dx dy (line a b c d s)       = line (a + dx) (b + dy) (c + dx) (d + dy) s
shiftDraw dx dy (arrow a b c d s)      = arrow (a + dx) (b + dy) (c + dx) (d + dy) s
shiftDraw dx dy (label x y n t s)      = label (x + dx) (y + dy) n t s

shiftBox : S → S → Box S → Box S
shiftBox dx dy (box l t w h) = box (l + dx) (t + dy) w h

shiftAnchor : S → S → String × Box S → String × Box S
shiftAnchor dx dy (n , b) = n , shiftBox dx dy b

-- the same layout, shifted inside a frame of a given size
inFrame : S → S → S → S → Layout S → Layout S
inFrame w h dx dy d = layout w h
  (map (shiftDraw dx dy) (Layout.draws d))
  (map (shiftAnchor dx dy) (Layout.anchors d))

-- two layouts in one frame, the second drawn over the first
overlay : S → S → Layout S → Layout S → Layout S
overlay w h a b = layout w h (Layout.draws a ++ Layout.draws b) (Layout.anchors a ++ Layout.anchors b)

width height : Layout S → S
width  = Layout.width
height = Layout.height

------------------------------------------------------------------------
-- Primitives

spacer : S → S → Layout S
spacer w h = layout w h [] []

rectangle : S → S → Style → Layout S
rectangle w h s = layout w h (rect 0# 0# w h s ∷ []) []

disc : S → Style → Layout S
disc r s = layout (dbl r) (dbl r) (circle (dbl r) (dbl r) r s ∷ []) []

-- a line from the top-left to the bottom-right corner
segment : S → S → Style → Layout S
segment w h s = layout w h (line 0# 0# (dbl w) (dbl h) s ∷ []) []

-- text: as wide as its characters (`pct` percent, for a heavier font), and
-- `size * 3/2` high
text : ℕ → ℕ → String → Style → Layout S
text pct size t s = layout w h (label w h size t s ∷ []) []
  where w = fromℕ ((textWidth size t * pct) / 100)
        h = fromℕ ((size * 3) / 2)


------------------------------------------------------------------------
-- Combining

-- `inner` inside `outer`: the position, in half units
valignOffset : VAlign → S → S → S
valignOffset top    outer inner = 0#
valignOffset middle outer inner = outer - inner
valignOffset bottom outer inner = dbl (outer - inner)

alignOffset : Align → S → S → S
alignOffset left    outer inner = 0#
alignOffset centred outer inner = outer - inner
alignOffset right   outer inner = dbl (outer - inner)

-- a frame holding two layouts at given positions, the second drawn over the
-- first: every binary connective is one of these
combine : S → S → S × S → Layout S → S × S → Layout S → Layout S
combine w h p a q b =
  overlay w h (inFrame w h (proj₁ p) (proj₂ p) a) (inFrame w h (proj₁ q) (proj₂ q) b)

-- on top of one another, both centred
atop : Layout S → Layout S → Layout S
atop a b =
  let w = width a ⊔ width b ; h = height a ⊔ height b in
  combine w h (w - width a , h - height a) a (w - width b , h - height b) b

besideA : VAlign → Layout S → Layout S → Layout S
besideA al a b =
  let w = width a + width b ; h = height a ⊔ height b in
  combine w h (0# , valignOffset al h (height a)) a
              (dbl (width a) , valignOffset al h (height b)) b

aboveA : Align → Layout S → Layout S → Layout S
aboveA al a b =
  let w = width a ⊔ width b ; h = height a + height b in
  combine w h (alignOffset al w (width a) , 0#) a
              (alignOffset al w (width b) , dbl (height a)) b

-- a caption above or below, with empty space of the caption's size on the
-- other side, so the layout stays at the centre
labelAbove labelBelow : Layout S → Layout S → Layout S
labelAbove lbl d = aboveA centred lbl (aboveA centred d (spacer 0# (height lbl)))
labelBelow lbl d = aboveA centred (spacer 0# (height lbl)) (aboveA centred d lbl)

------------------------------------------------------------------------
-- Names and connections

named : String → Layout S → Layout S
named n d = layout (width d) (height d) (Layout.draws d)
  ((n , box 0# 0# (width d) (height d)) ∷ Layout.anchors d)

findAnchor : String → List (String × Box S) → Maybe (Box S)
findAnchor n [] = nothing
findAnchor n ((m , b) ∷ bs) = if ⌊ n ≟ m ⌋ then just b else findAnchor n bs

-- the point of a box a port names, in half units
portPoint : Port → Box S → S × S
portPoint (side north)  (box l t w h) = l + w , t
portPoint (side south)  (box l t w h) = l + w , t + dbl h
portPoint (side east)   (box l t w h) = l + dbl w , t + h
portPoint (side west)   (box l t w h) = l , t + h
portPoint (side middle) (box l t w h) = l + w , t + h
portPoint (at north p)  (box l t w h) = l + percentOf p (dbl w) , t
portPoint (at south p)  (box l t w h) = l + percentOf p (dbl w) , t + dbl h
portPoint (at east p)   (box l t w h) = l + dbl w , t + percentOf p (dbl h)
portPoint (at west p)   (box l t w h) = l , t + percentOf p (dbl h)
portPoint (at middle p) b             = portPoint (side middle) b

-- An arrow between two named boxes.  A name that does not exist draws
-- nothing; `Slides.Diagram.Names` reports such connections.
connectP : String → Port → String → Port → Style → Layout S → Layout S
connectP a pa b pb s d with findAnchor a (Layout.anchors d) | findAnchor b (Layout.anchors d)
... | just ba | just bb =
  let (x₁ , y₁) = portPoint pa ba ; (x₂ , y₂) = portPoint pb bb in
  layout (width d) (height d) (Layout.draws d ++ arrow x₁ y₁ x₂ y₂ s ∷ []) (Layout.anchors d)
... | _ | _ = d

------------------------------------------------------------------------
-- Output: the final drawing, with positions halved to diagram units

toElement : Draw S → Element
toElement (rect x y w h s)  = D.rect (half x) (half y) (toℕ w) (toℕ h) s
  where half : S → ℕ
        half p = toℕ p / 2
toElement (circle x y r s)  = D.circle (toℕ x / 2) (toℕ y / 2) (toℕ r) s
toElement (line a b c d s)  = D.line (toℕ a / 2) (toℕ b / 2) (toℕ c / 2) (toℕ d / 2) s
toElement (arrow a b c d s) = D.arrow (toℕ a / 2) (toℕ b / 2) (toℕ c / 2) (toℕ d / 2) s
toElement (label x y n t s) = D.label (toℕ x / 2) (toℕ y / 2) n t s
