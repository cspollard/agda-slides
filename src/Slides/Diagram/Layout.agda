{-# OPTIONS --safe --without-K #-}

-- A small layout language for diagrams, in the spirit of Haskell's `diagrams`.
--
-- A `Dia` is a rectangle of known size that knows how to draw itself at any
-- offset, plus the named sub-rectangles ("anchors") inside it.  Combinators
-- put diagrams beside, above or on top of each other; `connect` then draws an
-- arrow between two named boxes, so no coordinate is written by hand.  `compile`
-- turns the result into a `Slides.Diagram.Diagram`, so the backends and the
-- stylesheets are unchanged.
--
-- Coordinates are natural numbers: a `Dia` always lives at non-negative
-- offsets inside its own frame, and every combinator grows the frame to fit.
-- Text is measured from a table of character widths (see
-- `Slides.Diagram.TextMetrics`): a `text` is `size * 3/2` high and as wide as
-- its characters, markup included, so centring, spacing and `paragraph`'s word
-- wrapping follow the actual text.

module Slides.Diagram.Layout where

open import Data.Bool using (Bool; if_then_else_; not; _∧_)
open import Data.List using (List; []; _∷_; map; _++_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _/_; _⊔_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; length; words; _≟_) renaming (_++_ to _++ˢ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram
open import Slides.Diagram.TextMetrics using (textWidth; spaceWidth)

-- A rectangle: left, top, width, height.
record Box : Set where
  constructor box
  field
    left top width height : ℕ

-- The points of a box that a connection can attach to.
data Side : Set where
  north south east west middle : Side

point : Side → Box → ℕ × ℕ
point north  (box l t w h) = l + w / 2 , t
point south  (box l t w h) = l + w / 2 , t + h
point east   (box l t w h) = l + w , t + h / 2
point west   (box l t w h) = l , t + h / 2
point middle (box l t w h) = l + w / 2 , t + h / 2

-- A point along a side, in percent from the left (north, south) or the top
-- (east, west): `at north 40` is two fifths of the way along the top edge.
-- It spreads several connections over one edge.
data Port : Set where
  side : Side → Port
  at   : Side → ℕ → Port

portPoint : Port → Box → ℕ × ℕ
portPoint (side s)    b             = point s b
portPoint (at north p) (box l t w h) = l + (w * p) / 100 , t
portPoint (at south p) (box l t w h) = l + (w * p) / 100 , t + h
portPoint (at east p)  (box l t w h) = l + w , t + (h * p) / 100
portPoint (at west p)  (box l t w h) = l , t + (h * p) / 100
portPoint (at middle p) b            = point middle b

shiftBox : ℕ → ℕ → Box → Box
shiftBox dx dy (box l t w h) = box (l + dx) (t + dy) w h

record Dia : Set where
  field
    width   : ℕ
    height  : ℕ
    -- draw the diagram with its top-left corner at the given offset
    render  : ℕ → ℕ → List Element
    anchors : List (String × Box)

open Dia public

------------------------------------------------------------------------
-- Basic diagrams

-- empty space of a given size
spacer : ℕ → ℕ → Dia
spacer w h = record { width = w ; height = h ; render = λ _ _ → [] ; anchors = [] }

empty : Dia
empty = spacer 0 0

-- a rectangle (the style carries the corner radius, class, id, …)
rectangle : ℕ → ℕ → Style → Dia
rectangle w h s = record
  { width = w ; height = h ; anchors = []
  ; render = λ x y → rect x y w h s ∷ [] }

-- a circle of radius r
disc : ℕ → Style → Dia
disc r s = record
  { width = 2 * r ; height = 2 * r ; anchors = []
  ; render = λ x y → circle (x + r) (y + r) r s ∷ [] }

-- a line from the top-left to the bottom-right corner of a w × h box
-- (a horizontal rule is `segment w 0`)
segment : ℕ → ℕ → Style → Dia
segment w h s = record
  { width = w ; height = h ; anchors = []
  ; render = λ x y → line x y (x + w) (y + h) s ∷ [] }

-- one line of text at a font size; `textScaled` stretches the measured width
-- (percent) for a heavier font, as `bold` does
textScaled : ℕ → ℕ → String → Style → Dia
textScaled pct size t s = record
  { width = w ; height = (size * 3) / 2 ; anchors = []
  ; render = λ x y → label (x + w / 2) (y + (size * 3) / 4) size t s ∷ [] }
  where w = (textWidth size t * pct) / 100

text bold : ℕ → String → Style → Dia
text = textScaled 100
bold = textScaled 108

-- raw elements, drawn with the diagram's own coordinates at the given size
-- (the escape hatch: paths, curves, anything the combinators do not cover)
raw : ℕ → ℕ → List Element → Dia
raw w h es = record { width = w ; height = h ; anchors = [] ; render = λ _ _ → es }

------------------------------------------------------------------------
-- Moving and combining

-- the same diagram, shifted inside a frame of a given size
inFrame : ℕ → ℕ → ℕ → ℕ → Dia → Dia
inFrame w h dx dy d = record
  { width = w ; height = h
  ; render = λ x y → render d (x + dx) (y + dy)
  ; anchors = map (λ { (n , b) → n , shiftBox dx dy b }) (anchors d) }

-- two diagrams in one frame, the second drawn over the first
overlay : ℕ → ℕ → Dia → Dia → Dia
overlay w h a b = record
  { width = w ; height = h
  ; render = λ x y → render a x y ++ render b x y
  ; anchors = anchors a ++ anchors b }

-- centre an extent `inner` inside `outer`
centre : ℕ → ℕ → ℕ
centre outer inner = (outer ∸ inner) / 2

-- put `b` on top of `a`, both centred
atop : Dia → Dia → Dia
atop a b =
  let w = width a ⊔ width b ; h = height a ⊔ height b in
  overlay w h (inFrame w h (centre w (width a)) (centre h (height a)) a)
              (inFrame w h (centre w (width b)) (centre h (height b)) b)

data VAlign : Set where
  top middle bottom : VAlign

valignOffset : VAlign → ℕ → ℕ → ℕ
valignOffset top    outer inner = 0
valignOffset middle outer inner = centre outer inner
valignOffset bottom outer inner = outer ∸ inner

-- `a` then `b` to its right, a gap apart, aligned vertically
besideA : VAlign → ℕ → Dia → Dia → Dia
besideA al g a b =
  let w = width a + g + width b ; h = height a ⊔ height b in
  overlay w h (inFrame w h 0 (valignOffset al h (height a)) a)
              (inFrame w h (width a + g) (valignOffset al h (height b)) b)

-- centred
beside : ℕ → Dia → Dia → Dia
beside = besideA middle

data Align : Set where
  left centred right : Align

-- offset of an extent of size `inner` inside `outer`
alignOffset : Align → ℕ → ℕ → ℕ
alignOffset left    outer inner = 0
alignOffset centred outer inner = centre outer inner
alignOffset right   outer inner = outer ∸ inner

-- `a` then `b` below it, a gap apart, aligned horizontally
aboveA : Align → ℕ → Dia → Dia → Dia
aboveA al g a b =
  let w = width a ⊔ width b ; h = height a + g + height b in
  overlay w h (inFrame w h (alignOffset al w (width a)) 0 a)
              (inFrame w h (alignOffset al w (width b)) (height a + g) b)

-- centred
above : ℕ → Dia → Dia → Dia
above = aboveA centred

-- a row / column of diagrams with a gap between neighbours
hcatA : VAlign → ℕ → List Dia → Dia
hcatA al g []       = empty
hcatA al g (d ∷ []) = d
hcatA al g (d ∷ ds) = besideA al g d (hcatA al g ds)

hcat : ℕ → List Dia → Dia
hcat = hcatA middle

vcatA : Align → ℕ → List Dia → Dia
vcatA al g []       = empty
vcatA al g (d ∷ []) = d
vcatA al g (d ∷ ds) = aboveA al g d (vcatA al g ds)

vcat : ℕ → List Dia → Dia
vcat = vcatA centred

-- extra space left, top, right, bottom
margin : ℕ → ℕ → ℕ → ℕ → Dia → Dia
margin l t r b d = inFrame (l + width d + r) (t + height d + b) l t d

padded : ℕ → Dia → Dia
padded n = margin n n n n

-- the diagram at the top of a frame of the given height (centred
-- horizontally); inside `framed` this lines up contents of different heights
topAligned : ℕ → Dia → Dia
topAligned h d = inFrame (width d) (h ⊔ height d) 0 0 d

-- at least this wide, the diagram centred (to give columns equal widths)
boxWidth : ℕ → Dia → Dia
boxWidth w d = let w′ = w ⊔ width d in inFrame w′ (height d) (centre w′ (width d)) 0 d

-- A label above or below a diagram, a gap away.  Empty space of the same size
-- goes on the other side, so the diagram itself stays at the centre of the
-- result: rows of such things still line up on their diagrams.
labelAbove labelBelow : ℕ → Dia → Dia → Dia
labelAbove g lbl d = vcat g (lbl ∷ d ∷ spacer 0 (height lbl) ∷ [])
labelBelow g lbl d = vcat g (spacer 0 (height lbl) ∷ d ∷ lbl ∷ [])

-- a rectangle of a given size with a diagram centred on it
framed : ℕ → ℕ → Style → Dia → Dia
framed w h s d = atop (rectangle w h s) d

-- lines of text, one under the other, centred
lines : ℕ → List String → Style → Dia
lines size ts s = vcat 0 (map (λ t → text size t s) ts)

-- running text broken into lines of at most `maxWidth`, by words.  A word
-- wider than the box gets a line to itself.  Keep markup inside one word
-- (`t_ω`, not `t_{a b}`).
wrap : ℕ → ℕ → List String → List String
wrap size maxWidth = go "" 0
  where
    sp = spaceWidth size
    go : String → ℕ → List String → List String
    go cur w []       = cur ∷ []
    go cur w (x ∷ xs) =
      let xw = textWidth size x in
      if ⌊ cur ≟ "" ⌋ then go x xw xs
      else if (w + sp + xw) ≤ᵇ maxWidth then go (cur ++ˢ " " ++ˢ x) (w + sp + xw) xs
      else cur ∷ go x xw xs

paragraph : Align → ℕ → ℕ → String → Style → Dia
paragraph al size maxWidth t s =
  vcatA al 0 (map (λ l → text size l s) (wrap size maxWidth (words t)))

------------------------------------------------------------------------
-- Names and connections

-- remember the extent of a diagram under a name
named : String → Dia → Dia
named n d = record d { anchors = (n , box 0 0 (width d) (height d)) ∷ anchors d }

private
  find : String → List (String × Box) → Maybe Box
  find n [] = nothing
  find n ((m , b) ∷ bs) = if ⌊ n ≟ m ⌋ then just b else find n bs

-- an arrow from a port of one named box to a port of another.  A name that
-- does not exist draws nothing, so check the picture.
connectP : String → Port → String → Port → Style → Dia → Dia
connectP a pa b pb s d with find a (anchors d) | find b (anchors d)
... | just ba | just bb =
  let (x₁ , y₁) = portPoint pa ba ; (x₂ , y₂) = portPoint pb bb in
  record d { render = λ x y → render d x y ++ arrow (x + x₁) (y + y₁) (x + x₂) (y + y₂) s ∷ [] }
... | _ | _ = d

-- … between sides (the middle of an edge)
connect : String → Side → String → Side → Style → Dia → Dia
connect a sa b sb = connectP a (side sa) b (side sb)

-- an arrow from the east edge of one named box to the west edge of another
connectEW : String → String → Style → Dia → Dia
connectEW a b = connect a east b west

------------------------------------------------------------------------
-- Turning a diagram into a `Diagram`

-- `name` must be unique in the deck; `percent` is the displayed width.
compile : (name : String) (percent : ℕ) → Dia → Diagram
compile n pct d = record
  { name = n ; width = width d ; height = height d ; percent = pct
  ; elements = render d 0 0 }
