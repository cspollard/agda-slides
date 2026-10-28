{-# OPTIONS --safe --without-K #-}

-- The diagram language: one container, and the free monad on it.
--
-- `Op S` is the signature, over a scalar `S` for sizes.  Its operations are
--
--   * primitives (no sub-diagrams): rectangles, text, spacers, …
--   * binary connectives, which place two diagrams relative to each other:
--     beside, above, atop, and the two that keep a caption's room free
--   * absolute placement: `Place` (a child at `(x, y)` of a frame of declared size) and
--     `Overlay` (two children at the corner of a declared frame): no centring, so the
--     coordinates do not depend on the size of a neighbour; this is what keeps the symbolic
--     layout of a template small (`Slides.Examples.PairsHero`, `docs/Design.md`)
--   * annotations (one sub-diagram) that do not change the picture's geometry:
--     `Named`, `Connect`
--
-- `arity` says how many sub-diagrams each takes (none, `Fin 2`, one), which
-- makes `DiagramC S = Op S ▷ arity` a container.  A diagram is a closed
-- program `DiagramC S ⋆ ⊥`: a tree of operations whose leaves are primitives.
-- Gaps, margins, minimum widths and the like are not operations: they are
-- spacers, so they are built from these in `Slides.Diagram.Notation`.
--
-- An interpretation is an `Algebra S A`, that is `⟦ DiagramC S ⟧ A → A`
-- (curried), and `fold` is the catamorphism.  `Slides.Diagram.Layout` renders,
-- `Slides.Diagram.Names` checks that every connection refers to a name that
-- exists.

module Slides.Diagram.Syntax where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Container.Pick using (pick2)

open import Slides.Diagram using (Style)
open import Slides.Diagram.TextMetrics using (textWidth; spaceWidth)
open import Slides.Diagram.Geometry public
  using (Side; north; south; east; west; middle; Port; side; at; VAlign; top; bottom; Align; left; centred; right)

------------------------------------------------------------------------
-- The signature

-- Geometry conventions (every picture in this file and in
-- `Slides.Diagram.Place` follows them)
--
--   * The origin is the top-left corner of a diagram's frame; x grows to the
--     right and y grows DOWN.
--   * Every diagram has a frame, a width x height rectangle.  The frame is all
--     that a neighbour sees: connectives place frames, never the ink inside.
--   * A connective never scales or rotates a child; it shifts it inside a new
--     frame and declares that frame's size.
--   * Of two children, the second is drawn after the first, so it is on top.
--   * Sizes are in units; positions are kept in half units, so that centring
--     (half of a difference) needs no division (`Slides.Diagram.Draw`).
--
-- Pictures below use `+--+` for a frame, `a`, `b` for the children.

data Op (S : Set) : Set where
  -- A w x h rectangle at the origin.  The frame is w x h.
  --
  --   (0,0)+--------+
  --        |        | h
  --        +--------+
  --            w
  Rectangle : (w h : S) → Style → Op S
  -- A circle of radius r.  The frame is the bounding square, 2r x 2r, and the
  -- centre of the circle is the centre of the frame.
  --
  --      +---------+
  --      |  .---.  |
  --      |  ( c )  |  2r
  --      |  '---'  |
  --      +---------+
  --          2r
  Disc      : (r : S) → Style → Op S
  -- A line from the top-left to the bottom-right corner of a w x h box.  The
  -- frame is that box.
  --
  --   (0,0) *
  --         | \
  --         |  \   h
  --         +---* (w,h)
  Segment   : (w h : S) → Style → Op S
  -- A connected line through the points, in the frame's own coordinates (units, origin at the
  -- top-left, y down).  The frame is the extent of the points from the origin: as wide as the
  -- largest x and as high as the largest y, so every point is inside it and none needs a negative
  -- coordinate.  Fewer than two points draw nothing.  A `Segment` is the polyline through
  -- `(0, 0)` and `(w, h)`, and a curve is a polyline through enough of its points.
  --
  --   (0,0)+---------------+
  --        |    p₂         |
  --        |   /  \   p₄   |
  --        | p₁    p₃ /    |   frame: max x by max y
  --        +---------------+
  Polyline  : (pts : List (S × S)) → Style → Op S
  -- One line of text at a font size, centred in its frame.  The frame is as
  -- wide as the characters (measured from a table; markup counts as
  -- characters) times `widthPct` percent (a heavier font is wider), and
  -- size * 3/2 high.
  --
  --   +-----------+
  --   |   text    |  h = size * 3/2
  --   +-----------+
  --   w = measured width * widthPct / 100
  Text      : (widthPct size : ℕ) → String → Style → Op S
  -- Empty space: a frame of the given size and nothing drawn.  This is how
  -- gaps and margins are made (a zero in one direction, `↔ n` and `↕ n` in
  -- `Slides.Diagram.Notation`).
  Spacer    : (w h : S) → Op S
  -- Two children, the second to the right of the first: the frames touch,
  -- the width is the sum of the widths, the height the larger of the two.  The
  -- alignment says how the shorter one sits in the extra height (`top`,
  -- `middle` = `beside`, `bottom`), with a the first child, b the second.
  --
  --   top            middle         bottom
  --   +--+--+       +--+       +--+
  --   |a |b |    +--+  |       |  |
  --   +--+  |    |a |b |    +--+b |
  --      |  |    +--+  |    |a |  |
  --      +--+       +--+    +--+--+
  Beside    : VAlign → Op S
  -- Two children, the second below the first: the frames touch, the height is
  -- the sum, the width the larger.  The alignment (`left`, `centred` =
  -- `above`, `right`) says how the narrower one sits in the extra width.
  --
  --   left        centred       right
  --   +--+          +--+           +--+
  --   |a |          |a |           |a |
  --   +--+---+    +-+--+-+       +-+--+
  --   |  b   |    |  b   |       |  b   |
  --   +------+    +------+       +------+
  Above     : Align → Op S
  -- Two children on top of one another, both centred in the larger of the two
  -- frames (width and height are each the larger of the two): the second is
  -- drawn over the first.  Nothing is added between them.
  --
  --   +------------+
  --   |   +----+   |  here a is the larger frame and is drawn first;
  --   |   | b  |   |  b is centred over it
  --   |   +----+   |
  --   +------------+
  Atop      : Op S
  -- Two children, a caption and a diagram: a column caption / diagram / empty
  -- space of the caption's height (`LabelBelow` is the mirror image).  So the
  -- height is two captions plus the diagram, and the diagram is exactly at the
  -- centre of the result, whatever the caption's size: this keeps a labelled
  -- thing aligned with its unlabelled neighbours.  Everything is centred
  -- horizontally.
  --
  --   +-----------+
  --   |  caption  |  hl
  --   +-----------+
  --   |  diagram  |  hd        d is centred in the frame
  --   +-----------+
  --   |  (empty)  |  hl
  --   +-----------+
  LabelAbove LabelBelow : Op S
  -- One child at the absolute position (x, y) of a frame of the declared size
  -- w x h.  x and y are in units and measure from the frame's top-left corner
  -- to the child's top-left corner.  Nothing is centred and nothing depends on
  -- the child's size: the frame does not grow to fit (a child that sticks out
  -- is drawn outside it, uncounted).  The child's names move with it.
  --
  --   (0,0)+---------------+
  --        |               |
  --        |   (x,y)+---+  |  frame w x h, declared
  --        |        | d |  |
  --        |        +---+  |
  --        +---------------+
  Place     : (w h x y : S) → Op S
  -- Two children in one frame of the declared size w x h, both with their
  -- top-left corner at the origin, the second drawn over the first.  As for
  -- `Place`, nothing is centred and the frame size does not depend on the
  -- children.
  --
  --   (0,0)+----------------+
  --        | b      |       |  b is drawn over a;
  --        +--------+       |  their top-left corners coincide
  --        |   a            |  (a here is as large as the frame)
  --        +----------------+
  Overlay   : (w h : S) → Op S
  -- Remember the frame of the child under a name, so that a `Connect` further
  -- out can point at it.  The name keeps referring to that frame after later
  -- layout moves it.  Size, drawing and everything else are those of the
  -- child: it is an annotation.
  --
  --   "n" ⦂ d   draws exactly d; the name "n" is the whole frame of d
  Named     : String → Op S
  -- An arrow from a port of one named box to a port of another (see `Port` in
  -- `Slides.Diagram.Geometry`), drawn after the child so that it is over it.
  -- The size, the other drawings and the names are those of the child; the
  -- two names must be bound somewhere inside the child (`Named`), or no arrow
  -- is drawn (`Slides.Diagram.Names` reports it).  The arrowhead is at the
  -- second port.
  --
  --   +-----+                 +-----+
  --   |  a  |>--------------->|  b  |   connect "a" east "b" west
  --   +-----+                 +-----+
  Connect   : String → Port → String → Port → Style → Op S

-- how many sub-diagrams
arity : ∀ {S} → Op S → Set
arity (Rectangle _ _ _) = ⊥
arity (Disc _ _)        = ⊥
arity (Segment _ _ _)   = ⊥
arity (Polyline _ _)    = ⊥
arity (Text _ _ _ _)    = ⊥
arity (Spacer _ _)      = ⊥
arity (Beside _)        = Fin 2
arity (Above _)         = Fin 2
arity Atop              = Fin 2
arity LabelAbove        = Fin 2
arity LabelBelow        = Fin 2
arity (Place _ _ _ _)   = ⊤
arity (Overlay _ _)     = Fin 2
arity (Named _)         = ⊤
arity (Connect _ _ _ _ _) = ⊤

DiagramC : Set → Container 0ℓ 0ℓ
DiagramC S = Op S ▷ arity

-- A diagram.
Dia : Set → Set
Dia S = DiagramC S ⋆ ⊥

------------------------------------------------------------------------
-- Interpretation: algebras and the catamorphism

-- `⟦ DiagramC S ⟧ A → A`, curried: an operation and the results for its children
Algebra : Set → Set → Set
Algebra S A = (o : Op S) → (arity o → A) → A

fold : ∀ {S A} → Algebra S A → Dia S → A
fold α (pure ())
fold α (impure (o , k)) = α o (λ i → fold α (k i))

------------------------------------------------------------------------
-- The surface language (nothing here needs a zero, so any scalar will do)

rectangle : ∀ {S} → S → S → Style → Dia S
rectangle w h s = impure (Rectangle w h s , λ ())

disc : ∀ {S} → S → Style → Dia S
disc r s = impure (Disc r s , λ ())

segment : ∀ {S} → S → S → Style → Dia S
segment w h s = impure (Segment w h s , λ ())

polyline : ∀ {S} → List (S × S) → Style → Dia S
polyline pts s = impure (Polyline pts s , λ ())

text bold : ∀ {S} → ℕ → String → Style → Dia S
text size t s = impure (Text 100 size t s , λ ())
bold size t s = impure (Text 108 size t s , λ ())

spacer : ∀ {S} → S → S → Dia S
spacer w h = impure (Spacer w h , λ ())


-- `a` then `b` to its right / below it
besideA : ∀ {S} → VAlign → Dia S → Dia S → Dia S
besideA al a b = impure (Beside al , pick2 a b)

aboveA : ∀ {S} → Align → Dia S → Dia S → Dia S
aboveA al a b = impure (Above al , pick2 a b)

-- put `b` on top of `a`, both centred
atop : ∀ {S} → Dia S → Dia S → Dia S
atop a b = impure (Atop , pick2 a b)

-- centred
beside above : ∀ {S} → Dia S → Dia S → Dia S
beside = besideA middle
above  = aboveA centred

-- a caption above or below a diagram, with room of the caption's size on the
-- other side
labelAbove labelBelow : ∀ {S} → Dia S → Dia S → Dia S
labelAbove lbl d = impure (LabelAbove , pick2 lbl d)
labelBelow lbl d = impure (LabelBelow , pick2 lbl d)

-- a rectangle of a given size with a diagram centred on it
framed : ∀ {S} → S → S → Style → Dia S → Dia S
framed w h s d = atop (rectangle w h s) d

-- two diagrams in one w × h frame, both at its corner, the second over the first
overlay : ∀ {S} → S → S → Dia S → Dia S → Dia S
overlay w h a b = impure (Overlay w h , pick2 a b)

-- a diagram at the absolute position (x, y) of an empty w × h frame
place : ∀ {S} → S → S → S → S → Dia S → Dia S
place w h x y d = impure (Place w h x y , λ _ → d)

-- remember the extent of a diagram under a name
named : ∀ {S} → String → Dia S → Dia S
named n d = impure (Named n , λ _ → d)

-- an arrow from a port of one named box to a port of another
connectP : ∀ {S} → String → Port → String → Port → Style → Dia S → Dia S
connectP a pa b pb s d = impure (Connect a pa b pb s , λ _ → d)

-- … between sides (the middle of an edge)
connect : ∀ {S} → String → Side → String → Side → Style → Dia S → Dia S
connect a sa b sb = connectP a (side sa) b (side sb)

-- an arrow from the east edge of one named box to the west edge of another
connectEW : ∀ {S} → String → String → Style → Dia S → Dia S
connectEW a b = connect a east b west

-- a map on both coordinates of a point
onPair : ∀ {S T : Set} → (S → T) → S × S → T × T
onPair f p = f (proj₁ p) , f (proj₂ p)

-- Change of scalar: a diagram with sizes in `S` becomes one with sizes in `T`.
-- This is the action of `Dia` on functions (a fold, rebuilding each operation).
rescale : ∀ {S T} → (S → T) → Algebra S (Dia T)
rescale f (Rectangle w h s)       _ = rectangle (f w) (f h) s
rescale f (Disc r s)              _ = disc (f r) s
rescale f (Segment w h s)         _ = segment (f w) (f h) s
rescale f (Polyline pts s)        _ = polyline (map (onPair f) pts) s
rescale f (Text pct size t s)     _ = impure (Text pct size t s , λ ())
rescale f (Spacer w h)            _ = spacer (f w) (f h)
rescale f (Beside al)             k = besideA al (k zero) (k (suc zero))
rescale f (Above al)              k = aboveA al (k zero) (k (suc zero))
rescale f Atop                    k = atop (k zero) (k (suc zero))
rescale f LabelAbove              k = labelAbove (k zero) (k (suc zero))
rescale f LabelBelow              k = labelBelow (k zero) (k (suc zero))
rescale f (Place w h x y)         k = place (f w) (f h) (f x) (f y) (k tt)
rescale f (Overlay w h)           k = overlay (f w) (f h) (k zero) (k (suc zero))
rescale f (Named n)               k = named n (k tt)
rescale f (Connect a pa b pb s)   k = connectP a pa b pb s (k tt)

mapDia : ∀ {S T} → (S → T) → Dia S → Dia T
mapDia f = fold (rescale f)

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

