{-# OPTIONS --safe --without-K #-}

-- Operators for writing diagrams: a notation over the smart constructors of
-- `Slides.Diagram.Syntax` (it builds the same terms, so every interpretation
-- of the language applies unchanged).
--
-- The algebra.  `Dia` has three associative operations with the unit `empty`:
--
--   a ∥ b   beside (b to the right of a, centred vertically)
--   a ═ b   above  (b below a, centred horizontally)
--   a ⊙ b   atop   (b on top of a, centred)
--
-- A gap is an ordinary diagram (`↔ n` is n units of width, `↕ n` of height), so
-- `a ∥ ↔ 40 ∥ b` needs no gap parameter and chains without nesting.  Margins,
-- minimum widths and captions are built the same way, from spacers.  There is
-- no interchange law between `∥` and `═`: `(a ∥ b) ═ (c ∥ d)` and
-- `(a ═ c) ∥ (b ═ d)` align their columns differently.
--
-- What needs a zero (`empty`, `↔`, the combinators with gaps) is in
-- `NotationWith O` for a scalar `Ops S`; decks get it at ℕ.
--
-- Edges are data, `"a" ⟶ "b"`, and `d ▹[ style ] edges` draws a list of them,
-- in order, over `d`.

module Slides.Diagram.Notation where

open import Data.List using (List; []; _∷_; foldl; map)
open import Data.Nat using (ℕ)
open import Data.String using (String; words)

open import Slides.Diagram using (Style)
open import Slides.Diagram.Scalar using (Ops; natOps)
open import Slides.Diagram.Syntax public

------------------------------------------------------------------------
-- Composition

infixr 8 _⊙_
infixr 7 _∥_
infixr 6 _═_

-- The three connectives (pictures of each: `Slides.Diagram.Syntax`):
--
--   a ∥ b          a ═ b         a ⊙ b
--   +---+---+      +-------+     +-----------+
--   | a | b |      |   a   |     |  +-----+  |   b is on top of a,
--   +---+---+      +-------+     |  |  b  |  |   both centred
--   (centred        |   b   |     |  +-----+  |
--    vertically)   +-------+     +-----------+
--
-- Frames touch for `∥` and `═`; `⊙` adds nothing.  Sizes: `∥` adds widths
-- and takes the larger height; `═` adds heights and takes the larger width; `⊙`
-- takes the larger of each.  Precedence: `⊙` binds tightest, then `∥`, then `═`,
-- so `a ∥ b ═ c ∥ d` is `(a ∥ b) ═ (c ∥ d)`.

_∥_ _═_ _⊙_ : ∀ {S} → Dia S → Dia S → Dia S
_∥_ = besideA middle
_═_ = aboveA centred
_⊙_ = atop

-- the same, aligned: `∥↑ ∥↓` to the top or bottom, `═◂ ═▸` left or right
--
-- (the pictures of the alignments are with `Beside` and `Above` in
-- `Slides.Diagram.Syntax`)
infixr 7 _∥↑_ _∥↓_
infixr 6 _═◂_ _═▸_

_∥↑_ _∥↓_ _═◂_ _═▸_ : ∀ {S} → Dia S → Dia S → Dia S
_∥↑_ = besideA top
_∥↓_ = besideA bottom
_═◂_ = aboveA left
_═▸_ = aboveA right

------------------------------------------------------------------------
-- Names and edges

infixr 4 _⦂_

-- `"id" ⦂ d`: remember the extent (the whole frame) of `d` under a name.  It
-- changes neither the size nor the drawing.
_⦂_ : ∀ {S} → String → Dia S → Dia S
_⦂_ = named

-- A place on a named box: `"a" ⊢ side east`, `"a" ⊢ at south 40` (ports are
-- pictured in `Slides.Diagram.Geometry`).
infix 8 _⊢_
record Endpoint : Set where
  constructor _⊢_
  field
    name : String
    port : Port

record Edge : Set where
  constructor edge
  field
    from to : Endpoint

infix 7 _⟶_ _⟱_ _⇒_

-- east edge to west edge, south edge to north edge, or any two ports.  The
-- arrow goes from the first named box to the second.
--
--   "a" ⟶ "b"                "a" ⟱ "b"
--   +---+            +---+      +---+
--   | a |>---------->| b |      | a |
--   +---+            +---+      +-v-+
--                                 |
--                               +-v-+
--                               | b |
--                               +---+
_⟶_ _⟱_ : String → String → Edge
a ⟶ b = edge (a ⊢ side east)  (b ⊢ side west)
a ⟱ b = edge (a ⊢ side south) (b ⊢ side north)

_⇒_ : Endpoint → Endpoint → Edge
_⇒_ = edge

private
  draw : ∀ {S} → Style → Dia S → Edge → Dia S
  draw s d (edge (a ⊢ pa) (b ⊢ pb)) = connectP a pa b pb s d

infixl 3 _▹[_]_ _▹_∶_

-- Draw edges in a style over `d`, the first one first (later ones on top).
-- Each is a `Connect` around the result so far, so the size and the other
-- drawings of `d` do not change; an edge whose name `d` does not bind draws
-- nothing.
_▹[_]_ : ∀ {S} → Dia S → Style → List Edge → Dia S
d ▹[ s ] es = foldl (draw s) d es

-- one edge
_▹_∶_ : ∀ {S} → Dia S → Edge → Style → Dia S
d ▹ e ∶ s = d ▹[ s ] (e ∷ [])

------------------------------------------------------------------------
-- What needs a zero

module NotationWith {S : Set} (O : Ops S) where
  open Ops O using (0#)

  -- Empty space; the unit of `∥`, `═` and `⊙` (a frame 0 x 0, nothing drawn).
  -- `↔ n` is a frame n wide and 0 high, `↕ n` is 0 wide and n high: a gap
  -- between two neighbours, since sizes add along the direction of the join.
  --
  --   a ∥ ↔ 4 ∥ b          a ═ ↕ 4 ═ b
  --   +---+    +---+       +---+
  --   | a |<-->| b |       | a |
  --   +---+  4 +---+       +---+  ^ 4
  --                        +---+  v
  --                        | b |
  --                        +---+
  empty : Dia S
  empty = spacer 0# 0#

  ↔ ↕ : S → Dia S
  ↔ n = spacer n 0#
  ↕ n = spacer 0# n

  -- A row / column with the same gap between neighbours (and none at the
  -- ends); `al` aligns as in `besideA` / `aboveA`.  An empty list is `empty`.
  --
  --   hcat g (a ∷ b ∷ c ∷ [])
  --   +---+     +---+     +---+     the gaps are spacers of width g
  --   | a |<-g->| b |<-g->| c |     (right-nested, so it needs no
  --   +---+     +---+     +---+      parentheses)
  hcatA : VAlign → S → List (Dia S) → Dia S
  hcatA al g []       = empty
  hcatA al g (d ∷ []) = d
  hcatA al g (d ∷ ds) = besideA al d (besideA al (↔ g) (hcatA al g ds))

  hcat : S → List (Dia S) → Dia S
  hcat = hcatA middle

  vcatA : Align → S → List (Dia S) → Dia S
  vcatA al g []       = empty
  vcatA al g (d ∷ []) = d
  vcatA al g (d ∷ ds) = aboveA al d (aboveA al (↕ g) (vcatA al g ds))

  vcat : S → List (Dia S) → Dia S
  vcat = vcatA centred

  ⟨_⟩ₕ_ ⟨_⟩ᵥ_ : List (Dia S) → S → Dia S
  ⟨ ds ⟩ₕ g = hcat g ds
  ⟨ ds ⟩ᵥ g = vcat g ds

  -- Extra space left, top, right, bottom: the frame grows by that much, the
  -- diagram keeps its size and is shifted by (left, top).
  --
  --   +---------------+
  --   |   top         |
  --   | l +-------+ r |
  --   |   |   d   |   |
  --   |   +-------+   |
  --   |   bottom      |
  --   +---------------+
  margin : S → S → S → S → Dia S → Dia S
  margin l t r b d = ↔ l ∥ ((↕ t ═ d ═ ↕ b) ∥ ↔ r)

  padded : S → Dia S → Dia S
  padded n = margin n n n n

  -- At least this wide, the diagram centred (to give columns equal widths):
  -- `d ⊙ ↔ w`, so the width is the larger of the two and the height is `d`'s.
  --
  --   +--------------+
  --   |   +-----+    |   width max w (width d); d centred
  --   |   |  d  |    |
  --   |   +-----+    |
  --   +--------------+
  boxWidth : S → Dia S → Dia S
  boxWidth w d = d ⊙ ↔ w

  -- The diagram at the top of a frame of at least the given height: `d ∥↑
  -- ↕ h`, so the width is `d`'s and the height the larger of `d`'s and `h`.
  -- Inside `framed` this lines up contents of different heights.
  --
  --   +-----+  h        the empty space is below d,
  --   |  d  |           not around it
  --   +-----+
  topAligned : S → Dia S → Dia S
  topAligned h d = d ∥↑ ↕ h

  -- A caption a gap above or below a diagram (the diagram stays centred): the
  -- caption with the gap on its far side is the `labelAbove` caption, so the
  -- room kept free on the other side is as big as caption plus gap.
  --
  --   captionAbove g lbl d
  --   +-------+
  --   |  lbl  |
  --   +-------+
  --   |  gap  | g
  --   +-------+
  --   |   d   |        (and the same amount of empty space below d)
  --   +-------+
  captionAbove captionBelow : S → Dia S → Dia S → Dia S
  captionAbove g lbl d = labelAbove (lbl ═ ↕ g) d
  captionBelow g lbl d = labelBelow (↕ g ═ lbl) d

  -- `d ⌄[ g ] lbl` puts a caption a gap below `d`, `lbl ⌃[ g ] d` above it
  infixl 9 _⌄[_]_ _⌃[_]_

  _⌄[_]_ : Dia S → S → Dia S → Dia S
  d ⌄[ g ] lbl = captionBelow g lbl d

  _⌃[_]_ : Dia S → S → Dia S → Dia S
  lbl ⌃[ g ] d = captionAbove g lbl d

  -- lines of text, one under the other, centred (`vcat 0`: no gap)
  lines : ℕ → List String → Style → Dia S
  lines size ts s = vcat 0# (map (λ t → text size t s) ts)

  paragraph : Align → ℕ → ℕ → String → Style → Dia S
  paragraph al size maxWidth t s =
    vcatA al 0# (map (λ l → text size l s) (wrap size maxWidth (words t)))

-- decks compute in ℕ
open NotationWith natOps public
