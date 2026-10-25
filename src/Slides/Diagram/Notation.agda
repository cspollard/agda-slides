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

_∥_ _═_ _⊙_ : ∀ {S} → Dia S → Dia S → Dia S
_∥_ = besideA middle
_═_ = aboveA centred
_⊙_ = atop

-- the same, aligned: `∥↑ ∥↓` to the top or bottom, `═◂ ═▸` left or right
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

-- `"id" ⦂ d`: remember the extent of `d` under a name
_⦂_ : ∀ {S} → String → Dia S → Dia S
_⦂_ = named

-- a place on a named box: `"a" ⊢ side east`, `"a" ⊢ at south 40`
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

-- east edge to west edge, south edge to north edge, or any two ports
_⟶_ _⟱_ : String → String → Edge
a ⟶ b = edge (a ⊢ side east)  (b ⊢ side west)
a ⟱ b = edge (a ⊢ side south) (b ⊢ side north)

_⇒_ : Endpoint → Endpoint → Edge
_⇒_ = edge

private
  draw : ∀ {S} → Style → Dia S → Edge → Dia S
  draw s d (edge (a ⊢ pa) (b ⊢ pb)) = connectP a pa b pb s d

infixl 3 _▹[_]_ _▹_∶_

-- draw edges in a style, the first one first (later ones on top)
_▹[_]_ : ∀ {S} → Dia S → Style → List Edge → Dia S
d ▹[ s ] es = foldl (draw s) d es

-- one edge
_▹_∶_ : ∀ {S} → Dia S → Edge → Style → Dia S
d ▹ e ∶ s = d ▹[ s ] (e ∷ [])

------------------------------------------------------------------------
-- What needs a zero

module NotationWith {S : Set} (O : Ops S) where
  open Ops O using (0#)

  -- empty space
  empty : Dia S
  empty = spacer 0# 0#

  ↔ ↕ : S → Dia S
  ↔ n = spacer n 0#
  ↕ n = spacer 0# n

  -- a row / column with a gap between neighbours
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

  -- extra space left, top, right, bottom
  margin : S → S → S → S → Dia S → Dia S
  margin l t r b d = ↔ l ∥ ((↕ t ═ d ═ ↕ b) ∥ ↔ r)

  padded : S → Dia S → Dia S
  padded n = margin n n n n

  -- at least this wide, the diagram centred (to give columns equal widths)
  boxWidth : S → Dia S → Dia S
  boxWidth w d = d ⊙ ↔ w

  -- the diagram at the top of a frame of the given height (centred
  -- horizontally); inside `framed` this lines up contents of different heights
  topAligned : S → Dia S → Dia S
  topAligned h d = d ∥↑ ↕ h

  -- a caption a gap above or below a diagram (the diagram stays centred)
  captionAbove captionBelow : S → Dia S → Dia S → Dia S
  captionAbove g lbl d = labelAbove (lbl ═ ↕ g) d
  captionBelow g lbl d = labelBelow (↕ g ═ lbl) d

  -- `d ⌄[ g ] lbl` puts a caption a gap below `d`, `lbl ⌃[ g ] d` above it
  infixl 9 _⌄[_]_ _⌃[_]_

  _⌄[_]_ : Dia S → S → Dia S → Dia S
  d ⌄[ g ] lbl = captionBelow g lbl d

  _⌃[_]_ : Dia S → S → Dia S → Dia S
  lbl ⌃[ g ] d = captionAbove g lbl d

  -- lines of text, one under the other, centred
  lines : ℕ → List String → Style → Dia S
  lines size ts s = vcat 0# (map (λ t → text size t s) ts)

  paragraph : Align → ℕ → ℕ → String → Style → Dia S
  paragraph al size maxWidth t s =
    vcatA al 0# (map (λ l → text size l s) (wrap size maxWidth (words t)))

-- decks compute in ℕ
open NotationWith natOps public
