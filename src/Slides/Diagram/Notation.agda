{-# OPTIONS --safe --without-K #-}

-- Operators for writing diagrams: a notation over the smart constructors of
-- `Slides.Diagram.Syntax` (it builds the same terms, so every interpretation applies unchanged).
--
-- The algebra.  `Dia` has three associative operations with the unit `empty`:
--
--   a ∥ b   beside (b to the right of a, centred vertically)
--   a ═ b   above  (b below a, centred horizontally)
--   a ⊙ b   atop   (b on top of a, centred)
--
-- A gap is an ordinary diagram (`↔ n` is n units of width, `↕ n` of height), so
-- `a ∥ ↔ 40 ∥ b` needs no gap parameter.  Margins, minimum widths and captions are built the
-- same way, from spacers.  What needs a zero or a literal is in `NotationWith 0# fromℕ` for a
-- scalar `S`; decks get it at ℕ.  Edges are data, `"a" ⟶ "b"`, and `d ▹[ style ] edges` draws a
-- list of them, in order, over `d`.

module Slides.Diagram.Notation where

open import Data.List using (List; []; _∷_; foldl; map)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Diagram.Style using (Style) public
open import Slides.Diagram.Syntax hiding (text) public

infixr 8 _⊙_
infixr 7 _∥_
infixr 6 _═_
infixr 7 _∥↑_ _∥↓_
infixr 6 _═◂_ _═▸_

_∥_ _═_ _⊙_ : ∀ {S} → Dia S → Dia S → Dia S
_∥_ = besideA middle
_═_ = aboveA centred
_⊙_ = atop

_∥↑_ _∥↓_ _═◂_ _═▸_ : ∀ {S} → Dia S → Dia S → Dia S
_∥↑_ = besideA top
_∥↓_ = besideA bottom
_═◂_ = aboveA left
_═▸_ = aboveA right

------------------------------------------------------------------------
-- Names and edges

infixr 4 _⦂_
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

infixl 3 _▹[_]_ _▹_∶_

-- draw edges in a style over `d`, the first one first (later ones on top); an edge whose name `d`
-- does not bind draws nothing
_▹[_]_ : ∀ {S} → Dia S → Style → List Edge → Dia S
d ▹[ s ] es = foldl (λ d′ → λ { (edge (a ⊢ pa) (b ⊢ pb)) → connectP a pa b pb s d′ }) d es

_▹_∶_ : ∀ {S} → Dia S → Edge → Style → Dia S
d ▹ e ∶ s = d ▹[ s ] (e ∷ [])

------------------------------------------------------------------------
-- What needs a zero or a literal

module NotationWith {S : Set} (0# : S) (fromℕ : ℕ → S) where
  -- empty space, the unit of `∥`, `═` and `⊙`; `↔ n` is n wide and 0 high, `↕ n` 0 wide and n high
  empty : Dia S
  empty = spacer 0# 0#

  ↔ ↕ : S → Dia S
  ↔ n = spacer n 0#
  ↕ n = spacer 0# n

  -- a row / column with the same gap between neighbours (none at the ends)
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

  -- extra space left, top, right, bottom around a diagram
  margin : S → S → S → S → Dia S → Dia S
  margin l t r b d = ↔ l ∥ ((↕ t ═ d ═ ↕ b) ∥ ↔ r)

  -- at least this wide, the diagram centred
  boxWidth : S → Dia S → Dia S
  boxWidth w d = d ⊙ ↔ w

  -- the diagram at the top of a frame of at least the given height
  topAligned : S → Dia S → Dia S
  topAligned h d = d ∥↑ ↕ h

  -- a caption a gap above or below a diagram (which stays centred)
  infixl 9 _⌄[_]_ _⌃[_]_
  _⌄[_]_ : Dia S → S → Dia S → Dia S
  d ⌄[ g ] lbl = labelBelow (↕ g ═ lbl) d
  _⌃[_]_ : Dia S → S → Dia S → Dia S
  lbl ⌃[ g ] d = labelAbove (lbl ═ ↕ g) d

  -- a line of text at a font size, `bold` a heavier (wider) one
  text bold : ℕ → String → Style → Dia S
  text = Slides.Diagram.Syntax.text fromℕ 100
  bold = Slides.Diagram.Syntax.text fromℕ 108

  -- lines of text, one under the other, centred
  lines : ℕ → List String → Style → Dia S
  lines size ts s = vcat 0# (map (λ t → text size t s) ts)

-- decks compute in ℕ
open NotationWith 0 (λ n → n) public
