{-# OPTIONS --safe --without-K #-}

-- Writing diagrams: operators and one-line combinators over the constructors of
-- `Slides.Diagram.Syntax`.  They build the same terms, so every interpretation applies unchanged.
--
-- `Dia` has three associative operations with unit `empty` (`spacer 0 0`):
--
--   a ∥ b   beside (b right of a, centred vertically)      a ∥ ↔ 40 ∥ b   a 40-unit gap
--   a ═ b   above  (b below a, centred horizontally)       (a gap is just a spacer)
--   a ⊙ b   atop   (b on top of a, centred)
--
-- Margins, minimum widths and captions are likewise built from spacers.  What needs a zero or a
-- literal is in `ConvenienceWith 0# fromℕ`; decks use it at ℕ.  Edges are data,
-- `"a" ⟶ "b"`, drawn in order over `d` by `d ▹[ style ] edges`.  Looks come from CSS classes
-- (`cls`), so diagrams restyle with the deck.  Laws: `Slides.Diagram.Convenience.Properties`.

module Slides.Diagram.Convenience where

open import Data.List using (List; []; _∷_; foldl; foldr; map)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Diagram.Style using (Style; defaultStyle; withClass; withId; rounded) public
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

circle : ∀ {S} → S → Style → Dia S
circle = disc

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

-- Looks, boxes and layers

cls : String → Style
cls c = withClass c defaultStyle

-- a rounded box of a CSS class (radius `r`) with a diagram centred on it; the name is for
-- `connect`, and doubles as the element id that scripts light up
card : ∀ {S} → String → String → ℕ → S → S → Dia S → Dia S
card i c r w h d = named i (framed w h (rounded r (withId i (cls c))) d)

-- diagrams of one size laid over each other (the first of the list on top), from an empty one
layers : ∀ {S} → S → S → List (Dia S) → Dia S
layers w h = foldr (λ d acc → overlay w h acc d) (spacer w h)

-- What needs a zero or a literal

module ConvenienceWith {S : Set} (0# : S) (fromℕ : ℕ → S) where
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

  -- text in the slide colour; `dim` a muted caption, `big` a heavier title
  txt dim big : ℕ → String → Dia S
  txt  size t = text size t defaultStyle
  dim  size t = text size t (cls "dim")
  big  size t = bold size t (cls "big")

  -- lines of text, one under the other, centred
  lines : ℕ → List String → Style → Dia S
  lines size ts s = vcat 0# (map (λ t → text size t s) ts)

-- decks compute in ℕ
open ConvenienceWith 0 (λ n → n) public
