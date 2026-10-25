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
-- `a ∥ ↔ 40 ∥ b` needs no gap parameter and chains without nesting.  There is
-- no interchange law between `∥` and `═`: `(a ∥ b) ═ (c ∥ d)` and
-- `(a ═ c) ∥ (b ═ d)` align their columns differently.
--
-- Edges are data, `"a" ⟶ "b"`, and `d ▹[ style ] edges` draws a list of them,
-- in order, over `d`.

module Slides.Diagram.Notation where

open import Data.List using (List; []; _∷_; foldl)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Diagram using (Style)
open import Slides.Diagram.Syntax public

------------------------------------------------------------------------
-- Composition

infixr 8 _⊙_
infixr 7 _∥_
infixr 6 _═_

_∥_ _═_ _⊙_ : Dia → Dia → Dia
_∥_ = besideA middle 0
_═_ = aboveA centred 0
_⊙_ = atop

-- the same, aligned: `∥↑ ∥↓` to the top or bottom, `═◂ ═▸` left or right
infixr 7 _∥↑_ _∥↓_
infixr 6 _═◂_ _═▸_

_∥↑_ _∥↓_ _═◂_ _═▸_ : Dia → Dia → Dia
_∥↑_ = besideA top 0
_∥↓_ = besideA bottom 0
_═◂_ = aboveA left 0
_═▸_ = aboveA right 0

-- empty space
↔ ↕ : ℕ → Dia
↔ n = spacer n 0
↕ n = spacer 0 n

-- a row / column of diagrams a given gap apart
⟨_⟩ₕ_ ⟨_⟩ᵥ_ : List Dia → ℕ → Dia
⟨ ds ⟩ₕ g = hcat g ds
⟨ ds ⟩ᵥ g = vcat g ds

------------------------------------------------------------------------
-- Names and captions

infixr 4 _⦂_

-- `"id" ⦂ d`: remember the extent of `d` under a name
_⦂_ : String → Dia → Dia
_⦂_ = named

-- `d ⌄[ g ] lbl` puts a caption a gap below `d`, `lbl ⌃[ g ] d` above it
infixl 9 _⌄[_]_ _⌃[_]_

_⌄[_]_ : Dia → ℕ → Dia → Dia
d ⌄[ g ] lbl = labelBelow g lbl d

_⌃[_]_ : Dia → ℕ → Dia → Dia
lbl ⌃[ g ] d = labelAbove g lbl d

------------------------------------------------------------------------
-- Edges

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
  draw : Style → Dia → Edge → Dia
  draw s d (edge (a ⊢ pa) (b ⊢ pb)) = connectP a pa b pb s d

infixl 3 _▹[_]_ _▹_∶_

-- draw edges in a style, the first one first (later ones on top)
_▹[_]_ : Dia → Style → List Edge → Dia
d ▹[ s ] es = foldl (draw s) d es

-- one edge
_▹_∶_ : Dia → Edge → Style → Dia
d ▹ e ∶ s = d ▹[ s ] (e ∷ [])
