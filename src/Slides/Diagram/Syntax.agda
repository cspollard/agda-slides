{-# OPTIONS --safe --without-K #-}

-- The diagram language as a free monad on a container.
--
-- The signature is the sum of three layers:
--
--   * `PrimShape`   the primitives (no sub-diagrams): rectangles, text, …
--   * `Connective`  the combinators that place diagrams relative to each
--                   other: beside, above, atop, margin, …
--   * `Annotation`  names and connections, which do not change the picture's
--                   geometry: `named`, `connect`
--
-- `DiagramC = PrimC ⊎ (ConnectiveC ⊎ AnnotationC)`; a diagram is a closed
-- program `DiagramC ⋆ ⊥`, i.e. a tree of operations (open programs, with
-- variables for holes, substitute with `>>=`).  The smart constructors below
-- are the surface language; nothing is laid out here.  An interpretation of
-- diagrams is an `Algebra`, and `fold` is the catamorphism:
-- `Slides.Diagram.Layout` renders to elements, `Slides.Diagram.Names` checks
-- that every connection refers to a name that exists.

module Slides.Diagram.Syntax where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _+_; _≤ᵇ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String; words; _≟_) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Slides.Diagram using (Style; Element)
open import Slides.Diagram.TextMetrics using (textWidth; spaceWidth)
open import Slides.Diagram.Geometry public
  using (Side; north; south; east; west; middle; Port; side; at; VAlign; top; bottom; Align; left; centred; right)

------------------------------------------------------------------------
-- The signature

data PrimShape : Set where
  -- a rectangle (the style carries the corner radius, class, id, …)
  Rectangle : (w h : ℕ) → Style → PrimShape
  -- a circle of radius r
  Disc      : (r : ℕ) → Style → PrimShape
  -- a line from the top-left to the bottom-right corner of a w × h box
  Segment   : (w h : ℕ) → Style → PrimShape
  -- one line of text at a font size; the measured width is stretched by
  -- `widthPct` percent (a heavier font is wider)
  Text      : (widthPct size : ℕ) → String → Style → PrimShape
  -- empty space of a given size
  Spacer    : (w h : ℕ) → PrimShape
  -- elements in the diagram's own coordinates (paths, curves, …)
  Raw       : (w h : ℕ) → List Element → PrimShape

data Connective : Set where
  Beside     : VAlign → (gap : ℕ) → Connective   -- two children
  Above      : Align → (gap : ℕ) → Connective    -- two children
  Atop       : Connective                         -- two: the second over the first
  -- extra space left, top, right, bottom
  Margin     : (l t r b : ℕ) → Connective        -- one child
  -- at least this wide, the child centred
  MinWidth   : ℕ → Connective                     -- one child
  -- the child at the top of a frame at least this high
  TopAlign   : ℕ → Connective                     -- one child
  -- a label (first child) above / below a diagram (second), a gap away;
  -- empty space of the same size goes on the other side, so the diagram
  -- stays at the centre of the result
  LabelAbove : (gap : ℕ) → Connective             -- two children: label, diagram
  LabelBelow : (gap : ℕ) → Connective

data Annotation : Set where
  -- remember the extent of the child under a name
  Named   : String → Annotation
  -- an arrow from a port of one named box to a port of another
  Connect : String → Port → String → Port → Style → Annotation

arity : Connective → ℕ
arity (Beside _ _)   = 2
arity (Above _ _)    = 2
arity Atop           = 2
arity (Margin _ _ _ _) = 1
arity (MinWidth _)   = 1
arity (TopAlign _)   = 1
arity (LabelAbove _) = 2
arity (LabelBelow _) = 2

PrimC : Container 0ℓ 0ℓ
PrimC = PrimShape ▷ λ _ → ⊥

ConnectiveC : Container 0ℓ 0ℓ
ConnectiveC = Connective ▷ λ c → Fin (arity c)

AnnotationC : Container 0ℓ 0ℓ
AnnotationC = Annotation ▷ λ _ → ⊤

DiagramC : Container 0ℓ 0ℓ
DiagramC = PrimC ⊎ (ConnectiveC ⊎ AnnotationC)

-- A diagram.
Dia : Set
Dia = DiagramC ⋆ ⊥

------------------------------------------------------------------------
-- Interpretation: algebras and the catamorphism

-- One case per layer; the children of a connective are indexed by `Fin (arity c)`.
record Algebra (A : Set) : Set where
  field
    prim       : PrimShape → A
    connective : (c : Connective) → (Fin (arity c) → A) → A
    annotation : Annotation → A → A

open Algebra public

fold : ∀ {A} → Algebra A → Dia → A
fold α (pure ())
fold α (impure (inj₁ p , _))           = prim α p
fold α (impure (inj₂ (inj₁ c) , k))    = connective α c (λ i → fold α (k i))
fold α (impure (inj₂ (inj₂ a) , k))    = annotation α a (fold α (k tt))

------------------------------------------------------------------------
-- The surface language

private
  leaf : PrimShape → Dia
  leaf p = impure (inj₁ p , λ ())

  unary : (a : Annotation) → Dia → Dia
  unary a d = impure (inj₂ (inj₂ a) , λ _ → d)

  pick2 : Dia → Dia → Fin 2 → Dia
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

rectangle : ℕ → ℕ → Style → Dia
rectangle w h s = leaf (Rectangle w h s)

disc : ℕ → Style → Dia
disc r s = leaf (Disc r s)

segment : ℕ → ℕ → Style → Dia
segment w h s = leaf (Segment w h s)

text bold : ℕ → String → Style → Dia
text size t s = leaf (Text 100 size t s)
bold size t s = leaf (Text 108 size t s)

spacer : ℕ → ℕ → Dia
spacer w h = leaf (Spacer w h)

empty : Dia
empty = spacer 0 0

-- the escape hatch: elements with the diagram's own coordinates
raw : ℕ → ℕ → List Element → Dia
raw w h es = leaf (Raw w h es)

-- `a` then `b` to its right / below it, a gap apart
besideA : VAlign → ℕ → Dia → Dia → Dia
besideA al g a b = impure (inj₂ (inj₁ (Beside al g)) , pick2 a b)

aboveA : Align → ℕ → Dia → Dia → Dia
aboveA al g a b = impure (inj₂ (inj₁ (Above al g)) , pick2 a b)

-- centred
beside above : ℕ → Dia → Dia → Dia
beside = besideA middle
above  = aboveA centred

-- put `b` on top of `a`, both centred
atop : Dia → Dia → Dia
atop a b = impure (inj₂ (inj₁ Atop) , pick2 a b)

-- a row / column with a gap between neighbours
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
margin l t r b d = impure (inj₂ (inj₁ (Margin l t r b)) , λ _ → d)

padded : ℕ → Dia → Dia
padded n = margin n n n n

-- at least this wide, the diagram centred (to give columns equal widths)
boxWidth : ℕ → Dia → Dia
boxWidth w d = impure (inj₂ (inj₁ (MinWidth w)) , λ _ → d)

-- the diagram at the top of a frame of the given height (centred
-- horizontally); inside `framed` this lines up contents of different heights
topAligned : ℕ → Dia → Dia
topAligned h d = impure (inj₂ (inj₁ (TopAlign h)) , λ _ → d)

-- a label above or below a diagram, a gap away (the diagram stays centred)
labelAbove labelBelow : ℕ → Dia → Dia → Dia
labelAbove g lbl d = impure (inj₂ (inj₁ (LabelAbove g)) , pick2 lbl d)
labelBelow g lbl d = impure (inj₂ (inj₁ (LabelBelow g)) , pick2 lbl d)

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

-- remember the extent of a diagram under a name
named : String → Dia → Dia
named n = unary (Named n)

-- an arrow from a port of one named box to a port of another
connectP : String → Port → String → Port → Style → Dia → Dia
connectP a pa b pb s = unary (Connect a pa b pb s)

-- … between sides (the middle of an edge)
connect : String → Side → String → Side → Style → Dia → Dia
connect a sa b sb = connectP a (side sa) b (side sb)

-- an arrow from the east edge of one named box to the west edge of another
connectEW : String → String → Style → Dia → Dia
connectEW a b = connect a east b west
