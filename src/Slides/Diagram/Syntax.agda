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
open import Data.Product using (_,_)
open import Data.String using (String; words; _≟_) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Slides.Diagram using (Style)
open import Slides.Diagram.TextMetrics using (textWidth; spaceWidth)
open import Slides.Diagram.Geometry public
  using (Side; north; south; east; west; middle; Port; side; at; VAlign; top; bottom; Align; left; centred; right)

------------------------------------------------------------------------
-- The signature

data Op (S : Set) : Set where
  -- a rectangle (the style carries the corner radius, class, id, …)
  Rectangle : (w h : S) → Style → Op S
  -- a circle of radius r
  Disc      : (r : S) → Style → Op S
  -- a line from the top-left to the bottom-right corner of a w × h box
  Segment   : (w h : S) → Style → Op S
  -- one line of text at a font size; the measured width is stretched by
  -- `widthPct` percent (a heavier font is wider)
  Text      : (widthPct size : ℕ) → String → Style → Op S
  -- empty space of a given size
  Spacer    : (w h : S) → Op S
  -- two children: the second to the right of / below the first, aligned
  Beside    : VAlign → Op S
  Above     : Align → Op S
  -- two children: the second over the first, both centred
  Atop      : Op S
  -- two children, a caption and a diagram: the caption above / below the
  -- diagram, with empty space of the caption's size on the other side, so the
  -- diagram stays at the centre of the result
  LabelAbove LabelBelow : Op S
  -- one child at absolute position (x, y) (units, from the top-left corner) in a frame of
  -- size w × h: no centring, no complement margins.  The caller says where the child goes; the
  -- frame does not grow to fit (a child that sticks out is drawn outside it)
  Place     : (w h x y : S) → Op S
  -- two children in one frame of size w × h, both at its top-left corner, the second drawn
  -- over the first: no centring, so nothing about the size of the children enters the
  -- coordinates (the frame is declared, like a `Spacer`'s)
  Overlay   : (w h : S) → Op S
  -- remember the extent of the child under a name
  Named     : String → Op S
  -- an arrow from a port of one named box to a port of another
  Connect   : String → Port → String → Port → Style → Op S

-- how many sub-diagrams
arity : ∀ {S} → Op S → Set
arity (Rectangle _ _ _) = ⊥
arity (Disc _ _)        = ⊥
arity (Segment _ _ _)   = ⊥
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

private
  pick2 : ∀ {S} → Dia S → Dia S → Fin 2 → Dia S
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

rectangle : ∀ {S} → S → S → Style → Dia S
rectangle w h s = impure (Rectangle w h s , λ ())

disc : ∀ {S} → S → Style → Dia S
disc r s = impure (Disc r s , λ ())

segment : ∀ {S} → S → S → Style → Dia S
segment w h s = impure (Segment w h s , λ ())

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

-- Change of scalar: a diagram with sizes in `S` becomes one with sizes in `T`.
-- This is the action of `Dia` on functions (a fold, rebuilding each operation).
rescale : ∀ {S T} → (S → T) → Algebra S (Dia T)
rescale f (Rectangle w h s)       _ = rectangle (f w) (f h) s
rescale f (Disc r s)              _ = disc (f r) s
rescale f (Segment w h s)         _ = segment (f w) (f h) s
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

