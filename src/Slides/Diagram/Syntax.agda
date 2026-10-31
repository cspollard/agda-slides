{-# OPTIONS --safe --without-K #-}

-- The diagram language: the free monad `Dia S = DiagramC S ⋆ ⊥` of the layout signature over a
-- scalar `S`.
--
-- `Op S` is the signature: *primitives* (no sub-diagram, a frame of intrinsic size), *connectives*
-- (place the frames of their children relative to each other) and *annotations* (`Named`,
-- `Connect`: the geometry is the child's).  An interpretation is a `Handler` read by `pfold`
-- (`Layout`, `Names`, `Size`); the size of a composite is synthesised, never stored.  A map of
-- scalars acts by the container morphism `mapC` (`mapDia`).
--
-- Conventions: origin at the top-left of a frame, x right, y DOWN.  A frame is all a neighbour
-- sees.  A connective never scales a child, it shifts it inside a new frame; of two children the
-- second is drawn on top.  Sizes are in units, positions in half units (centring is a difference
-- of sizes, no division).
--
--     Rectangle w h   Disc r        Segment w h   Text w h     Path w h      Spacer w h
--     +-------+       +-----+       *             +--------+   +-------+     +       +
--     |       | h     | ( ) | 2r    | \           |  text  |   | d ... |
--     +-------+       +-----+       +--*          +--------+   +-------+     +       +
--
--     Ellipse rx ry   Polyline closed pts
--     +---------+     +-----------+   frame: the extent of the points from the origin
--     |  ( _ )  | 2ry |  p2       |   (largest x by largest y; no points, the empty frame).
--     +---------+     | p1  p3    |   Unlike `Path`, whose `d` is opaque, the points are
--      2rx            +-----------+   scalars, so they move with `mapDia` and animation time.
--
--     `Disc r` has the size of `Ellipse r r` (`size-disc-ellipse`) and prints as `<circle>`.
--
--     Beside al        Above al      Atop          LabelAbove       Place w h x y  Overlay w h
--     +--+--+          +--+          +----------+  +-----+          +----------+   +-------+
--     |a |b |          |a |          |  +----+  |  | lbl |          |  (x,y)+-+|   | a   b |
--     +--+--+          +--+--+       |  | b  |  |  +-----+          |       |d||   +-------+
--                      | b   |      +----------+  |  d  | (room of  +----------+
--                      +-----+                    +-----+  lbl below)
--
--     Named n d: the frame of d under the name n      Connect a pa b pb d: an arrow a → b over d

module Slides.Diagram.Syntax where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; map; length)
open import Data.Nat using (ℕ; _*_; _/_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; trans; sym)
open import Data.Container.Core using (Container; _⇒_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Container.Pick using (pick2)
open import Container.Lowering using (translate)
open import Container.Tagged using (Tagged; over)
open import Slides.Diagram.Style using (Style; anchored)
open import Slides.Diagram.Draw using (mapPt)
open import Slides.Diagram.TextMetrics using (inlineWidth)
open import Slides.Text using (Inline; parse; lines)
open import Slides.Diagram.Geometry public

-- A command is a tag and a payload.  The payload of a tag is described by `Fields`, so that scalars
-- are found by structure (`fmap`) and the arity of a tag does not depend on the scalar.

infixr 5 _⊗_
data Fields : Set₁ where
  scalar : Fields
  const  : Set → Fields
  ptList : Fields                 -- points of scalars
  _⊗_    : Fields → Fields → Fields

⟦_⟧ : Fields → Set → Set
⟦ scalar ⟧  S = S
⟦ const X ⟧ S = X
⟦ ptList ⟧  S = List (S × S)
⟦ A ⊗ B ⟧   S = ⟦ A ⟧ S × ⟦ B ⟧ S

fmap : ∀ {S T} → (S → T) → ∀ A → ⟦ A ⟧ S → ⟦ A ⟧ T
fmap f scalar    x = f x
fmap f (const _) x = x
fmap f ptList   ps = map (mapPt f) ps
fmap f (A ⊗ B)   p = fmap f A (proj₁ p) , fmap f B (proj₂ p)

fmap-id : ∀ {S} A (p : ⟦ A ⟧ S) → fmap id A p ≡ p
fmap-id scalar    _ = refl
fmap-id (const _) _ = refl
fmap-id ptList   ps = trans (ListP.map-cong (λ _ → refl) ps) (ListP.map-id ps)
fmap-id (A ⊗ B)   p = cong₂ _,_ (fmap-id A _) (fmap-id B _)

fmap-∘ : ∀ {S T U} (g : T → U) (f : S → T) A (p : ⟦ A ⟧ S) → fmap g A (fmap f A p) ≡ fmap (g ∘ f) A p
fmap-∘ g f scalar    _ = refl
fmap-∘ g f (const _) _ = refl
fmap-∘ g f ptList   ps = trans (sym (ListP.map-∘ ps)) (ListP.map-cong (λ _ → refl) ps)
fmap-∘ g f (A ⊗ B)   p = cong₂ _,_ (fmap-∘ g f A _) (fmap-∘ g f B _)

data Tag : Set where
  rectT segT discT ellipseT polylineT textT pathT spacerT : Tag
  besideT aboveT atopT labelAboveT labelBelowT placeT overlayT namedT connectT : Tag

fields : Tag → Fields
fields rectT       = scalar ⊗ scalar ⊗ const Style
fields segT        = scalar ⊗ scalar ⊗ const Style
fields discT       = scalar ⊗ const Style
fields ellipseT    = scalar ⊗ scalar ⊗ const Style
fields polylineT   = const Bool ⊗ ptList ⊗ const Style      -- points from the frame's top-left
fields textT       = scalar ⊗ scalar ⊗ const ℕ ⊗ const (List Inline) ⊗ const Style   -- frame as measured
fields pathT       = scalar ⊗ scalar ⊗ const String ⊗ const Style   -- opaque `d` in the frame's units: not scalar-parametric
fields spacerT     = scalar ⊗ scalar
fields besideT     = const VAlign
fields aboveT      = const Align
fields atopT       = const ⊤
fields labelAboveT = const ⊤
fields labelBelowT = const ⊤
fields placeT      = scalar ⊗ scalar ⊗ scalar ⊗ scalar     -- one child at (x, y) of a declared frame
fields overlayT    = scalar ⊗ scalar                       -- two children at the corner of a declared frame
fields namedT      = const String
fields connectT    = const String ⊗ const Port ⊗ const String ⊗ const Port ⊗ const Style

arity : Tag → Set
arity rectT       = ⊥
arity segT        = ⊥
arity discT       = ⊥
arity ellipseT    = ⊥
arity polylineT   = ⊥
arity textT       = ⊥
arity pathT       = ⊥
arity spacerT     = ⊥
arity besideT     = Fin 2
arity aboveT      = Fin 2
arity atopT       = Fin 2
arity labelAboveT = Fin 2
arity labelBelowT = Fin 2
arity placeT      = ⊤
arity overlayT    = Fin 2
arity namedT      = ⊤
arity connectT    = ⊤

Payload : Tag → Set → Set
Payload t = ⟦ fields t ⟧

Op : Set → Set
Op S = Σ Tag (λ t → Payload t S)

pattern Rectangle w h s       = rectT , w , h , s
pattern Segment w h s         = segT , w , h , s
pattern Disc r s              = discT , r , s
pattern Ellipse a b s         = ellipseT , a , b , s
pattern Polyline c ps s       = polylineT , c , ps , s
pattern Text w h n t s        = textT , w , h , n , t , s
pattern Path w h d s          = pathT , w , h , d , s
pattern Spacer w h            = spacerT , w , h
pattern Beside al             = besideT , al
pattern Above al              = aboveT , al
pattern Atop                  = atopT , tt
pattern LabelAbove            = labelAboveT , tt
pattern LabelBelow            = labelBelowT , tt
pattern Place w h x y         = placeT , w , h , x , y
pattern Overlay w h           = overlayT , w , h
pattern Named n               = namedT , n
pattern Connect a pa b pb s   = connectT , a , pa , b , pb , s

DiagramC : Set → Container 0ℓ 0ℓ
DiagramC S = Tagged arity (λ t → Payload t S)

Dia : Set → Set
Dia S = DiagramC S ⋆ ⊥

-- Change of scalar: the action on maps, a container morphism with the identity on positions

mapOp : ∀ {S T} → (S → T) → Op S → Op T
mapOp f (t , p) = t , fmap f (fields t) p

mapC : ∀ {S T} → (S → T) → DiagramC S ⇒ DiagramC T
mapC f = over arity (λ t → fmap f (fields t))

mapDia : ∀ {S T} → (S → T) → Dia S → Dia T
mapDia f = translate (mapC f)

-- The surface language

rectangle segment : ∀ {S} → S → S → Style → Dia S
rectangle w h s = impure (Rectangle w h s , λ ())
segment w h s   = impure (Segment w h s , λ ())

disc : ∀ {S} → S → Style → Dia S
disc r s = impure (Disc r s , λ ())

ellipse : ∀ {S} → S → S → Style → Dia S
ellipse a b s = impure (Ellipse a b s , λ ())

-- through the points (from the top-left corner), open or closed
polyline polygon : ∀ {S} → List (S × S) → Style → Dia S
polyline ps s = impure (Polyline false ps s , λ ())
polygon ps s  = impure (Polyline true ps s , λ ())

spacer : ∀ {S} → S → S → Dia S
spacer w h = impure (Spacer w h , λ ())

path : ∀ {S} → S → S → String → Style → Dia S
path w h d s = impure (Path w h d s , λ ())

-- a line of text at a font size: as wide as its characters times `pct` percent (a heavier
-- font is wider), `size * 3/2` high; `fromℕ` reads a number of units as a length
textI : ∀ {S} → (ℕ → S) → (pct size : ℕ) → List Inline → Style → Dia S
textI fromℕ pct size is s =
  impure (Text (fromℕ ((inlineWidth size is * pct) / 100)) (fromℕ (((size * 3) / 2) * length (lines is))) size is s , λ ())

-- the same for a label written with markup (`Slides.Text.parse`)
text : ∀ {S} → (ℕ → S) → (pct size : ℕ) → String → Style → Dia S
text fromℕ pct size t = textI fromℕ pct size (parse t)

-- a line of text in a frame of no width, anchored (at its "start", "middle" or "end") on the point
-- it is placed at, so that its place does not depend on the width the page's font gives it
textAt : ∀ {S} → S → (ℕ → S) → String → (size : ℕ) → String → Style → Dia S
textAt 0# fromℕ a size t s =
  impure (Text 0# (fromℕ ((size * 3) / 2)) size (parse t) (anchored a s) , λ ())

besideA : ∀ {S} → VAlign → Dia S → Dia S → Dia S
besideA al a b = impure (Beside al , pick2 a b)

aboveA : ∀ {S} → Align → Dia S → Dia S → Dia S
aboveA al a b = impure (Above al , pick2 a b)

beside above atop labelAbove labelBelow : ∀ {S} → Dia S → Dia S → Dia S
beside = besideA middle
above  = aboveA centred
atop a b       = impure (Atop , pick2 a b)
labelAbove l d = impure (LabelAbove , pick2 l d)    -- caption, diagram, room of the caption's height
labelBelow l d = impure (LabelBelow , pick2 l d)    -- the diagram is at the centre either way

overlay : ∀ {S} → S → S → Dia S → Dia S → Dia S
overlay w h a b = impure (Overlay w h , pick2 a b)

place : ∀ {S} → S → S → S → S → Dia S → Dia S
place w h x y d = impure (Place w h x y , λ _ → d)

named : ∀ {S} → String → Dia S → Dia S
named n d = impure (Named n , λ _ → d)

connectP : ∀ {S} → String → Port → String → Port → Style → Dia S → Dia S
connectP a pa b pb s d = impure (Connect a pa b pb s , λ _ → d)

connect : ∀ {S} → String → Side → String → Side → Style → Dia S → Dia S
connect a sa b sb = connectP a (side sa) b (side sb)

-- a rectangle with a diagram centred on it
framed : ∀ {S} → S → S → Style → Dia S → Dia S
framed w h s d = atop (rectangle w h s) d
