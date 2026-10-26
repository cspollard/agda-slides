{-# OPTIONS --safe --without-K #-}

-- The drifting point pairs behind the title and closing slides of the Pairs deck,
-- as a loop (`Slides.Anim.Loop`): each pair is two dots joined by a line; over one
-- period of `period` frames a pair turns through a half turn (the pair is unordered)
-- and sways to and fro along a fixed direction, a triangle wave, so the last frame
-- runs into the first and nothing jumps.  The pairs are a deterministic function of
-- a seed (a linear congruential generator), so the output is reproducible.
--
-- The frame is written *once*, over any scalar with the three layers of
-- `Slides.Diagram.Euclid` (`Frame`: sum, monus, maximum, floor division, remainder, comparison
-- and a literal factor), with the tick `t` a scalar.  At ℕ it is the frame the flipbook shows
-- (`heroAt`, `hero`); over the free algebra `DExpr ⊤`, with `t` the variable, it is a *discrete
-- template* (`heroT`, `heroD`): the pairs' data are literals (partially evaluated by Agda: a
-- constant spin makes the angle a number, and the closed subformulas fold), and only the tick
-- stays symbolic.  Nothing is written twice, and the template is the frame by naturality of
-- the construction along the evaluation homomorphism (`Slides.Examples.PairsHeroNatural`,
-- `heroT-correct`).

module Slides.Examples.PairsHero where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; zipWith; upTo; foldr)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _%_; _/_; _<ᵇ_; NonZero)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Integer using (+_)
import Data.Rational as ℚ
open import Data.Unit using (⊤)

open import Slides.Diagram using (Style; withClass; defaultStyle)
open import Slides.Diagram.Syntax using (Dia; disc; named; connect; spacer; place; overlay)
open import Slides.Diagram.Notation using (side; east; west)
import Slides.Diagram.Notation as N
open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Euclid using (DiscreteOps; natD; DExpr; dexprD; tickD; EuclidOps)
open import Slides.Anim.Syntax using (Anim; Seg; tween; tweenD; units)
import Slides.Anim.Track as T

W H period : ℕ
W = 1280
H = 720
period = 64

------------------------------------------------------------------------
-- The pairs

-- a pair: centre, radius, starting angle (of 8 over a half turn), spin (-1, 0, 1 as 0, 1, 2),
-- sway amplitude and direction, and a colour
record Pair : Set where
  field
    cx cy radius angle spin amp : ℕ
    swayX swayY blue : Bool

-- the next pseudo-random number
next : ℕ → ℕ
next s = (s * 1103515245 + 12345) % 2147483648

-- `k` pairs from a seed
pairs : ℕ → ℕ → List Pair
pairs zero    s = []
pairs (suc k) s = p ∷ pairs k s₉
  where
    s₁ = next s; s₂ = next s₁; s₃ = next s₂; s₄ = next s₃; s₅ = next s₄
    s₆ = next s₅; s₇ = next s₆; s₈ = next s₇; s₉ = next s₈
    pick : ℕ → ℕ → (n : ℕ) → {{_ : NonZero n}} → ℕ
    pick seed lo n = lo + (seed / 65536) % n
    p = record
      { cx = pick s₁ 130 1020; cy = pick s₂ 110 500; radius = pick s₃ 26 60
      ; angle = pick s₄ 0 8; spin = pick s₅ 0 3; amp = pick s₆ 20 36
      ; swayX = pick s₇ 0 2 <ᵇ 1; swayY = pick s₈ 0 2 <ᵇ 1; blue = pick s₉ 0 2 <ᵇ 1 }

------------------------------------------------------------------------
-- A frame, over any scalar

-- the lookup table of 8 entries by the angle: `sel i xs a` is `xs !! (a - i)`, the last entry
-- for all larger `a`
tabX tabY : List ℕ
tabX = 100 ∷ 92 ∷ 71 ∷ 38 ∷ 0 ∷ 38 ∷ 71 ∷ 92 ∷ []
tabY = 0 ∷ 38 ∷ 71 ∷ 92 ∷ 100 ∷ 92 ∷ 71 ∷ 38 ∷ []

module Frame {S : Set} (D : DiscreteOps S) where
  private
    O = DiscreteOps.ops D
    Eu = DiscreteOps.euclid D
  open Ops O renaming (_+_ to _⊕_; _-_ to _⊖_; fromℕ to lit)
  open EuclidOps Eu

  sel : ℕ → List ℕ → S → S
  sel i []           a = lit 0
  sel i (x ∷ [])     a = lit x
  sel i (x ∷ y ∷ xs) a = lt a (lit (suc i)) (lit x) (sel (suc i) (y ∷ xs) a)

  -- the direction of angle `i` of 8: |dx|, |dy| in hundredths (the lines through it rise to the
  -- right for the angles 5, 6, 7, so that "left" is the lower end)
  dirX dirY : S → S
  dirX = sel 0 tabX
  dirY = sel 0 tabY

  -- the triangle wave: 0 up to 32 and back down over a period
  tri : S → S
  tri t = let m = modBy 63 t in lt m (lit 33) m (lit period ⊖ m)

  -- a dot of radius `r` with its top left corner at (x, y), on a layer of the canvas's size
  -- (`place`: absolute position, a frame of declared size)
  dot : String → String → ℕ → S → S → Dia S
  dot name cls r x y =
    place (lit W) (lit H) x y (named name (disc (lit r) (withClass cls defaultStyle)))

  -- the quantities of one pair at tick `t`
  record At (p : Pair) (t : S) : Set where
    open Pair p
    field
      ang dx dy d ox oy lx rx ly ry : S

  -- the angle turns by `spin - 1` steps every four frames
  angle′ : Pair → S → S
  angle′ p t = modBy 7 (lit (Pair.angle p) ⊕ spin′)
    where
      q = modBy 7 (divBy 3 t)
      spin′ = if Pair.spin p <ᵇ 1 then lit 8 ⊖ q else if Pair.spin p <ᵇ 2 then lit 0 else q

  -- the sway: along x and y by `amp * tri t / 32`
  swayD : Pair → S → S
  swayD p t = divBy 31 (mulLit (Pair.amp p) (tri t))

  at : (p : Pair) (t : S) → At p t
  at p t = record
    { ang = a ; dx = dx ; dy = dy ; d = d ; ox = ox ; oy = oy
    ; lx = ox ⊖ dx ; rx = ox ⊕ dx
    ; ly = lt a (lit 5) (oy ⊖ dy) (oy ⊕ dy) ; ry = lt a (lit 5) (oy ⊕ dy) (oy ⊖ dy) }
    where
      open Pair p using (cx; cy; radius; amp; swayX; swayY)
      a  = angle′ p t
      dx = divBy 99 (mulLit radius (dirX a))
      dy = divBy 99 (mulLit radius (dirY a))
      d  = swayD p t
      ox = lit (cx ∸ amp) ⊕ (if swayX then d else lit amp ⊖ d)
      oy = lit (cy ∸ amp) ⊕ (if swayY then d else lit amp ⊖ d)

  -- one pair at tick `t`
  pairAt : S → ℕ → Pair → Dia S
  pairAt t i p = connect ("a" ++ˢ si) east ("b" ++ˢ si) west (withClass "hero-link" defaultStyle)
                   (overlay (lit W) (lit H)
                      (dot ("a" ++ˢ si) col 5 (At.lx v ⊖ lit 5) (At.ly v ⊖ lit 5))
                      (dot ("b" ++ˢ si) col 5 (At.rx v ⊖ lit 5) (At.ry v ⊖ lit 5)))
    where
      si  = show i
      col = if Pair.blue p then "hero-b" else "hero-r"
      v   = at p t

  -- the whole picture at tick `t`: every pair on a layer of the canvas's size, the layers
  -- overlaid in a frame of that size
  -- (`n` pairs: the deck uses 26)
  heroFrame : (n seed : ℕ) → S → Dia S
  heroFrame n seed t = foldr (overlay (lit W) (lit H)) (spacer (lit W) (lit H)) (zipWith (pairAt t) (upTo n) (pairs n seed))

-- the frame the flipbook shows
heroAt : (seed : ℕ) → ℕ → Dia ℕ
heroAt = Frame.heroFrame natD 26

-- one period of the sway and spin, played as a loop
hero : ℕ → Anim ℕ (Seg ℕ)
hero seed = tween period (+ 0 ℚ./ 1) (+ period ℚ./ 1) T.Linear (λ q → heroAt seed (units q))

-- the same frame over the free algebra, with the tick as the variable: a discrete template
-- (`n` pairs).  The frame is an overlay of placed dots on a canvas of declared size (`dot`,
-- `pairAt`, `heroFrame`), so no coordinate depends on the size of another element: the symbolic
-- layout is linear in `n` (placing each pair by margins against `W - (x + 2r)` and centring the
-- layers against the maximum of their widths made it cubic: 779 KB of formulas for 3 pairs, see
-- `docs/Design.md`), and the formulas of a phase are shared when shipped (`Slides.Anim.Share`)
heroT : (n seed : ℕ) → Dia (DExpr ⊤)
heroT n seed = Frame.heroFrame dexprD n seed tickD

-- the same loop shipped as formulas
heroD : (n seed : ℕ) → Anim ℕ (Seg ℕ)
heroD n seed = tweenD period (+ 0 ℚ./ 1) (+ period ℚ./ 1) T.Linear (heroT n seed)
