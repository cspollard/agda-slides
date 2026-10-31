{-# OPTIONS --safe --without-K #-}

-- Clipping a polyline to a box in data space (Liang-Barsky): a curve that leaves the range is cut
-- where it crosses the edge, not flattened onto it.  `clipLine` gives the pieces inside, each an
-- open polyline; consecutive segments that stay inside stay one piece.
--
-- A segment `a → b` is `a + t (b − a)`, t in [0, 1]; each edge of the box bounds t from one side
-- (`edge p q`: `p t ≤ q`).  A segment that misses the box gives nothing.  Checked on closed values
-- below; that every point lies in the box is `clipLine-inside`.

module Slides.Plot.Clip where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _++_; reverse; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.Rational.Properties as ℚP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤ᵇ_; _⊔_; _⊓_; -_)

open import Slides.Plot.Data using (inv; lt)

private
  P : Set
  P = ℚ × ℚ

  -- bound t by the edge `p t ≤ q`
  edge : ℚ → ℚ → ℚ × ℚ → Maybe (ℚ × ℚ)
  edge p q (t₀ , t₁) =
    if (p ≤ᵇ 0ℚ) ∧ (0ℚ ≤ᵇ p)
      then (if lt q 0ℚ then nothing else just (t₀ , t₁))
      else (if lt p 0ℚ
        then (if lt t₁ r then nothing else just (t₀ ⊔ r , t₁))
        else (if lt r t₀ then nothing else just (t₀ , t₁ ⊓ r)))
    where r = q * inv p

  bind : {B : Set} → Maybe (ℚ × ℚ) → (ℚ × ℚ → Maybe B) → Maybe B
  bind nothing  f = nothing
  bind (just t) f = f t

-- the part of `a → b` inside the box: its end points, and whether each was moved
clipSeg : (xlo xhi ylo yhi : ℚ) → P → P → Maybe (P × P × Bool × Bool)
clipSeg xlo xhi ylo yhi (x₀ , y₀) (x₁ , y₁) =
  bind (edge (- dx) (x₀ - xlo) (0ℚ , 1ℚ)) λ t →
  bind (edge dx (xhi - x₀) t)             λ t →
  bind (edge (- dy) (y₀ - ylo) t)         λ t →
  bind (edge dy (yhi - y₀) t)             λ { (t₀ , t₁) →
    just ((x₀ + t₀ * dx , y₀ + t₀ * dy) , (x₀ + t₁ * dx , y₀ + t₁ * dy) , lt 0ℚ t₀ , lt t₁ 1ℚ) }
  where dx = x₁ - x₀
        dy = y₁ - y₀

cut : (xlo xhi ylo yhi : ℚ) → List P → List (List P)
cut xlo xhi ylo yhi []        = []
cut xlo xhi ylo yhi (a ∷ ps) = walk a ps []
  where
    -- a piece is kept if it has two points; `cur` is the open piece, reversed
    flush : List P → List (List P)
    flush (p ∷ q ∷ r) = reverse (p ∷ q ∷ r) ∷ []
    flush _           = []

    extend : List P → P → P → List P
    extend [] s e = e ∷ s ∷ []
    extend cur s e = e ∷ cur

    walk : P → List P → List P → List (List P)
    walk a []         cur = flush cur
    walk a (b ∷ rest) cur with clipSeg xlo xhi ylo yhi a b
    ... | nothing                     = flush cur ++ walk b rest []
    ... | just (s , e , sMoved , eMoved) =
          let cur′ = if sMoved then [] else cur
              new  = extend cur′ s e
          in (if sMoved then flush cur else []) ++
             (if eMoved then flush new ++ walk b rest [] else walk b rest new)

-- Every point is clamped to the box at the end.  Where `cut` is right this moves nothing (the ends
-- of a clipped segment are on the edge, in ℚ exactly), and it makes `clipLine-inside` hold by
-- construction; that `cut` is faithful (pieces, ends) is what the closed checks below look at.
clampP : (xlo xhi ylo yhi : ℚ) → P → P
clampP xlo xhi ylo yhi (x , y) = xlo ⊔ (x ⊓ xhi) , ylo ⊔ (y ⊓ yhi)

clipLine : (xlo xhi ylo yhi : ℚ) → List P → List (List P)
clipLine xlo xhi ylo yhi ps = map (map (clampP xlo xhi ylo yhi)) (cut xlo xhi ylo yhi ps)

InBox : (xlo xhi ylo yhi : ℚ) → P → Set
InBox xlo xhi ylo yhi (x , y) = (xlo ℚ.≤ x × x ℚ.≤ xhi) × (ylo ℚ.≤ y × y ℚ.≤ yhi)

private
  all-map : ∀ {A B : Set} {Q : B → Set} (f : A → B) → (∀ x → Q (f x)) → ∀ xs → All Q (map f xs)
  all-map f q []       = []
  all-map f q (x ∷ xs) = q x ∷ all-map f q xs

clipLine-inside : ∀ {xlo xhi ylo yhi} → xlo ℚ.≤ xhi → ylo ℚ.≤ yhi → ∀ ps →
                  All (All (InBox xlo xhi ylo yhi)) (clipLine xlo xhi ylo yhi ps)
clipLine-inside {xlo} {xhi} {ylo} {yhi} lx ly ps =
  all-map (map (clampP xlo xhi ylo yhi)) (λ piece → all-map (clampP xlo xhi ylo yhi) inside piece) (cut xlo xhi ylo yhi ps)
  where
    inside : ∀ p → InBox xlo xhi ylo yhi (clampP xlo xhi ylo yhi p)
    inside (x , y) = (ℚP.p≤p⊔q xlo (x ⊓ xhi) , ℚP.⊔-lub lx (ℚP.p⊓q≤q x xhi))
                   , (ℚP.p≤p⊔q ylo (y ⊓ yhi) , ℚP.⊔-lub ly (ℚP.p⊓q≤q y yhi))

-- closed checks, in the box [0, 10] × [0, 10]
private
  open import Data.Integer using (+_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  q : ℕ → ℚ
  q n = + n ℚ./ 1

  -- inside: unchanged; across the right edge: cut at x = 10; wholly outside: nothing
  _ : clipLine (q 0) (q 10) (q 0) (q 10) ((q 1 , q 1) ∷ (q 3 , q 5) ∷ []) ≡ ((q 1 , q 1) ∷ (q 3 , q 5) ∷ []) ∷ []
  _ = refl
  _ : clipLine (q 0) (q 10) (q 0) (q 10) ((q 5 , q 5) ∷ (q 15 , q 5) ∷ []) ≡ ((q 5 , q 5) ∷ (q 10 , q 5) ∷ []) ∷ []
  _ = refl
  _ : clipLine (q 0) (q 10) (q 0) (q 10) ((q 11 , q 1) ∷ (q 12 , q 3) ∷ []) ≡ []
  _ = refl
  -- out and back in: two pieces
  _ : length (clipLine (q 0) (q 10) (q 0) (q 10) ((q 2 , q 2) ∷ (q 5 , q 14) ∷ (q 8 , q 2) ∷ [])) ≡ 2
  _ = refl
