{-# OPTIONS --safe --without-K #-}

-- Time dependence of paint quantities, as explicit data.
--
-- A *track* is a program in the free monad on the one-operation container `Seq`
-- (two children) whose leaves are *pieces*: for a number of ticks, move from a
-- value to a value along an easing.  `sample` interprets a track as an algebra
-- into `Sampled A`, a length and a function of the tick; sequencing a track is
-- `seqS`, which switches function at the boundary.  Interpolation is passed in
-- (`Lerp A`, with its two endpoint laws), not found by instance search.
--
-- Semantics.  Pieces are half-open, so evaluation is total and right-continuous:
-- at a boundary the *new* piece's start value holds, and a track holds its last
-- value after its end.  Every easing fixes 0 and 1 (`progress-0`, `progress-1`),
-- hence a piece starts at its `from` and ends at its `to`.
--
-- Proved: the endpoint laws, associativity of `seqS` (pointwise, so no function
-- extensionality), `reverse` as a fold and its involution, the involution on
-- easings (the time-reverse of `cubic-bezier(x₁,y₁,x₂,y₂)` is
-- `cubic-bezier(1-x₂,1-y₂,1-x₁,1-y₁)`).  `Bezier` is evaluated by bisection to a
-- fixed number of steps: an approximation, but one that keeps the endpoint laws.

module Slides.Anim.Track where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Properties as ℚP
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
import Data.Nat.Properties as ℕP
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Easings

-- `Bezier` takes control points in hundredths (`Bezier 40 0 20 100` is CSS's
-- `cubic-bezier(.4, 0, .2, 1)`); `Step` jumps at the end of a piece, `StepStart`
-- at its start (CSS `step-end`, `step-start`)
data Easing : Set where
  Linear Step StepStart : Easing
  Bezier : (x₁ y₁ x₂ y₂ : ℤ) → Easing

-- an easing run backwards
reverseE : Easing → Easing
reverseE Linear           = Linear
reverseE Step             = StepStart
reverseE StepStart        = Step
reverseE (Bezier a b c d) = Bezier (ℤ.+ 100 ℤ.- c) (ℤ.+ 100 ℤ.- d) (ℤ.+ 100 ℤ.- a) (ℤ.+ 100 ℤ.- b)

private
  inv : ∀ x → ℤ.+ 100 ℤ.- (ℤ.+ 100 ℤ.- x) ≡ x
  inv = solve-∀
    where open import Data.Integer.Tactic.RingSolver

reverseE-invol : ∀ e → reverseE (reverseE e) ≡ e
reverseE-invol Linear           = refl
reverseE-invol Step             = refl
reverseE-invol StepStart        = refl
reverseE-invol (Bezier a b c d) rewrite inv a | inv b | inv c | inv d = refl

------------------------------------------------------------------------
-- Progress: how far along the piece, after easing

private
  _≤ᵇ_ = ℚ._≤ᵇ_
  infixl 6 _⊕_ _⊖_
  infixl 7 _⊗_
  _⊕_ _⊖_ _⊗_ : ℚ → ℚ → ℚ
  _⊕_ = ℚ._+_
  _⊖_ = ℚ._-_
  _⊗_ = ℚ._*_

  hundredths : ℤ → ℚ
  hundredths n = n ℚ./ 100

  three half : ℚ
  three = ℤ.+ 3 ℚ./ 1
  half  = ℤ.+ 1 ℚ./ 2

  -- the cubic Bézier coordinate with end points 0 and 1
  cubic : ℚ → ℚ → ℚ → ℚ
  cubic c₁ c₂ s =
    three ⊗ (1ℚ ⊖ s) ⊗ (1ℚ ⊖ s) ⊗ s ⊗ c₁ ⊕ three ⊗ (1ℚ ⊖ s) ⊗ s ⊗ s ⊗ c₂ ⊕ s ⊗ s ⊗ s

  -- the parameter `s` with `x(s) = p`, by `n` bisection steps from `[lo, hi]`
  bisect : ℕ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
  bisect ℕ.zero    x₁ x₂ lo hi p = half ⊗ (lo ⊕ hi)
  bisect (ℕ.suc n) x₁ x₂ lo hi p =
    let mid = half ⊗ (lo ⊕ hi) in
    if cubic x₁ x₂ mid ≤ᵇ p then bisect n x₁ x₂ mid hi p else bisect n x₁ x₂ lo mid p

-- `p` in `[0, 1]` to the eased progress, fixing both ends.  `Bezier` is
-- approximate (sixteen bisection steps); the clamping makes the end points exact.
progress : Easing → ℚ → ℚ
progress Linear    p = p
progress Step      p = if 1ℚ ≤ᵇ p then 1ℚ else 0ℚ
progress StepStart p = if p ≤ᵇ 0ℚ then 0ℚ else 1ℚ
progress (Bezier a b c d) p =
  if p ≤ᵇ 0ℚ then 0ℚ
  else if 1ℚ ≤ᵇ p then 1ℚ
  else cubic (hundredths b) (hundredths d) (bisect 16 (hundredths a) (hundredths c) 0ℚ 1ℚ p)

progress-0 : ∀ e → progress e 0ℚ ≡ 0ℚ
progress-0 Linear           = refl
progress-0 Step             = refl
progress-0 StepStart        = refl
progress-0 (Bezier a b c d) = refl

progress-1 : ∀ e → progress e 1ℚ ≡ 1ℚ
progress-1 Linear           = refl
progress-1 Step             = refl
progress-1 StepStart        = refl
progress-1 (Bezier a b c d) = refl

------------------------------------------------------------------------
-- Interpolation

-- `lerp p a b` moves from `a` (at `p = 0`) to `b` (at `p = 1`); a type with no
-- interpolation uses `holdLerp` and only the `Step` easings.
record Lerp (A : Set) : Set where
  field
    lerp   : ℚ → A → A → A
    lerp-0 : ∀ a b → lerp 0ℚ a b ≡ a
    lerp-1 : ∀ a b → lerp 1ℚ a b ≡ b

holdLerp : ∀ {A} → Lerp A
holdLerp = record
  { lerp = λ p a b → if 1ℚ ≤ᵇ p then b else a ; lerp-0 = λ _ _ → refl ; lerp-1 = λ _ _ → refl }

-- `a + p (b - a)`
ℚLerp : Lerp ℚ
ℚLerp = record
  { lerp   = λ p a b → a ⊕ p ⊗ (b ⊖ a)
  ; lerp-0 = λ a b → trans (cong (a ⊕_) (ℚP.*-zeroˡ (b ⊖ a))) (ℚP.+-identityʳ a)
  ; lerp-1 = λ a b → trans (cong (a ⊕_) (ℚP.*-identityˡ (b ⊖ a))) (pf a b) }
  where
    pf : ∀ a b → a ⊕ (b ⊖ a) ≡ b
    pf a b = trans (cong (a ⊕_) (ℚP.+-comm b (ℚ.- a)))
            (trans (sym (ℚP.+-assoc a (ℚ.- a) b))
            (trans (cong (_⊕ b) (ℚP.+-inverseʳ a)) (ℚP.+-identityˡ b)))

------------------------------------------------------------------------
-- Tracks: the free monad on `Seq`, with pieces as leaves

record Piece (A : Set) : Set where
  constructor piece
  field
    ticks  : ℕ
    from   : A
    to     : A
    easing : Easing
open Piece public

SeqC : Container 0ℓ 0ℓ
SeqC = ⊤ ▷ (λ _ → Fin 2)

Track : Set → Set
Track A = SeqC ⋆ Piece A

private
  pick2 : ∀ {X : Set} → X → X → Fin 2 → X
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

infixr 5 _⨾ᵗ_
_⨾ᵗ_ : ∀ {A} → Track A → Track A → Track A
a ⨾ᵗ b = impure (tt , pick2 a b)

-- the fold of the free monad on `Seq`
foldT : ∀ {P X : Set} → (P → X) → (X → X → X) → SeqC ⋆ P → X
foldT leaf seq (pure p)          = leaf p
foldT leaf seq (impure (_ , k))  = seq (foldT leaf seq (k zero)) (foldT leaf seq (k (suc zero)))

------------------------------------------------------------------------
-- Sampling: the algebra into (length, function of the tick)

Sampled : Set → Set
Sampled A = ℕ × (ℕ → A)

-- how far through `d` ticks the tick `t` is
ratio : ℕ → ℕ → ℚ
ratio t ℕ.zero    = 1ℚ
ratio t (ℕ.suc d) = if t <ᵇ ℕ.suc d then ℤ.+ t ℚ./ ℕ.suc d else 1ℚ

samplePiece : ∀ {A} → Lerp A → Piece A → Sampled A
samplePiece L (piece d a b e) = d , λ t → Lerp.lerp L (progress e (ratio t d)) a b

-- one after the other: the second function takes over at the boundary
seqS : ∀ {A} → Sampled A → Sampled A → Sampled A
seqS (n , f) (m , g) = n + m , λ t → if t <ᵇ n then f t else g (t ∸ n)

sample : ∀ {A} → Lerp A → Track A → Sampled A
sample L = foldT (samplePiece L) seqS

-- the length of a track
dur : ∀ {A} → Track A → ℕ
dur = foldT ticks _+_

sample-dur : ∀ {A} (L : Lerp A) (t : Track A) → proj₁ (sample L t) ≡ dur t
sample-dur L (pure p)         = refl
sample-dur L (impure (_ , k)) = cong₂ _+_ (sample-dur L (k zero)) (sample-dur L (k (suc zero)))

sample-⨾ᵗ : ∀ {A} (L : Lerp A) (a b : Track A) → sample L (a ⨾ᵗ b) ≡ seqS (sample L a) (sample L b)
sample-⨾ᵗ L a b = refl

------------------------------------------------------------------------
-- Endpoint laws

private
  ge⇒¬lt : ∀ t d → d ℕ.≤ t → (t <ᵇ d) ≡ false
  ge⇒¬lt t        ℕ.zero    _            = refl
  ge⇒¬lt (ℕ.suc t) (ℕ.suc d) (ℕ.s≤s h)   = ge⇒¬lt t d h

  zero-lt : ∀ d → (0 <ᵇ ℕ.suc d) ≡ true
  zero-lt d = refl

-- a piece of positive length starts at `from`
piece-start : ∀ {A} (L : Lerp A) d a b e →
              proj₂ (samplePiece L (piece (ℕ.suc d) a b e)) 0 ≡ a
piece-start L d a b e =
  trans (cong (λ p → Lerp.lerp L p a b) (trans (cong (progress e) (ℚP.0/n≡0 (ℕ.suc d))) (progress-0 e)))
        (Lerp.lerp-0 L a b)

-- and holds `to` from its end on
piece-end : ∀ {A} (L : Lerp A) d a b e t → d ℕ.≤ t →
            proj₂ (samplePiece L (piece d a b e)) t ≡ b
piece-end L d a b e t h = trans (cong (λ p → Lerp.lerp L (progress e p) a b) (r d h)) (trans (cong (λ p → Lerp.lerp L p a b) (progress-1 e)) (Lerp.lerp-1 L a b))
  where
    r : ∀ d → d ℕ.≤ t → ratio t d ≡ 1ℚ
    r ℕ.zero    _ = refl
    r (ℕ.suc d) h′ = if-false (t <ᵇ ℕ.suc d) (ge⇒¬lt t (ℕ.suc d) h′)
      where if-false : ∀ {X Y : ℚ} b → b ≡ false → (if b then X else Y) ≡ Y
            if-false .false refl = refl

------------------------------------------------------------------------
-- Sequencing is associative (pointwise: no function extensionality)

infix 4 _≈ˢ_
_≈ˢ_ : ∀ {A} → Sampled A → Sampled A → Set
(n , f) ≈ˢ (m , g) = n ≡ m × (∀ t → f t ≡ g t)

private
  lt-+ˡ : ∀ t n m → (t <ᵇ n) ≡ true → (t <ᵇ n + m) ≡ true
  lt-+ˡ ℕ.zero    (ℕ.suc n) m _ = refl
  lt-+ˡ (ℕ.suc t) (ℕ.suc n) m h = lt-+ˡ t n m h

  lt-+ʳ : ∀ t n m → (t <ᵇ n) ≡ false → (t <ᵇ n + m) ≡ (t ∸ n <ᵇ m)
  lt-+ʳ t        ℕ.zero    m _ = refl
  lt-+ʳ (ℕ.suc t) (ℕ.suc n) m h = lt-+ʳ t n m h

seqS-assoc : ∀ {A} (a b c : Sampled A) → seqS (seqS a b) c ≈ˢ seqS a (seqS b c)
seqS-assoc (n , f) (m , g) (k , h) = ℕP.+-assoc n m k , pf
  where
    pf : ∀ t → (if t <ᵇ n + m then (if t <ᵇ n then f t else g (t ∸ n)) else h (t ∸ (n + m)))
             ≡ (if t <ᵇ n then f t else (if t ∸ n <ᵇ m then g (t ∸ n) else h (t ∸ n ∸ m)))
    pf t with t <ᵇ n in eq
    ... | true  rewrite lt-+ˡ t n m eq = refl
    ... | false rewrite lt-+ʳ t n m eq | ℕP.∸-+-assoc t n m = refl

------------------------------------------------------------------------
-- Reversal: a fold, and an involution

-- the track played backwards: pieces swap their ends and reverse their easing,
-- and sequencing swaps its operands
reverseT : ∀ {A} → Track A → Track A
reverseT (pure (piece d a b e)) = pure (piece d b a (reverseE e))
reverseT (impure (_ , k))       = reverseT (k (suc zero)) ⨾ᵗ reverseT (k zero)

-- equality of tracks, by recursion (no function extensionality)
_≈ᵗ_ : ∀ {A} → Track A → Track A → Set
pure p          ≈ᵗ pure q          = p ≡ q
pure _          ≈ᵗ impure _        = ⊥
impure _        ≈ᵗ pure _          = ⊥
impure (_ , k)  ≈ᵗ impure (_ , k′) = k zero ≈ᵗ k′ zero × k (suc zero) ≈ᵗ k′ (suc zero)

≈ᵗ-refl : ∀ {A} (t : Track A) → t ≈ᵗ t
≈ᵗ-refl (pure p)         = refl
≈ᵗ-refl (impure (_ , k)) = ≈ᵗ-refl (k zero) , ≈ᵗ-refl (k (suc zero))

reverseT-invol : ∀ {A} (t : Track A) → reverseT (reverseT t) ≈ᵗ t
reverseT-invol (pure (piece d a b e)) rewrite reverseE-invol e = refl
reverseT-invol (impure (_ , k))       = reverseT-invol (k zero) , reverseT-invol (k (suc zero))

reverseT-dur : ∀ {A} (t : Track A) → dur (reverseT t) ≡ dur t
reverseT-dur (pure p)         = refl
reverseT-dur (impure (_ , k)) =
  trans (ℕP.+-comm (dur (reverseT (k (suc zero)))) (dur (reverseT (k zero))))
        (cong₂ _+_ (reverseT-dur (k zero)) (reverseT-dur (k (suc zero))))
