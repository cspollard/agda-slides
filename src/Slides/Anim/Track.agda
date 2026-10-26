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
open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Tactic.RingSolver using (solve-∀)
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; *≡*; _≃_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
import Tactic.RingSolver.NonReflective as NR
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat.Properties as ℕP
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

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

-- the value a track starts at
start : ∀ {A} → Track A → A
start = foldT from (λ a _ → a)

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

------------------------------------------------------------------------
-- Reversal at the level of samples
--
-- For `Linear` pieces, playing a piece backwards is sampling it at `d - k`:
-- the reversed piece (ends swapped) at tick `k` equals the piece at tick `d - k`.
-- (At a boundary inside a track the original is right-continuous and the reversed
-- track left-continuous, so the statement is for one piece.  `Bezier` is
-- approximate; see `reverse-piece` for the easings that reverse exactly.)

private
  pos∸ : ∀ d k → k ≤ d → + (d ∸ k) ≡ + d ℤ.- + k
  pos∸ d k h = trans (sym (ℤP.⊖-≥ h)) (sym (ℤP.m-n≡m⊖n d k))

  toℚᵘ-/ : ∀ n d′ → ℚ.toℚᵘ (n / ℕ.suc d′) ≃ mkℚᵘ n d′
  toℚᵘ-/ n d′ = ℚP.toℚᵘ-fromℚᵘ (mkℚᵘ n d′)

  core : ∀ k d′ → k ≤ ℕ.suc d′ → mkℚᵘ (+ (ℕ.suc d′ ∸ k)) d′ ≃ ℚᵘ.1ℚᵘ ℚᵘ.+ ℚᵘ.- mkℚᵘ (+ k) d′
  core k d′ h rewrite pos∸ (ℕ.suc d′) k h | ℕP.+-identityʳ d′ = *≡* (alg (+ ℕ.suc d′) (+ k))
    where alg : ∀ E K → (E ℤ.- K) ℤ.* E ≡ (E ℤ.+ ℤ.- K ℤ.* ℤ.+ 1) ℤ.* E
          alg = solve-∀


frac-compl : ∀ k d′ → k ≤ ℕ.suc d′ → (+ (ℕ.suc d′ ∸ k)) / ℕ.suc d′ ≡ 1ℚ ℚ.- (+ k) / ℕ.suc d′
frac-compl k d′ h = ℚP.toℚᵘ-injective chain
  where
    x = (+ k) / ℕ.suc d′
    s1 : ℚ.toℚᵘ (1ℚ ℚ.- x) ≃ ℚᵘ.1ℚᵘ ℚᵘ.+ ℚᵘ.- ℚ.toℚᵘ x
    s1 = ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-+ 1ℚ (ℚ.- x)) (ℚᵘP.+-cong (ℚᵘP.≃-refl {ℚᵘ.1ℚᵘ}) (ℚP.toℚᵘ-homo‿- x))
    s2 : ℚᵘ.1ℚᵘ ℚᵘ.+ ℚᵘ.- ℚ.toℚᵘ x ≃ ℚᵘ.1ℚᵘ ℚᵘ.+ ℚᵘ.- mkℚᵘ (+ k) d′
    s2 = ℚᵘP.+-cong (ℚᵘP.≃-refl {ℚᵘ.1ℚᵘ}) (ℚᵘP.-‿cong (toℚᵘ-/ (+ k) d′))
    chain : ℚ.toℚᵘ ((+ (ℕ.suc d′ ∸ k)) / ℕ.suc d′) ≃ ℚ.toℚᵘ (1ℚ ℚ.- x)
    chain = ℚᵘP.≃-trans (toℚᵘ-/ (+ (ℕ.suc d′ ∸ k)) d′) (ℚᵘP.≃-trans (core k d′ h) (ℚᵘP.≃-sym (ℚᵘP.≃-trans s1 s2)))



private
  ring′ = fromCommutativeRing ℚP.+-*-commutativeRing zero?
    where zero? : ∀ x → Maybe (0ℚ ≡ x)
          zero? x with x ℚ.≟ 0ℚ
          ... | yes p = just (sym p)
          ... | no _  = nothing
open NR ring′ using (solve; _⊜_; Κ; ⊝_) renaming (_⊕_ to _:+_; _⊗_ to _:*_)

flip-ℚ : ∀ q a b → a ℚ.+ (1ℚ ℚ.- q) ℚ.* (b ℚ.- a) ≡ b ℚ.+ q ℚ.* (a ℚ.- b)
flip-ℚ = solve 3 (λ q a b → (a :+ (Κ 1ℚ :+ ⊝ q) :* (b :+ ⊝ a)) ⊜ (b :+ q :* (a :+ ⊝ b))) refl

private
  ite-true : ∀ {X Y : ℚ} b → b ≡ true → (if b then X else Y) ≡ X
  ite-true .true refl = refl

  ite-false : ∀ {X Y : ℚ} b → b ≡ false → (if b then X else Y) ≡ Y
  ite-false .false refl = refl

  lt-true : ∀ k n → k ℕ.< n → (k <ᵇ n) ≡ true
  lt-true ℕ.zero    (ℕ.suc n) _          = refl
  lt-true (ℕ.suc k) (ℕ.suc n) (ℕ.s≤s h)  = lt-true k n h

  lt-irrefl : ∀ n → (n <ᵇ n) ≡ false
  lt-irrefl ℕ.zero    = refl
  lt-irrefl (ℕ.suc n) = lt-irrefl n

ratio-lt : ∀ t d′ → t ℕ.< ℕ.suc d′ → ratio t (ℕ.suc d′) ≡ ℤ.+ t / ℕ.suc d′
ratio-lt t d′ h = ite-true (t <ᵇ ℕ.suc d′) (lt-true t (ℕ.suc d′) h)

ratio-full : ∀ d′ → ratio (ℕ.suc d′) (ℕ.suc d′) ≡ 1ℚ
ratio-full d′ = ite-false (ℕ.suc d′ <ᵇ ℕ.suc d′) (lt-irrefl (ℕ.suc d′))

-- progress at `d - k` is the complement of progress at `k`
ratio-compl : ∀ k d′ → k ≤ ℕ.suc d′ → ratio (ℕ.suc d′ ∸ k) (ℕ.suc d′) ≡ 1ℚ ℚ.- ratio k (ℕ.suc d′)
ratio-compl ℕ.zero d′ _ =
  trans (ratio-full d′)
        (sym (cong (λ x → 1ℚ ℚ.- x) (trans (ratio-lt 0 d′ (ℕ.s≤s ℕ.z≤n)) (ℚP.0/n≡0 (ℕ.suc d′)))))
ratio-compl (ℕ.suc k) d′ h with ℕP.m≤n⇒m<n∨m≡n h
... | inj₂ refl rewrite ℕP.n∸n≡0 k =
  trans (trans (ratio-lt 0 k (ℕ.s≤s ℕ.z≤n)) (ℚP.0/n≡0 (ℕ.suc k)))
        (sym (cong (λ x → 1ℚ ℚ.- x) (ratio-full k)))
... | inj₁ lt =
  trans (ratio-lt (ℕ.suc d′ ∸ ℕ.suc k) d′ (ℕ.s≤s (ℕP.m∸n≤m d′ k)))
  (trans (frac-compl (ℕ.suc k) d′ (ℕP.<⇒≤ lt))
         (sym (cong (λ x → 1ℚ ℚ.- x) (ratio-lt (ℕ.suc k) d′ lt))))

-- the interpolation is symmetric: `lerp (1 - q) a b = lerp q b a`
LerpFlip : ∀ {A} → Lerp A → Set
LerpFlip {A} L = ∀ q (a b : A) → Lerp.lerp L (1ℚ ℚ.- q) a b ≡ Lerp.lerp L q b a

ℚLerpFlip : LerpFlip ℚLerp
ℚLerpFlip = flip-ℚ

------------------------------------------------------------------------
-- Reversing an easing
--
-- Playing a piece backwards swaps its ends and reverses its easing.  `Linear`,
-- `Step` and `StepStart` reverse exactly: progress of the reversed easing is the
-- complement of progress of the original at the complementary time
-- (`progress e (1 - x) = 1 - progress (reverseE e) x`).  `Bezier` reverses only
-- approximately (the progress is found by bisection), so it is excluded.

private
  T⇒≡ : ∀ {a b : Bool} → (T a → T b) → (T b → T a) → a ≡ b
  T⇒≡ {true}  {true}  _ _ = refl
  T⇒≡ {true}  {false} f _ = ⊥-elim (f tt)
  T⇒≡ {false} {true}  _ g = ⊥-elim (g tt)
  T⇒≡ {false} {false} _ _ = refl

  ≤ᵇ-iff : ∀ {p q} → (T (p ℚ.≤ᵇ q) → p ℚ.≤ q) × (p ℚ.≤ q → T (p ℚ.≤ᵇ q))
  ≤ᵇ-iff = ℚP.≤ᵇ⇒≤ , ℚP.≤⇒≤ᵇ

  sub₂ : ∀ {a b c d} → a ≡ c → b ≡ d → a ℚ.≤ b → c ℚ.≤ d
  sub₂ refl refl h = h

  e₁ : ∀ x → 1ℚ ℚ.+ (x ℚ.+ ℚ.- 1ℚ) ≡ x
  e₁ = solve 1 (λ x → (Κ 1ℚ :+ (x :+ ⊝ Κ 1ℚ)) ⊜ x) refl
  e₂ : ∀ x → (1ℚ ℚ.+ ℚ.- x) ℚ.+ (x ℚ.+ ℚ.- 1ℚ) ≡ 0ℚ
  e₂ = solve 1 (λ x → ((Κ 1ℚ :+ ⊝ x) :+ (x :+ ⊝ Κ 1ℚ)) ⊜ Κ 0ℚ) refl
  e₃ : ∀ x → 1ℚ ℚ.+ (x ℚ.+ ℚ.- x) ≡ 1ℚ
  e₃ = solve 1 (λ x → (Κ 1ℚ :+ (x :+ ⊝ x)) ⊜ Κ 1ℚ) refl
  e₄ : ∀ x → 1ℚ ℚ.+ (0ℚ ℚ.+ ℚ.- x) ≡ 1ℚ ℚ.- x
  e₄ = solve 1 (λ x → (Κ 1ℚ :+ (Κ 0ℚ :+ ⊝ x)) ⊜ (Κ 1ℚ :+ ⊝ x)) refl
  e₅ : ∀ x → (1ℚ ℚ.+ ℚ.- x) ℚ.+ x ≡ 1ℚ
  e₅ = solve 1 (λ x → ((Κ 1ℚ :+ ⊝ x) :+ x) ⊜ Κ 1ℚ) refl
  e₆ : ∀ x → 0ℚ ℚ.+ x ≡ x
  e₆ = solve 1 (λ x → (Κ 0ℚ :+ x) ⊜ x) refl
  e₇ : ∀ x → 1ℚ ℚ.+ ℚ.- x ≡ 1ℚ ℚ.- x
  e₇ x = refl
  e₈ : ∀ x → x ℚ.+ ℚ.- x ≡ 0ℚ
  e₈ = solve 1 (λ x → (x :+ ⊝ x) ⊜ Κ 0ℚ) refl

  -- 1 ≤ 1 - x  ⇔  x ≤ 0
  a→ : ∀ x → 1ℚ ℚ.≤ 1ℚ ℚ.- x → x ℚ.≤ 0ℚ
  a→ x h = sub₂ (e₁ x) (e₂ x) (ℚP.+-mono-≤ h (ℚP.≤-refl {x ℚ.+ ℚ.- 1ℚ}))
  a← : ∀ x → x ℚ.≤ 0ℚ → 1ℚ ℚ.≤ 1ℚ ℚ.- x
  a← x h = sub₂ (e₃ x) (e₄ x) (ℚP.+-mono-≤ (ℚP.≤-refl {1ℚ}) (ℚP.+-mono-≤ h (ℚP.≤-refl {ℚ.- x})))
  -- 1 - x ≤ 0  ⇔  1 ≤ x
  b→ : ∀ x → 1ℚ ℚ.- x ℚ.≤ 0ℚ → 1ℚ ℚ.≤ x
  b→ x h = sub₂ (e₅ x) (e₆ x) (ℚP.+-mono-≤ h (ℚP.≤-refl {x}))
  b← : ∀ x → 1ℚ ℚ.≤ x → 1ℚ ℚ.- x ℚ.≤ 0ℚ
  b← x h = sub₂ (e₇ x) (e₈ x) (ℚP.+-mono-≤ h (ℚP.≤-refl {ℚ.- x}))

  s₁ : ∀ x → (1ℚ ≤ᵇ (1ℚ ℚ.- x)) ≡ (x ≤ᵇ 0ℚ)
  s₁ x = T⇒≡ (λ t → proj₂ ≤ᵇ-iff (a→ x (proj₁ ≤ᵇ-iff t))) (λ t → proj₂ ≤ᵇ-iff (a← x (proj₁ ≤ᵇ-iff t)))
  s₂ : ∀ x → ((1ℚ ℚ.- x) ≤ᵇ 0ℚ) ≡ (1ℚ ≤ᵇ x)
  s₂ x = T⇒≡ (λ t → proj₂ ≤ᵇ-iff (b→ x (proj₁ ≤ᵇ-iff t))) (λ t → proj₂ ≤ᵇ-iff (b← x (proj₁ ≤ᵇ-iff t)))

-- the easings that reverse exactly
Exact : Easing → Set
Exact (Bezier _ _ _ _) = ⊥
Exact _                = ⊤

private
  -- the constants, proved once and kept opaque so no rational arithmetic is
  -- normalised while checking `reversal`
  abstract
    sub-11 : 1ℚ ℚ.- 1ℚ ≡ 0ℚ
    sub-11 = refl
    sub-10 : 1ℚ ℚ.- 0ℚ ≡ 1ℚ
    sub-10 = refl

  rev-step : ∀ b → (if b then 1ℚ else 0ℚ) ≡ 1ℚ ℚ.- (if b then 0ℚ else 1ℚ)
  rev-step true  = sym sub-10
  rev-step false = sym sub-11

  rev-start : ∀ b → (if b then 0ℚ else 1ℚ) ≡ 1ℚ ℚ.- (if b then 1ℚ else 0ℚ)
  rev-start true  = sym sub-11
  rev-start false = sym sub-10

reversal : ∀ e → Exact e → ∀ x → progress e (1ℚ ℚ.- x) ≡ 1ℚ ℚ.- progress (reverseE e) x
reversal Linear    _ x = refl
reversal Step      _ x = trans (cong (λ b → if b then 1ℚ else 0ℚ) (s₁ x)) (rev-step (x ≤ᵇ 0ℚ))
reversal StepStart _ x = trans (cong (λ b → if b then 0ℚ else 1ℚ) (s₂ x)) (rev-start (1ℚ ≤ᵇ x))
reversal (Bezier _ _ _ _) ()

-- a piece played backwards (ends swapped, easing reversed) at tick `k` is the
-- piece at tick `d - k`
reverse-piece : ∀ {A} (L : Lerp A) → LerpFlip L → ∀ e → Exact e → ∀ k d′ a b → k ≤ ℕ.suc d′ →
                proj₂ (samplePiece L (piece (ℕ.suc d′) b a (reverseE e))) k
                ≡ proj₂ (samplePiece L (piece (ℕ.suc d′) a b e)) (ℕ.suc d′ ∸ k)
reverse-piece L F e ex k d′ a b h =
  sym (trans (cong (λ x → Lerp.lerp L (progress e x) a b) (ratio-compl k d′ h))
       (trans (cong (λ x → Lerp.lerp L x a b) (reversal e ex (ratio k (ℕ.suc d′))))
              (F (progress (reverseE e) (ratio k (ℕ.suc d′))) a b)))

-- (for `Linear`, `reverseE` is the identity)
reverse-linear : ∀ {A} (L : Lerp A) → LerpFlip L → ∀ k d′ a b → k ≤ ℕ.suc d′ →
                 proj₂ (samplePiece L (piece (ℕ.suc d′) b a Linear)) k
                 ≡ proj₂ (samplePiece L (piece (ℕ.suc d′) a b Linear)) (ℕ.suc d′ ∸ k)
reverse-linear L F = reverse-piece L F Linear tt

------------------------------------------------------------------------
-- Reversal of whole tracks
--
-- Across a boundary the original track is right-continuous (the later piece
-- owns the tick where two pieces meet) while the reversed track gives that tick
-- to the earlier piece, so the two samples agree there exactly when the pieces
-- meet: the end of one is the start of the next.  A track is `Good` when every
-- piece has positive length and an `Exact` easing and consecutive pieces meet.
-- For a good track, tick `k` of the reversed track is tick `dur - k` of the
-- original, for every `k` up to and including `dur` (`reverse-sample`).  Without
-- continuity the statement fails exactly at the boundaries; zero-length pieces
-- are never sampled inside a track and are excluded.

-- the value a track ends at
endT : ∀ {A} → Track A → A
endT = foldT to (λ _ b → b)

Good : ∀ {A} → Track A → Set
Good (pure (piece d _ _ e)) = 0 ℕ.< d × Exact e
Good (impure (_ , k))       = Good (k zero) × Good (k (suc zero)) × endT (k zero) ≡ start (k (suc zero))

private
  if-true′ : ∀ {X : Set} {x y : X} b → b ≡ true → (if b then x else y) ≡ x
  if-true′ .true refl = refl

  if-false′ : ∀ {X : Set} {x y : X} b → b ≡ false → (if b then x else y) ≡ y
  if-false′ .false refl = refl

  lt⇒< : ∀ k m → (k <ᵇ m) ≡ true → k ℕ.< m
  lt⇒< ℕ.zero    (ℕ.suc m) _ = ℕ.s≤s ℕ.z≤n
  lt⇒< (ℕ.suc k) (ℕ.suc m) h = ℕ.s≤s (lt⇒< k m h)

  ≮⇒≥ : ∀ k m → (k <ᵇ m) ≡ false → m ℕ.≤ k
  ≮⇒≥ k          ℕ.zero    _ = ℕ.z≤n
  ≮⇒≥ (ℕ.suc k)  (ℕ.suc m) h = ℕ.s≤s (≮⇒≥ k m h)

  -- sequencing at a tick, given the length of the first operand
  seqS-at′ : ∀ {A} (L : Lerp A) (x y : Track A) n → dur x ≡ n → ∀ t →
             proj₂ (seqS (sample L x) (sample L y)) t
             ≡ (if t <ᵇ n then proj₂ (sample L x) t else proj₂ (sample L y) (t ∸ n))
  seqS-at′ L x y .(dur x) refl t rewrite sample-dur L x = refl

  seqS-at : ∀ {A} (L : Lerp A) (x y : Track A) t →
            proj₂ (seqS (sample L x) (sample L y)) t
            ≡ (if t <ᵇ dur x then proj₂ (sample L x) t else proj₂ (sample L y) (t ∸ dur x))
  seqS-at L x y = seqS-at′ L x y (dur x) refl

  -- after the first operand, the second
  seq-hi : ∀ {A} (L : Lerp A) (x y : Track A) i →
           proj₂ (seqS (sample L x) (sample L y)) (dur x + i) ≡ proj₂ (sample L y) i
  seq-hi L x y i =
    trans (seqS-at L x y (dur x + i))
      (trans (if-false′ _ (ge⇒¬lt (dur x + i) (dur x) (ℕP.m≤m+n (dur x) i)))
             (cong (proj₂ (sample L y)) (ℕP.m+n∸m≡n (dur x) i)))

  dur-pos : ∀ {A} (t : Track A) → Good t → 0 ℕ.< dur t
  dur-pos (pure (piece d _ _ _)) (h , _)       = h
  dur-pos (impure (_ , k))       (ga , gb , _) =
    ℕP.<-≤-trans (dur-pos (k zero) ga) (ℕP.m≤m+n (dur (k zero)) (dur (k (suc zero))))

  -- a good track starts at its start, and holds its end after its length
  sample-start : ∀ {A} (L : Lerp A) (t : Track A) → Good t → proj₂ (sample L t) 0 ≡ start t
  sample-start L (pure (piece (ℕ.suc d) a b e)) _ = piece-start L d a b e
  sample-start L (impure (_ , k)) (ga , gb , _) =
    trans (seqS-at L (k zero) (k (suc zero)) 0)
      (trans (if-true′ _ (lt-true 0 (dur (k zero)) (dur-pos (k zero) ga)))
             (sample-start L (k zero) ga))

  sample-end : ∀ {A} (L : Lerp A) (t : Track A) → proj₂ (sample L t) (dur t) ≡ endT t
  sample-end L (pure (piece d a b e)) = piece-end L d a b e d ℕP.≤-refl
  sample-end L (impure (_ , k)) =
    trans (seq-hi L (k zero) (k (suc zero)) (dur (k (suc zero)))) (sample-end L (k (suc zero)))

  sub-lem : ∀ n m j → (n + m) ∸ (m + j) ≡ n ∸ j
  sub-lem n ℕ.zero    j = cong (_∸ j) (ℕP.+-identityʳ n)
  sub-lem n (ℕ.suc m) j = trans (cong (_∸ ℕ.suc (m + j)) (ℕP.+-suc n m)) (sub-lem n m j)

  lt-step : ∀ n j′ → ℕ.suc j′ ℕ.≤ n → n ∸ ℕ.suc j′ ℕ.< n
  lt-step (ℕ.suc n) j′ _ = ℕ.s≤s (ℕP.m∸n≤m n j′)

-- the inductive step: two good tracks that meet, with the claim for each
private
  reverse-seq : ∀ {A} (L : Lerp A) (a b : Track A) → Good a → Good b → endT a ≡ start b →
                (∀ k → k ℕ.≤ dur a → proj₂ (sample L (reverseT a)) k ≡ proj₂ (sample L a) (dur a ∸ k)) →
                (∀ k → k ℕ.≤ dur b → proj₂ (sample L (reverseT b)) k ≡ proj₂ (sample L b) (dur b ∸ k)) →
                ∀ k → k ℕ.≤ dur a + dur b →
                proj₂ (seqS (sample L (reverseT b)) (sample L (reverseT a))) k
                ≡ proj₂ (seqS (sample L a) (sample L b)) (dur a + dur b ∸ k)
  reverse-seq L a b ga gb cont iha ihb k h =
    trans (seqS-at′ L (reverseT b) (reverseT a) m (reverseT-dur b) k) finish
    where
      n = dur a
      m = dur b
      orig : ℕ → _
      orig = proj₂ (seqS (sample L a) (sample L b))

      -- the part of the reversed track inside `reverseT a`, against the original near its end
      tail : ∀ j → j ℕ.≤ n → proj₂ (sample L (reverseT a)) j ≡ orig (n ∸ j)
      tail ℕ.zero _ =
        trans (trans (iha 0 ℕ.z≤n) (sample-end L a))
              (sym (trans (seqS-at L a b n)
                    (trans (if-false′ _ (lt-irrefl n))
                      (trans (cong (proj₂ (sample L b)) (ℕP.n∸n≡0 n))
                        (trans (sample-start L b gb) (sym cont))))))
      tail (ℕ.suc j′) jn =
        trans (iha (ℕ.suc j′) jn)
          (sym (trans (seqS-at L a b (n ∸ ℕ.suc j′))
                (if-true′ _ (lt-true (n ∸ ℕ.suc j′) n (lt-step n j′ jn)))))

      finish : (if k <ᵇ m then proj₂ (sample L (reverseT b)) k else proj₂ (sample L (reverseT a)) (k ∸ m))
               ≡ orig (n + m ∸ k)
      finish with k <ᵇ m in eq
      ... | true =
        let km = ℕP.<⇒≤ (lt⇒< k m eq) in
        trans (ihb k km)
              (sym (trans (cong orig (ℕP.+-∸-assoc n km)) (seq-hi L a b (m ∸ k))))
      ... | false =
        let mk  = ≮⇒≥ k m eq
            jn  = subst (k ∸ m ℕ.≤_) (ℕP.m+n∸n≡m n m) (ℕP.∸-monoˡ-≤ m h)
            idx = trans (cong (n + m ∸_) (sym (ℕP.m+[n∸m]≡n mk))) (sub-lem n m (k ∸ m))
        in trans (tail (k ∸ m) jn) (sym (cong orig idx))

-- tick `k` of the reversed track is tick `dur - k` of the original
reverse-sample : ∀ {A} (L : Lerp A) → LerpFlip L → (t : Track A) → Good t → ∀ k → k ℕ.≤ dur t →
                 proj₂ (sample L (reverseT t)) k ≡ proj₂ (sample L t) (dur t ∸ k)
reverse-sample L F (pure (piece (ℕ.suc d′) a b e)) (_ , ex) k h = reverse-piece L F e ex k d′ a b h
reverse-sample L F (pure (piece ℕ.zero _ _ _)) ()
reverse-sample L F (impure (_ , k′)) (ga , gb , cont) =
  reverse-seq L (k′ zero) (k′ (suc zero)) ga gb cont
    (reverse-sample L F (k′ zero) ga) (reverse-sample L F (k′ (suc zero)) gb)
