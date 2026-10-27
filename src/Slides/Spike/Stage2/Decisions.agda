{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The settled details of Stage 2 (docs/Stage2.md), each with its evidence:
--   (a) windows: primitives are eternal, so `Seq` of bare primitives is wrong (`bare-seq`);
--       under `Hold` it is right;
--   (b) `seqAt` leaks its left operand at negative times and its right operand past the end
--       (`seqAt-leak`); `seqW` is windowed by construction (`seqW-out`);
--   (c) `copairAlg` is the Set-level copairing of `Container.Sum.copair` (`copair-forget`);
--   (d) `Repeat`: the sample law at whole ticks (`loop-tick`) and `Loop.phase` / `Steps.index` as instances;
--   (e) `par` padding: an absent gap is a unit for `Par` on the nose (`mergeM-gap`), the present
--       empty frame `none` only up to layout equivalence (`none-not-unit`).

module Slides.Spike.Stage2.Decisions where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Container.Core using (Container; Shape; Position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; _+_; _*_; _∸_; _<ᵇ_; NonZero)
open import Data.Nat.DivMod using (_%_; m<n⇒m%n≡m; m≤n⇒[n∸m]%m≡n%m)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (¬_)

open import Container.Polynomial using (Poly₀)
open import Container.Sum using (copair)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-∸)
open import Slides.Diagram.Syntax using (Dia; atop; spacer)
open import Slides.Anim.Arith using (<ᵇ-ge; <ᵇ-false; <ᵇ-lt; <ᵇ-true)
open import Slides.Anim.Loop using (index; index<; index-step)
open import Slides.Anim.Continuous using (seqAt; _<ᵗ_)
open import Slides.Anim.Continuous.Properties using (ι-<ᵗ; zero≤ι)
open import Slides.Anim.Timeline using (mergeM)
open import Slides.Spike.Timed using (TM; holdT; delayT)
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.Scene.Properties using (seqW-tick; _≈_; mk≈)

------------------------------------------------------------------------
-- (c) Set-level copairing

-- the setoid `copair` (on the propositional setoid) forgets to `copairAlg` of the forgotten algebras
module _ {C₁ C₂ : Container 0ℓ 0ℓ} {X : Set} where
  private A = ≡.setoid X

  forget : ∀ {C : Container 0ℓ 0ℓ} → Func (Poly₀ C A) A → (s : Shape C) → (Position C s → X) → X
  forget α s k = α ⟨$⟩ (s , k)

  copair-forget : ∀ (α₁ : Func (Poly₀ C₁ A) A) (α₂ : Func (Poly₀ C₂ A) A) s k →
    copair C₁ C₂ A α₁ α₂ ⟨$⟩ (s , k) ≡ copairAlg (forget α₁) (forget α₂) s k
  copair-forget α₁ α₂ (inj₁ s) k = refl
  copair-forget α₁ α₂ (inj₂ s) k = refl

------------------------------------------------------------------------
-- (a), (b) windows

-- `seqAt` of two eternal values (duration 0): the left one shows only before time 0, the right
-- one from 0 on; so `Seq` of bare primitives loses the left one at every time ≥ 0
seqAt-leak : ∀ {A : Set} (a b : A) →
  (proj₂ (seqAt (0 , λ _ → just a) (0 , λ _ → just b)) (ℚ.- 1ℚ) ≡ just a)
  × (proj₂ (seqAt (0 , λ _ → just a) (0 , λ _ → just b)) 0ℚ ≡ just b)
seqAt-leak a b = refl , refl

private
  if-false : ∀ {A : Set} (b : Bool) (x y : A) → b ≡ false → (if b then x else y) ≡ y
  if-false .false x y refl = refl

  b∧¬b : ∀ b → (b ∧ not b) ≡ false
  b∧¬b true  = refl
  b∧¬b false = refl

-- `Seq` of bare primitives, with the guard: nothing at all (the window [0, 0+0) is empty), so
-- a primitive must sit under `Hold` to be shown; under `Hold` the window is the segment's
seqW-bare : ∀ {A : Set} (a b : A) τ → proj₂ (seqW (0 , λ _ → just a) (0 , λ _ → just b)) τ ≡ nothing
seqW-bare a b τ = if-false _ _ _ (b∧¬b (0ℚ ℚ.≤ᵇ τ))

-- `seqW` is windowed by construction: nothing outside [0, |x| + |y|)
seqW-out : ∀ {A : Set} (X Y : TM A) τ →
  ((0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι (proj₁ X + proj₁ Y))) ≡ false → proj₂ (seqW X Y) τ ≡ nothing
seqW-out X Y τ h = if-false _ _ _ h

-- `Delay` at whole ticks
delay-tick : ∀ {A : Set} n (X : TM A) k →
  proj₂ (delayT n X) (ι k) ≡ (if k <ᵇ n then nothing else proj₂ X (ι (k ∸ n)))
delay-tick n (m , f) k rewrite ι-<ᵗ k n with k <ᵇ n in e
... | true  = refl
... | false = cong f (sym (ι-∸ k n (<ᵇ-ge e)))

------------------------------------------------------------------------
-- (d) Repeat

loop-dur : ∀ {A : Set} n (X : TM A) → proj₁ (loopT n X) ≡ n * proj₁ X
loop-dur ℕ.zero    X = refl
loop-dur (ℕ.suc n) X = cong (proj₁ X +_) (loop-dur n X)

-- the sample law: at whole ticks, `Repeat n x` is `x` at the tick modulo its duration, for the
-- first `n * |x|` ticks (the guard of `seqW` does the rest)
private
  loop-shift : ∀ d m k → (k <ᵇ d + m) ≡ true → d ℕ.≤ k → (k ∸ d <ᵇ m) ≡ true
  loop-shift d m k h d≤k =
    <ᵇ-true {k ∸ d} {m} (ℕP.+-cancelˡ-< d (k ∸ d) m
      (≡.subst (ℕ._< d + m) (sym (ℕP.m+[n∸m]≡n d≤k)) (<ᵇ-lt {k} {d + m} h)))

loop-tick : ∀ {A : Set} n (X : TM A) .{{_ : NonZero (proj₁ X)}} k →
  proj₂ (loopT n X) (ι k) ≡ (if k <ᵇ n * proj₁ X then proj₂ X (ι (k % proj₁ X)) else nothing)
loop-tick ℕ.zero    X k = refl
loop-tick (ℕ.suc n) X k rewrite seqW-tick X (loopT n X) k | loop-dur n X
  with k <ᵇ proj₁ X + n * proj₁ X in e₁
... | false = refl
... | true with k <ᵇ proj₁ X in e₂
...   | true  = cong (λ j → proj₂ X (ι j)) (sym (m<n⇒m%n≡m (<ᵇ-lt {k} {proj₁ X} e₂)))
...   | false rewrite loop-tick n X (k ∸ proj₁ X) | loop-shift (proj₁ X) (n * proj₁ X) k e₁ (<ᵇ-ge {k} {proj₁ X} e₂)
                    = cong (λ j → proj₂ X (ι j)) (m≤n⇒[n∸m]%m≡n%m (<ᵇ-ge {k} {proj₁ X} e₂))

-- `Slides.Anim.Loop.phase`, `phase-id`, `index-step` and `Steps`' `both` (p phases of n step
-- frames, the frame at step `i` of phase `φ` being `i + φ * n`) are this law: the tick
-- `index n φ i` of `Repeat p x` shows `x` at `i`
repeat-phase : ∀ {A : Set} p (X : TM A) {{nz : NonZero (proj₁ X)}} φ i → φ ℕ.< p → i ℕ.< proj₁ X →
  proj₂ (loopT p X) (ι (index (proj₁ X) φ i)) ≡ proj₂ X (ι i)
repeat-phase p X {{nz}} φ i hφ hi rewrite loop-tick p X (index (proj₁ X) φ i)
  | <ᵇ-true {index (proj₁ X) φ i} {p * proj₁ X} (index< (proj₁ X) p φ i hφ hi)
  | index-step (proj₁ X) {{nz}} φ i hi = refl

------------------------------------------------------------------------
-- (e) padding

-- an absent scene of duration k (`Delay k` of an empty `Hold 0`)
gapT : ∀ {A : Set} → ℕ → TM A
gapT k = k , λ _ → nothing

-- absence is a unit of `mergeM` on the nose: padding `Par`'s shorter side with a gap changes nothing
mergeM-gap : ∀ {F : Set} (_⊙_ : F → F → F) x → (mergeM _⊙_ x nothing ≡ x) × (mergeM _⊙_ nothing x ≡ x)
mergeM-gap _⊙_ nothing  = refl , refl
mergeM-gap _⊙_ (just x) = refl , refl

-- the padding of the existing `par` (`none`) is a *present* empty frame, so it is a unit only up
-- to layout equivalence (`Place.Properties.Laws.⊙-unitˡ`, for valid layouts), never on the nose
none-not-unit : ∀ (z w h : ℕ) → ¬ (atop (spacer z z) (spacer w h) ≡ spacer w h)
none-not-unit z w h ()

-- ... and a gap is `Delay k` of an empty `Hold 0`, so `Delay` needs no frame of its own
gap-delay : ∀ {A : Set} k (x : TM A) → delayT k (holdT 0 x) ≈ gapT k
gap-delay k x = mk≈ (ℕP.+-identityʳ k) at
  where
    at : ∀ τ → proj₂ (delayT k (holdT 0 x)) τ ≡ nothing
    at τ with τ <ᵗ ι k
    ... | true  = refl
    ... | false = if-false _ _ _ (b∧¬b (0ℚ ℚ.≤ᵇ (τ ℚ.- ι k)))
