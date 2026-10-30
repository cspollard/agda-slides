{-# OPTIONS --safe --without-K #-}

-- The continuous model: ℚ.  Subtraction is exact, a percentage is multiplication by `p/100`,
-- scaling is ℚ over itself, and `ratCoupling` interprets ratio and easing (Béziers approximately).
-- `ι : ℕ → ℚ` embeds whole ticks as `n/1`; proofs about it are the only place ℚ is computed in.

module Slides.Scalar.Model.Rat where

open import Data.Integer as ℤ using (+_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕD
import Data.Nat.Coprimality as ℕC
import Data.Nat.Divisibility as ℕDv
open import Data.Bool using (T)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; mkℚ; _/_; _+_; _*_; _-_; _⊔_; _≤_; 0ℚ; 1ℚ; ½)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised as ℚᵘ using (*≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Slides.Scalar.Core
open import Slides.Scalar.Space
open import Slides.Scalar.Time
open import Slides.Scalar.Coupling
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)

ratMon : OrdMon ℚ
ratMon = record
  { 0# = 0ℚ ; _+_ = _+_ ; _⊔_ = _⊔_ ; _≤_ = _≤_ ; _≤?_ = ℚP._≤?_
  ; +-assoc = ℚP.+-assoc ; +-comm = ℚP.+-comm ; +-idˡ = ℚP.+-identityˡ
  ; +-cancelˡ = λ a b c e → trans (sym (ℚP.+-identityˡ b))
      (trans (cong (λ y → y + b) (sym (ℚP.+-inverseˡ a)))
        (trans (ℚP.+-assoc (ℚ.- a) a b)
          (trans (cong (λ y → (ℚ.- a) + y) e)
            (trans (sym (ℚP.+-assoc (ℚ.- a) a c))
              (trans (cong (λ y → y + c) (ℚP.+-inverseˡ a)) (ℚP.+-identityˡ c))))))
  ; ≤-refl = ℚP.≤-refl ; ≤-trans = ℚP.≤-trans ; ≤-antisym = ℚP.≤-antisym ; ≤-total = ℚP.≤-total
  ; +-mono = ℚP.+-mono-≤ ; ⊔-ub₁ = λ a b → ℚP.p≤p⊔q a b ; ⊔-ub₂ = λ a b → ℚP.p≤q⊔p a b ; ⊔-lub = ℚP.⊔-lub }

ratSub : Sub ratMon
ratSub = record
  { _-_ = _-_
  ; sub-add = λ {a} {b} _ → trans (ℚP.+-comm b (a - b))
      (trans (ℚP.+-assoc a (ℚ.- b) b) (trans (cong (λ y → a + y) (ℚP.+-inverseˡ b)) (ℚP.+-identityʳ a))) }

ratPct : ℕ → ℚ → ℚ
ratPct p x = (+ p / 100) * x

ratSpace : Space ℚ
ratSpace = record
  { ord = ratMon ; sub = ratSub ; pct = ratPct
  ; pct-100 = ℚP.*-identityˡ
  ; pct-mono = λ p x≤y → ℚP.*-monoˡ-≤-nonNeg (+ p / 100) {{ℚP.normalize-nonNeg p 100}} x≤y }

ratScale : Scale ratMon ℚ
ratScale = record
  { 0r = 0ℚ ; 1r = 1ℚ ; _+r_ = _+_ ; _*r_ = _*_ ; _≤r_ = _≤_ ; _·_ = _*_
  ; ·-1 = ℚP.*-identityˡ ; ·-zero = ℚP.*-zeroˡ ; ·-* = ℚP.*-assoc
  ; ·-+ = λ r s x → ℚP.*-distribʳ-+ x r s ; ·-dist = ℚP.*-distribˡ-+
  ; ·-mono = λ {r} 0≤r x≤y → ℚP.*-monoˡ-≤-nonNeg r {{ℚ.nonNegative 0≤r}} x≤y }

-- Whole ticks inside ℚ: `ι n = n/1`, and its facts (the only place ℚ is computed in)

private
  coprime-1 : ∀ n → ℕC.Coprime n 1
  coprime-1 n (_ , d∣1) = ℕDv.∣1⇒≡1 d∣1

ι : ℕ → ℚ
ι n = mkℚ (+ n) 0 (coprime-1 n)    -- n/1, written without the gcd normalisation

toℚᵘ-ι : ∀ n → ℚ.toℚᵘ (ι n) ℚᵘ.≃ ℚᵘ.mkℚᵘ (+ n) 0
toℚᵘ-ι n = ℚᵘP.≃-refl

ι-+ : ∀ a b → ι (a ℕ.+ b) ≡ ι a + ι b
ι-+ a b = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι (a ℕ.+ b))
  (ℚᵘP.≃-trans (*≡* (trans (cong (ℤ._* + 1) (ℤP.pos-+ a b)) (lem (+ a) (+ b))))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-+ (ι a) (ι b)) (ℚᵘP.+-cong (toℚᵘ-ι a) (toℚᵘ-ι b))))))
  where lem : ∀ x y → (x ℤ.+ y) ℤ.* + 1 ≡ (x ℤ.* + 1 ℤ.+ y ℤ.* + 1) ℤ.* + 1
        lem = solve-∀

ι-* : ∀ a b → ι (a ℕ.* b) ≡ ι a * ι b
ι-* a b = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι (a ℕ.* b))
  (ℚᵘP.≃-trans (*≡* (cong (ℤ._* + 1) (ℤP.pos-* a b)))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-* (ι a) (ι b)) (ℚᵘP.*-cong (toℚᵘ-ι a) (toℚᵘ-ι b))))))

-- the comparison, as a boolean, is preserved and reflected
ι-≤ᵇ : ∀ a b → (ι a ℚ.≤ᵇ ι b) ≡ (a ℕ.≤ᵇ b)
ι-≤ᵇ a b rewrite ℕP.*-identityʳ a | ℕP.*-identityʳ b
               | ℤP.+◃n≡+n a | ℤP.+◃n≡+n b = refl

ι-mono : ∀ {a b} → a ℕ.≤ b → ι a ≤ ι b
ι-mono {a} {b} h = ℚP.≤ᵇ⇒≤ {ι a} {ι b} (subst T (sym (ι-≤ᵇ a b)) (ℕP.≤⇒≤ᵇ h))

ι-reflect : ∀ {a b} → ι a ≤ ι b → a ℕ.≤ b
ι-reflect {a} {b} h = ℕP.≤ᵇ⇒≤ a b (subst T (ι-≤ᵇ a b) (ℚP.≤⇒≤ᵇ {ι a} {ι b} h))

ratFloor : ℚ → ℕ
ratFloor q = ℤ.∣ ℚ.floor q ∣

private
  div-gal : ∀ n m d → (n ℕ.* ℕ.suc d ℕ.≤ m → n ℕ.≤ m ℕ./ ℕ.suc d) × (n ℕ.≤ m ℕ./ ℕ.suc d → n ℕ.* ℕ.suc d ℕ.≤ m)
  div-gal n m d =
    (λ h → subst (ℕ._≤ _) (ℕD.m*n/n≡m n (ℕ.suc d)) (ℕD./-monoˡ-≤ (ℕ.suc d) h)) ,
    (λ h → ℕP.≤-trans (ℕP.*-monoˡ-≤ (ℕ.suc d) h) (ℕD.m/n*n≤m m (ℕ.suc d)))

  -- n/1 ≤ m/(d+1) iff n·(d+1) ≤ m  (`pos-*` turns ℤ products of naturals into ℕ ones)
  ι≤ : ∀ n m d .(c : ℕC.Coprime m (ℕ.suc d)) → (ι n ≤ mkℚ (+ m) d c → n ℕ.* ℕ.suc d ℕ.≤ m) × (n ℕ.* ℕ.suc d ℕ.≤ m → ι n ≤ mkℚ (+ m) d c)
  ι≤ n m d c =
    (λ h → subst (n ℕ.* ℕ.suc d ℕ.≤_) (ℕP.*-identityʳ m)
             (ℤ.drop‿+≤+ (subst₂ ℤ._≤_ (sym (ℤP.pos-* n (ℕ.suc d))) (sym (ℤP.pos-* m 1)) (ℚ.drop-*≤* h)))) ,
    (λ h → ℚ.*≤* (subst₂ ℤ._≤_ (ℤP.pos-* n (ℕ.suc d)) (ℤP.pos-* m 1)
             (ℤ.+≤+ (subst (n ℕ.* ℕ.suc d ℕ.≤_) (sym (ℕP.*-identityʳ m)) h))))

  ratFloor-pos : ∀ m d .(c : ℕC.Coprime m (ℕ.suc d)) → ratFloor (mkℚ (+ m) d c) ≡ m ℕ./ ℕ.suc d
  ratFloor-pos m d c = trans (ℤP.abs-◃ _ _) (ℕP.+-identityʳ _)

ratFloor-gal : ∀ n x → 0ℚ ≤ x → (ι n ≤ x → n ℕ.≤ ratFloor x) × (n ℕ.≤ ratFloor x → ι n ≤ x)
ratFloor-gal n (mkℚ (+ m) d c) _ rewrite ratFloor-pos m d c =
  (λ h → proj₁ (div-gal n m d) (proj₁ (ι≤ n m d c) h)) , (λ h → proj₂ (ι≤ n m d c) (proj₂ (div-gal n m d) h))
ratFloor-gal n (mkℚ ℤ.-[1+ k ] d c) (ℚ.*≤* ())

ratTime : Time ℚ
ratTime = record
  { ord = ratMon ; tick = ι ; floor = ratFloor
  ; tick-0 = refl ; tick-+ = ι-+ ; tick-mono = ι-mono ; tick-reflect = ι-reflect
  ; floor-gal = λ {n} {x} → ratFloor-gal n x }

ratRatio : ℚ → ℚ → ℚ
ratRatio t d with d ℚP.≟ 0ℚ
... | yes _   = 0ℚ
... | no d≢0  = ℚ._÷_ t d {{ℚ.≢-nonZero d≢0}}

-- the cubic Bézier curve with control values `c₁ c₂` (end values 0 and 1) at parameter `s`
cubic : ℚ → ℚ → ℚ → ℚ
cubic c₁ c₂ s = 3ℚ * u * u * s * c₁ + 3ℚ * u * s * s * c₂ + s * s * s
  where u = 1ℚ - s
        3ℚ = + 3 / 1

-- the parameter `s` with x(s) = r, by `n` bisection steps from [lo, hi]
bisect : ℕ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
bisect ℕ.zero    x₁ x₂ lo hi r = ½ * (lo + hi)
bisect (ℕ.suc n) x₁ x₂ lo hi r =
  if cubic x₁ x₂ (½ * (lo + hi)) ℚ.≤ᵇ r then bisect n x₁ x₂ (½ * (lo + hi)) hi r
  else bisect n x₁ x₂ lo (½ * (lo + hi)) r

hundredths : ℕ → ℚ
hundredths n = + n / 100

-- the easing of a ratio; a Bézier is approximate (sixteen bisection steps) and clamped at the ends
ratEase : Easing → ℚ → ℚ
ratEase Linear    r = r
ratEase (Bezier a b c d) r =
  if r ℚ.≤ᵇ 0ℚ then 0ℚ else if 1ℚ ℚ.≤ᵇ r then 1ℚ
  else cubic (hundredths b) (hundredths d) (bisect 16 (hundredths a) (hundredths c) 0ℚ 1ℚ r)
ratEase Step      r = if 1ℚ ℚ.≤ᵇ r then 1ℚ else 0ℚ
ratEase StepStart r = if r ℚ.≤ᵇ 0ℚ then 0ℚ else 1ℚ

ratCoupling : Coupling ratTime ratSub ratScale
ratCoupling = record
  { ratio = ratRatio ; ease = ratEase
  ; ratio-scale = λ r d d≢0 → scale-ratio r d d≢0
  ; ease-0 = λ { Linear → refl ; Step → refl ; StepStart → refl ; (Bezier _ _ _ _) → refl }
  ; ease-1 = λ { Linear → refl ; Step → refl ; StepStart → refl ; (Bezier _ _ _ _) → refl }}
  where
    scale-ratio : ∀ r d → ¬ (d ≡ 0ℚ) → ratRatio (r * d) d ≡ r
    scale-ratio r d d≢0 with d ℚP.≟ 0ℚ
    ... | yes e  = ⊥-elim (d≢0 e)
    ... | no  _  = trans (ℚP.*-assoc r d (ℚ.1/_ d {{ℚ.≢-nonZero d≢0}}))
                     (trans (cong (λ y → r * y) (ℚP.*-inverseʳ d {{ℚ.≢-nonZero d≢0}})) (ℚP.*-identityʳ r))
