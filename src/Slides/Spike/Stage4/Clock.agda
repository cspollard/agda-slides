{-# OPTIONS --safe --without-K #-}

-- STAGE 4 SPIKE (plan/Unify.md section 4): clock domains compose by substitution.
--
-- THEORY MODULE (no executable imports it).  Over the temporal signature of Stage 2 (restricted
-- to the operations that move time: `Seq`, `Delay`, plus `Par`), parametric in the leaves `A`:
--
--   TimeC            = Seq, Par (binary), Delay n (unary)        TimeC ⋆ A = scenes with leaves A
--   Deck A           = TimeC ⋆ (TimeC ⋆ A)                       a deck of slides of scenes
--   sample ℓ         : TimeC ⋆ A → TM X                          for a leaf semantics ℓ : A → TM X
--
-- Two statements:
--   `nested-flat`   sample ℓ (join d) ≈ sample (sample ℓ) d     (substitution, `foldT-bind`)
--   `nested-at`     deck step k, slide step j, animation time τ  =  time ι (k + j) + τ
--
-- Time is a parameter: `Clock` is a model (ordered-monoid fragment) with the laws used, and ℕ
-- is the tick clock read through ι.  Instance: ℚ (at the end).

module Slides.Spike.Stage4.Clock where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _▷_; Shape; Position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

------------------------------------------------------------------------
-- The signature (a restriction of Stage 2's `TimeC`; `Hold` is a pointwise guard, `Repeat`
-- is iterated `Seq`, `Drive` substitutes a value, not a clock: none moves time)

data TOp : Set where
  Seq Par : TOp
  Delay   : ℕ → TOp

tarity : TOp → Set
tarity Seq       = Fin 2
tarity Par       = Fin 2
tarity (Delay _) = ⊤

TimeC : Container 0ℓ 0ℓ
TimeC = TOp ▷ tarity

Scene : Set → Set
Scene A = TimeC ⋆ A

Deck : Set → Set
Deck A = Scene (Scene A)

join : ∀ {A} → Scene (Scene A) → Scene A
join d = d >>= λ s → s

fin2 : ∀ {A : Set} → A → A → Fin 2 → A
fin2 a b zero          = a
fin2 a b (suc zero)    = b
fin2 a b (suc (suc ()))

seqS parS : ∀ {A} → Scene A → Scene A → Scene A
seqS x y = impure (Seq , fin2 x y)
parS x y = impure (Par , fin2 x y)

------------------------------------------------------------------------
-- The model of time: what the temporal operations and the proofs use

record Clock : Set₁ where
  field
    T       : Set
    _+_ _-_ : T → T → T
    _<ᵇ_    : T → T → Bool
    ι       : ℕ → T                  -- the tick clock, read in T
    Nonneg  : T → Set
    +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    ι-+     : ∀ m n → ι (m ℕ.+ n) ≡ ι m + ι n
    +-minus : ∀ a b → (a + b) - a ≡ b
    nlt     : ∀ a b → Nonneg b → (a + b) <ᵇ a ≡ false
    nonneg-ι : ∀ n → Nonneg (ι n)
    nonneg-+ : ∀ {a b} → Nonneg a → Nonneg b → Nonneg (a + b)

module Sem (K : Clock) where
  open Clock K

  -- a timed value: a duration in ticks and a (partial) behaviour
  TM : Set → Set
  TM X = ℕ × (T → Maybe X)

  _∣ᵐ_ : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
  just x ∣ᵐ _ = just x
  nothing ∣ᵐ y = y

  seqT parT : ∀ {X : Set} → TM X → TM X → TM X
  seqT (n , f) (m , g) = n ℕ.+ m , λ τ → if τ <ᵇ ι n then f τ else g (τ - ι n)
  parT (n , f) (m , g) = n ℕ.⊔ m , λ τ → f τ ∣ᵐ g τ

  delayT : ∀ {X : Set} → ℕ → TM X → TM X
  delayT n (m , f) = n ℕ.+ m , λ τ → if τ <ᵇ ι n then nothing else f (τ - ι n)

  alg : ∀ {X : Set} (s : TOp) → (tarity s → TM X) → TM X
  alg Seq       k = seqT (k zero) (k (suc zero))
  alg Par       k = parT (k zero) (k (suc zero))
  alg (Delay n) k = delayT n (k tt)

  sample : ∀ {A X : Set} → (A → TM X) → Scene A → TM X
  sample ℓ (pure a)       = ℓ a
  sample ℓ (impure (s , k)) = alg s (λ p → sample ℓ (k p))

  -- equal duration, equal behaviour pointwise (no function extensionality)
  _≈_ : ∀ {X : Set} → TM X → TM X → Set
  x ≈ y = proj₁ x ≡ proj₁ y × ∀ τ → proj₂ x τ ≡ proj₂ y τ

  ≈-refl : ∀ {X : Set} {x : TM X} → x ≈ x
  ≈-refl = refl , λ _ → refl

  private
    ite : ∀ {X : Set} (b : Bool) {u u′ v v′ : Maybe X} → u ≡ u′ → v ≡ v′ → (if b then u else v) ≡ (if b then u′ else v′)
    ite true  p q = p
    ite false p q = q

    cong∣ : ∀ {X} {a a′ b b′ : Maybe X} → a ≡ a′ → b ≡ b′ → a ∣ᵐ b ≡ a′ ∣ᵐ b′
    cong∣ refl refl = refl

  -- the algebra respects ≈ in each child
  alg-cong : ∀ {X : Set} s {k k′ : tarity s → TM X} → (∀ p → k p ≈ k′ p) → alg s k ≈ alg s k′
  alg-cong Seq {k} {k′} h with k zero | k′ zero | k (suc zero) | k′ (suc zero) | h zero | h (suc zero)
  ... | n , f | .n , f′ | m , g | .m , g′ | refl , p | refl , q =
    refl , λ τ → ite (τ <ᵇ ι n) (p τ) (q (τ - ι n))
  alg-cong Par {k} {k′} h with k zero | k′ zero | k (suc zero) | k′ (suc zero) | h zero | h (suc zero)
  ... | n , f | .n , f′ | m , g | .m , g′ | refl , p | refl , q = refl , λ τ → cong∣ (p τ) (q τ)
  alg-cong (Delay n) {k} {k′} h with k tt | k′ tt | h tt
  ... | m , f | .m , f′ | refl , p = refl , λ τ → ite (τ <ᵇ ι n) refl (p (τ - ι n))

  -- SUBSTITUTION: sampling a bound scene is sampling with the leaf semantics substituted.
  nested-flat : ∀ {A B X : Set} (ℓ : B → TM X) (t : Scene A) (f : A → Scene B) →
                sample ℓ (t >>= f) ≈ sample (λ a → sample ℓ (f a)) t
  nested-flat ℓ (pure a) f = ≈-refl
  nested-flat ℓ (impure (s , k)) f = alg-cong s (λ p → nested-flat ℓ (k p) f)

  -- the clocks compose as a monoid action of ℕ on T
  at : ℕ → T → T
  at k τ = ι k + τ

  at-compose : ∀ k j τ → at k (at j τ) ≡ at (k ℕ.+ j) τ
  at-compose k j τ = trans (sym (+-assoc (ι k) (ι j) τ)) (cong (_+ τ) (sym (ι-+ k j)))

  -- sampling `seqT x y` strictly after `x` is sampling `y` on the shifted clock
  seq-right : ∀ {X : Set} (x y : TM X) τ → Nonneg τ → proj₂ (seqT x y) (at (proj₁ x) τ) ≡ proj₂ y τ
  seq-right (n , f) (m , g) τ nn rewrite nlt (ι n) τ nn | +-minus (ι n) τ = refl

  -- A deck `seqS p s` of slides: at deck step `dur p`, slide step j, animation time τ, the
  -- (nested) deck shows what the slide shows at `at j τ`.  Stated against the nested deck
  -- (leaves are slides) and, through `nested-flat`, against the flat scene.
  nested-at : ∀ {A X : Set} (ℓ : A → TM X) (p s : Scene A) j τ → Nonneg τ →
    proj₂ (sample (sample ℓ) (seqS (pure p) (pure s))) (at (proj₁ (sample ℓ p) ℕ.+ j) τ)
    ≡ proj₂ (sample ℓ s) (at j τ)
  nested-at ℓ p s j τ nn =
    trans (cong (proj₂ (seqT (sample ℓ p) (sample ℓ s))) (sym (at-compose (proj₁ (sample ℓ p)) j τ)))
          (seq-right (sample ℓ p) (sample ℓ s) (at j τ) (nonneg-+ (nonneg-ι j) nn))

  nested-at-flat : ∀ {A X : Set} (ℓ : A → TM X) (p s : Scene A) j τ → Nonneg τ →
    proj₂ (sample ℓ (join (seqS (pure p) (pure s)))) (at (proj₁ (sample ℓ p) ℕ.+ j) τ)
    ≡ proj₂ (sample ℓ s) (at j τ)
  nested-at-flat ℓ p s j τ nn =
    trans (proj₂ (nested-flat ℓ (seqS (pure p) (pure s)) (λ x → x)) _) (nested-at ℓ p s j τ nn)
