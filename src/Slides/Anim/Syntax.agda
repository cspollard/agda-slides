{-# OPTIONS --safe --without-K #-}

-- The animation language: temporal media after Hudak, as a free monad.
--
-- `AnimC` is the container of the two temporal connectives, `Seq` (one after the
-- other) and `Par` (together), each with two children.  Its leaves are
-- *segments*: a diagram shown for a whole number of ticks.  So
--
--     Anim S = AnimC ⋆ Seg S
--
-- `fmap` restyles every segment, `>>=` replaces a segment by an animation (a
-- tween is such a replacement), and `foldA` interprets a term in an algebra.
-- Durations are whole ticks because reveal advances in steps and a fractional
-- duration breaks `zero (a + b) = zero a ++ zero b` once sampled (Hudak).
--
-- `dur` is the first algebra: `Seq` adds, `Par` takes the maximum.  `par` is
-- well formed by construction: it pads the shorter side with an empty segment,
-- so both sides of every `Par` that the smart constructors build last equally
-- long.

module Slides.Anim.Syntax where

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; _+_; _⊔_; _∸_; _≤_; _<ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Data.Bool using (T)
open import Data.Unit using (tt)

open import Slides.Diagram.Syntax using (Dia; spacer)
open import Slides.Diagram.Scalar using (Ops)
import Slides.Anim.Track as T
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer as ℤ using ()

------------------------------------------------------------------------
-- The signature

data Op : Set where
  Seq Par : Op

AnimC : Container 0ℓ 0ℓ
AnimC = Op ▷ (λ _ → Fin 2)

-- A segment: a diagram that depends on a parameter, which follows a track for as
-- many ticks as the track lasts.  The track is explicit data (`Slides.Anim.Track`:
-- pieces with easings, steps for discontinuities); the body is the diagram as a
-- function of the parameter, so reflow (a spacer that grows) and paint (an
-- opacity in a style) are both just uses of the parameter.  A diagram held for
-- `n` ticks is the constant track.
record Seg (S : Set) : Set where
  constructor seg
  field
    track : T.Track ℚ
    body  : ℚ → Dia S
open Seg public

ticks : ∀ {S} → Seg S → ℕ
ticks s = T.dur (track s)

-- An animation over leaves `T`
Anim : Set → Set → Set
Anim S T = AnimC ⋆ T

private
  pick2 : ∀ {A : Set} → A → A → Fin 2 → A
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

infixr 6 _⨾_
infixr 7 _∥ᵃ_

_⨾_ _∥ᵃ_ : ∀ {T} → AnimC ⋆ T → AnimC ⋆ T → AnimC ⋆ T
a ⨾ b  = impure (Seq , pick2 a b)
a ∥ᵃ b = impure (Par , pick2 a b)

-- A segment as a one-leaf animation
hold : ∀ {S} → ℕ → Dia S → Anim S (Seg S)
hold n d = pure (seg (pure (T.piece n 0ℚ 0ℚ T.Linear)) (λ _ → d))

-- a parameter as a whole number of the scalar's units (rounded down, negatives clamp)
units : ℚ → ℕ
units q = ℤ.∣ ℚ.⌊ q ⌋ ∣

-- a parameter moving from `a` to `b` in `n` ticks along an easing
tween : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → (ℚ → Dia S) → Anim S (Seg S)
tween n a b e f = pure (seg (pure (T.piece n a b e)) f)

-- a pause: an empty frame, which needs the scalar's zero
none : ∀ {S} → Ops S → ℕ → Anim S (Seg S)
none O n = hold n (spacer 0# 0#) where open Ops O

------------------------------------------------------------------------
-- Duration: the algebra into (ℕ, +, max)

-- fold of a program with leaves, into any carrier that has `Seq` and `Par`
foldA : ∀ {T A : Set} → (T → A) → (A → A → A) → (A → A → A) → AnimC ⋆ T → A
foldA leaf sq pr (pure t)              = leaf t
foldA leaf sq pr (impure (Seq , k))    = sq (foldA leaf sq pr (k zero)) (foldA leaf sq pr (k (suc zero)))
foldA leaf sq pr (impure (Par , k))    = pr (foldA leaf sq pr (k zero)) (foldA leaf sq pr (k (suc zero)))

dur : ∀ {S} → Anim S (Seg S) → ℕ
dur = foldA ticks _+_ _⊔_

-- `foldA` commutes with `>>=` (a tween is a bind): substituting then folding is
-- folding with the folded substitution.  No extensionality is needed because
-- `Fin 2` continuations are applied at `zero` and `suc zero` only.
foldA-bind : ∀ {T U A : Set} (leaf : U → A) sq pr (m : AnimC ⋆ T) (g : T → AnimC ⋆ U) →
             foldA leaf sq pr (m >>= g) ≡ foldA (λ t → foldA leaf sq pr (g t)) sq pr m
foldA-bind leaf sq pr (pure t) g = refl
foldA-bind leaf sq pr (impure (Seq , k)) g =
  cong₂ sq (foldA-bind leaf sq pr (k zero) g) (foldA-bind leaf sq pr (k (suc zero)) g)
foldA-bind leaf sq pr (impure (Par , k)) g =
  cong₂ pr (foldA-bind leaf sq pr (k zero) g) (foldA-bind leaf sq pr (k (suc zero)) g)

dur-⨾ : ∀ {S} (a b : Anim S (Seg S)) → dur (a ⨾ b) ≡ dur a + dur b
dur-⨾ a b = refl

dur-∥ : ∀ {S} (a b : Anim S (Seg S)) → dur (a ∥ᵃ b) ≡ dur a ⊔ dur b
dur-∥ a b = refl

dur-none : ∀ {S} (O : Ops S) n → dur (none O n) ≡ n
dur-none O n = refl

------------------------------------------------------------------------
-- Well-formed parallel composition: pad the shorter side

-- extend to at least `n` ticks
pad : ∀ {S} → Ops S → ℕ → Anim S (Seg S) → Anim S (Seg S)
pad O n a with dur a <ᵇ n
... | true  = a ⨾ none O (n ∸ dur a)
... | false = a

dur-pad : ∀ {S} (O : Ops S) n (a : Anim S (Seg S)) → dur (pad O n a) ≡ dur a ⊔ n
dur-pad O n a with dur a <ᵇ n in eq
... | true  = trans (ℕP.m+[n∸m]≡n lt) (sym (ℕP.m≤n⇒m⊔n≡n lt))
  where lt = ℕP.<⇒≤ (ℕP.<ᵇ⇒< (dur a) n (subst T (sym eq) tt))
... | false = sym (ℕP.m≥n⇒m⊔n≡m (ℕP.≮⇒≥ (λ h → subst T eq (ℕP.<⇒<ᵇ h))))

-- both sides padded to the longer: a `Par` of equal durations
par : ∀ {S} → Ops S → Anim S (Seg S) → Anim S (Seg S) → Anim S (Seg S)
par O a b = pad O (dur b) a ∥ᵃ pad O (dur a) b

-- the two sides of `par` last equally long, and as long as the longer input
par-balanced : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) → dur (pad O (dur b) a) ≡ dur (pad O (dur a) b)
par-balanced O a b = trans (dur-pad O (dur b) a) (trans (ℕP.⊔-comm (dur a) (dur b)) (sym (dur-pad O (dur a) b)))

dur-par : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) → dur (par O a b) ≡ dur a ⊔ dur b
dur-par O a b = trans (cong₂ _⊔_ (dur-pad O (dur b) a) (dur-pad O (dur a) b))
                      (trans (cong ((dur a ⊔ dur b) ⊔_) (ℕP.⊔-comm (dur b) (dur a)))
                             (ℕP.⊔-idem (dur a ⊔ dur b)))
