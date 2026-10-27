{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The embedding agrees with the existing continuous semantics: for a template-only animation
-- `toAnim t`, `animAt` is `animT t` (a fold without the `Maybe`), the duration of the scene is
-- `dur`, and at every whole tick the frames of the scene are the frames of `animAt`.
-- (At fractional times the two differ only where an operand is not windowed, and none is; that
-- is the 4-case ℚ-order argument `seqW` was introduced to avoid, not needed for the readings the
-- existing theorems cover.)

module Slides.Spike.Stage2.OldNew where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Syntax using (Dia; atop; Atop)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-∸)
import Slides.Anim.Track as Tr
import Slides.Anim.Track.Properties as TrP
import Slides.Anim.Syntax as A
open import Slides.Anim.Timeline using (mergeM)
open import Slides.Anim.Arith using (<ᵇ-ge; <ᵇ-false; <ᵇ-true; <ᵇ-lt)
open import Slides.Anim.Continuous
open import Slides.Anim.Continuous.Properties using (ι-<ᵗ; zero≤ι; sampleAt-dur)
open import Slides.Spike.Timed using (TM; mapT; fin2)
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.Scene.Properties

-- the old fold, on template-only animations (no `Maybe`)
animT : TAnim → Timed (Maybe (Dia ℚ))
animT (pure (tr , d))       = leafAt tr d
animT (impure (A.Seq , k))  = seqAt (animT (k zero)) (animT (k (suc zero)))
animT (impure (A.Par , k))  = parAt atop (animT (k zero)) (animT (k (suc zero)))

animAt-toAnim : ∀ t → animAt (toAnim t) ≡ just (animT t)
animAt-toAnim (pure s)              = refl
animAt-toAnim (impure (A.Seq , k))  rewrite animAt-toAnim (k zero) | animAt-toAnim (k (suc zero)) = refl
animAt-toAnim (impure (A.Par , k))  rewrite animAt-toAnim (k zero) | animAt-toAnim (k (suc zero)) = refl

animT-dur : ∀ t → proj₁ (animT t) ≡ A.dur (toAnim t)
animT-dur (pure (tr , d))       = trans (sampleAt-dur Tr.ℚLerp tr) (TrP.sample-dur Tr.ℚLerp tr)
animT-dur (impure (A.Seq , k))  = cong₂ ℕ._+_ (animT-dur (k zero)) (animT-dur (k (suc zero)))
animT-dur (impure (A.Par , k))  = cong₂ ℕ._⊔_ (animT-dur (k zero)) (animT-dur (k (suc zero)))

private
  <ᵇ-+ˡ : ∀ {k n} m → (k <ᵇ n) ≡ true → (k <ᵇ n + m) ≡ true
  <ᵇ-+ˡ {k} {n} m h = <ᵇ-true {k} {n + m} (ℕP.<-≤-trans {k} {n} {n + m} (<ᵇ-lt {k} {n} h) (ℕP.m≤m+n n m))

  contra : ∀ {X : Set} → true ≡ false → X
  contra ()

⊔-false : ∀ {k} n m → (k <ᵇ n ℕ.⊔ m) ≡ false → (k <ᵇ n) ≡ false × (k <ᵇ m) ≡ false
⊔-false n m h = <ᵇ-false (ℕP.≤-trans (ℕP.m≤m⊔n n m) (<ᵇ-ge h)) , <ᵇ-false (ℕP.≤-trans (ℕP.m≤n⊔m n m) (<ᵇ-ge h))

-- the scene shows nothing from its end on (small lemmas, so no scene is ever normalised)
private
  if-false : ∀ {A : Set} (b : Bool) (x y : A) → b ≡ false → (if b then x else y) ≡ y
  if-false .false x y refl = refl

out-Seq : ∀ {A} (X Y : TM A) k → (k <ᵇ proj₁ X + proj₁ Y) ≡ false → proj₂ (seqW X Y) (ι k) ≡ nothing
out-Seq X Y k h = trans (seqW-tick X Y k) (if-false _ _ _ h)

out-QS : ∀ t k → (k <ᵇ A.dur (toAnim t)) ≡ false → proj₂ (sample algD bindD (embed t)) (ι k) ≡ nothing
out-QS (pure (tr , d)) k h =
  trans (segS-at tr d (ι k)) (if-false _ _ _ (trans (cong₂ _∧_ (zero≤ι k) (trans (ι-<ᵗ k (Tr.dur tr)) h)) refl))
out-QS (impure (A.Seq , k′)) k h =
  out-Seq (sample algD bindD (embed (k′ zero))) (sample algD bindD (embed (k′ (suc zero)))) k
    (trans (cong (k <ᵇ_) (cong₂ ℕ._+_ (embed-dur (k′ zero)) (embed-dur (k′ (suc zero))))) h)
out-QS (impure (A.Par , k′)) k h =
  trans (cong₂ (mergeM (λ x y → algD Atop (fin2 x y)))
          (out-QS (k′ zero) k (proj₁ (⊔-false (A.dur (toAnim (k′ zero))) (A.dur (toAnim (k′ (suc zero)))) h)))
          (out-QS (k′ (suc zero)) k (proj₂ (⊔-false (A.dur (toAnim (k′ zero))) (A.dur (toAnim (k′ (suc zero)))) h))))
        refl

-- `seqW` against `seqAt` at whole ticks, for abstract operands (small terms: no normalisation of scenes)
seq-agree : ∀ {A B : Set} (h : A → B) (X Y : TM A) (X′ Y′ : Timed (Maybe B)) →
  proj₁ X ≡ proj₁ X′ → proj₁ Y ≡ proj₁ Y′ →
  (∀ k → Maybe.map h (proj₂ X (ι k)) ≡ proj₂ X′ (ι k)) →
  (∀ k → Maybe.map h (proj₂ Y (ι k)) ≡ proj₂ Y′ (ι k)) →
  (∀ k → (k <ᵇ proj₁ Y) ≡ false → proj₂ Y (ι k) ≡ nothing) →
  ∀ k → Maybe.map h (proj₂ (seqW X Y) (ι k)) ≡ proj₂ (seqAt X′ Y′) (ι k)
seq-agree h (n , f) (m , g) (n′ , f′) (m′ , g′) refl refl p q w k
  rewrite seqW-tick (n , f) (m , g) k | ι-<ᵗ k n with k <ᵇ n + m in e₁ | k <ᵇ n in e₂
... | true  | true  = p k
... | true  | false rewrite sym (ι-∸ k n (<ᵇ-ge e₂)) = q (k ∸ n)
... | false | true  = contra (trans (sym (<ᵇ-+ˡ {k} {n} m e₂)) e₁)
... | false | false rewrite sym (ι-∸ k n (<ᵇ-ge e₂)) =
  sym (trans (sym (q (k ∸ n))) (cong (Maybe.map h) (w (k ∸ n) (<ᵇ-shift-false n m e₁))))

map-merge : ∀ x y → Maybe.map (λ g → g 0ℚ) (mergeM (λ a b → algD Atop (fin2 a b)) x y)
                   ≡ mergeM atop (Maybe.map (λ g → g 0ℚ) x) (Maybe.map (λ g → g 0ℚ) y)
map-merge nothing  y        = refl
map-merge (just x) nothing  = refl
map-merge (just x) (just y) = refl

embed-agree : ∀ t k → proj₂ (framesD (embed t)) (ι k) ≡ proj₂ (animT t) (ι k)
embed-agree (pure (tr , d)) k = at≈ (segS-sample tr d) (ι k)
embed-agree (impure (A.Par , k′)) k =
  trans (map-merge (proj₂ (sample algD bindD (embed (k′ zero))) (ι k)) (proj₂ (sample algD bindD (embed (k′ (suc zero)))) (ι k)))
        (cong₂ (mergeM atop) (embed-agree (k′ zero) k) (embed-agree (k′ (suc zero)) k))
embed-agree (impure (A.Seq , k′)) k =
  seq-agree (λ g → g 0ℚ) (sample algD bindD (embed (k′ zero))) (sample algD bindD (embed (k′ (suc zero))))
    (animT (k′ zero)) (animT (k′ (suc zero)))
    (trans (embed-dur (k′ zero)) (sym (animT-dur (k′ zero)))) (trans (embed-dur (k′ (suc zero))) (sym (animT-dur (k′ (suc zero)))))
    (embed-agree (k′ zero)) (embed-agree (k′ (suc zero)))
    (λ j h → out-QS (k′ (suc zero)) j (subst (λ n → (j <ᵇ n) ≡ false) (embed-dur (k′ (suc zero))) h)) k
