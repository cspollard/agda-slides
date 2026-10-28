{-# OPTIONS --safe --without-K #-}

-- Laws of continuous time: at whole ticks the continuous sample of a track is the discrete one (`sampleAt-ι`),
-- a piece holds its end, `Seq` offsets time and `Par` shares it, the duration of `animAt` is `dur`, and the
-- continuous frame of a template segment at a whole tick is the discrete frame sent through `ι` (`leaf-tick`).
module Slides.Anim.Continuous.Properties where

open import Data.Bool using (true; false; not; if_then_else_; T)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.NatQ using (ι)

open import Slides.Diagram.NatQ.Properties using (ι-≤ᵇ; ι-∸; ι-ratio)
import Slides.Anim.Track as Tr
import Slides.Anim.Track.Properties as TrP
open import Slides.Diagram.Ordered.Properties using (ι-<ᵇ)
open import Slides.Anim.Syntax using (units; bodyAt; track; content; template; blackBox; dur; Seq; Par)
open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Ordered.Properties.Faithful using (AllLayout; FaithfulO; faithful-layout)
open import Slides.Diagram.Ordered using (natO; termOps; _<ᵇℚ_)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (ratOps; natOps)
open import Slides.Diagram.Syntax using (atop)

open import Slides.Anim.Continuous

------------------------------------------------------------------------
-- Whole ticks: the continuous sample is the discrete one

ratioAt-ι : ∀ k d → ratioAt (ι k) d ≡ Tr.ratio k d
ratioAt-ι k zero    = refl
ratioAt-ι k (suc d) =
  trans (cong (λ c → if c then ι k ℚ.* (+ 1 / suc d) else 1ℚ) (ι-<ᵇ k (suc d))) (go (k ℕ.<ᵇ suc d))
  where go : ∀ b → (if b then ι k ℚ.* (+ 1 / suc d) else 1ℚ) ≡ (if b then + k / suc d else 1ℚ)
        go true  = ι-ratio k d
        go false = refl

pieceAt-ι : ∀ {A} (L : Tr.Lerp A) (p : Tr.Piece A) k →
            pieceAt L p (ι k) ≡ proj₂ (Tr.samplePiece L p) k
pieceAt-ι L (Tr.piece d a b e) k = cong (λ r → Tr.Lerp.lerp L (Tr.progress e r) a b) (ratioAt-ι k d)

sampleAt-dur : ∀ {A} (L : Tr.Lerp A) (tr : Tr.Track A) → proj₁ (sampleAt L tr) ≡ proj₁ (Tr.sample L tr)
sampleAt-dur L (pure p)         = refl
sampleAt-dur L (impure (_ , c)) = cong₂ ℕ._+_ (sampleAt-dur L (c zero)) (sampleAt-dur L (c (suc zero)))

-- A track sampled at whole ticks of real time is the track sampled by ticks.
sampleAt-ι : ∀ {A} (L : Tr.Lerp A) (tr : Tr.Track A) k →
             proj₂ (sampleAt L tr) (ι k) ≡ proj₂ (Tr.sample L tr) k
sampleAt-ι L (pure p) k = pieceAt-ι L p k
sampleAt-ι L (impure (_ , c)) k
  rewrite sampleAt-dur L (c zero) | ι-<ᵇ k (proj₁ (Tr.sample L (c zero)))
  with k ℕ.<ᵇ proj₁ (Tr.sample L (c zero)) in eq
... | true  = sampleAt-ι L (c zero) k
... | false = trans (cong (proj₂ (sampleAt L (c (suc zero))))
                          (sym (ι-∸ k m (ℕP.≮⇒≥ (λ h → subst T eq (ℕP.<⇒<ᵇ h))))))
                    (sampleAt-ι L (c (suc zero)) (k ℕ.∸ m))
  where m = proj₁ (Tr.sample L (c zero))

-- the first facts about the track at real time: a piece holds `to` once it is over, at a
-- boundary the *later* piece takes over (right-continuity), and sequencing offsets time
piece-hold : ∀ {A} (L : Tr.Lerp A) d a b e τ → (τ <ᵇℚ ι d) ≡ false →
             pieceAt L (Tr.piece d a b e) τ ≡ b
piece-hold L zero    a b e τ _ = trans (cong (λ p → Tr.Lerp.lerp L p a b) (TrP.progress-1 e)) (Tr.Lerp.lerp-1 L a b)
piece-hold L (suc d) a b e τ h
  rewrite h = trans (cong (λ p → Tr.Lerp.lerp L p a b) (TrP.progress-1 e)) (Tr.Lerp.lerp-1 L a b)

-- the duration of the timed frames is the duration of the animation
segAt-dur : ∀ s T → segAt s ≡ just T → proj₁ T ≡ Tr.dur (track s)
segAt-dur s T eq = go (track s) (content s) T eq
  where
    go : ∀ tr b T → bodyAt′ tr b ≡ just T → proj₁ T ≡ Tr.dur tr
    go tr (template d) _ refl = trans (sampleAt-dur Tr.ℚLerp tr) (TrP.sample-dur Tr.ℚLerp tr)
    go tr (blackBox _) _ ()

-- the parts of a `lift2` that is there
lift2-just : ∀ {A : Set} (f : A → A → A) x y {T} → lift2 f x y ≡ just T →
               ∃₂ λ a b → x ≡ just a × y ≡ just b × f a b ≡ T
lift2-just f (just a) (just b) refl = a , b , refl , refl , refl
lift2-just f (just a) nothing  ()
lift2-just f nothing  y        ()

animAt-dur : ∀ a T → animAt a ≡ just T → proj₁ T ≡ dur a
animAt-dur (pure s) T eq = segAt-dur s T eq
animAt-dur (impure (Seq , k)) T eq with lift2-just seqAt (animAt (k zero)) (animAt (k (suc zero))) eq
... | A , B , e₁ , e₂ , refl = cong₂ ℕ._+_ (animAt-dur (k zero) A e₁) (animAt-dur (k (suc zero)) B e₂)
animAt-dur (impure (Par , k)) T eq with lift2-just (parAt atop) (animAt (k zero)) (animAt (k (suc zero))) eq
... | A , B , e₁ , e₂ , refl = cong₂ ℕ._⊔_ (animAt-dur (k zero) A e₁) (animAt-dur (k (suc zero)) B e₂)

------------------------------------------------------------------------
-- A template segment at whole ticks

zero≤ι : ∀ k → (0ℚ ℚ.≤ᵇ ι k) ≡ true
zero≤ι k = ι-≤ᵇ 0 k

-- At a whole tick the continuous frame of a segment is its template at the track's tick
-- sample, exactly (no flooring).
leafAt-ι : ∀ tr d k → (k ℕ.<ᵇ Tr.dur tr) ≡ true →
           proj₂ (leafAt tr d) (ι k) ≡ just (instQ d (proj₂ (Tr.sample Tr.ℚLerp tr) k))
leafAt-ι tr d k hk
  rewrite sampleAt-dur Tr.ℚLerp tr | TrP.sample-dur Tr.ℚLerp tr
        | ι-<ᵇ k (Tr.dur tr) | hk | zero≤ι k
  = cong (λ q → just (instQ d q)) (sampleAt-ι Tr.ℚLerp tr k)

-- ... and that is the discrete frame sent through `ι` whenever the discrete reading was
-- exact: the sample is a whole number `m`, and the template's layout is exact at `m`
-- (`Slides.Diagram.Ordered.Properties.Faithful`: no monus that truncates, no percentage that rounds).
leaf-tick : ∀ tr d k → (k ℕ.<ᵇ Tr.dur tr) ≡ true →
            let q = proj₂ (Tr.sample Tr.ℚLerp tr) k in
            q ≡ ι (units q) →
            AllLayout (FaithfulO (λ _ → units q)) (LayoutWith.layout termOps d) →
            Maybe.map (LayoutWith.layout ratOps) (proj₂ (leafAt tr d) (ι k))
            ≡ just (mapLayout ι (LayoutWith.layout natOps (bodyAt natO (template d) q)))
leaf-tick tr d k hk whole ok rewrite leafAt-ι tr d k hk =
  cong just (trans (cong (λ r → LayoutWith.layout ratOps (instQ d r)) whole)
                   (sym (faithful-layout (λ _ → units q) d ok)))
  where q = proj₂ (Tr.sample Tr.ℚLerp tr) k

-- a piece of positive length starts at `from` (time 0 is the start)
piece-start : ∀ {A} (L : Tr.Lerp A) d a b e → pieceAt L (Tr.piece (suc d) a b e) 0ℚ ≡ a
piece-start L d a b e
  rewrite ι-≤ᵇ (suc d) 0 | ℚP.*-zeroˡ (+ 1 / suc d) | TrP.progress-0 e = Tr.Lerp.lerp-0 L a b
