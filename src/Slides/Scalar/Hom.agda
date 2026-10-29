{-# OPTIONS --safe --without-K #-}

-- The model homomorphism ι : ℕ → ℚ, the lowerings for what it does not preserve, digitisation.
--
-- Unconditional: the ordered monoid (`ι-hom`; hence ⊔ and comparison), scaling, ticks.
-- Conditional: `ι-sub` needs `b ≤ a` (`ι-sub-fails` otherwise).  Not preserved: percentages
-- (`ι-pct-fails`: ℕ floors a product).  `lowerS`, a Kleisli map of `ScC = SpaceC ⊎ TimeC`, sends
-- `a - b` to `(a ⊔ b) - b` and `pct p x` to `hold (pct p x)`.  `digitise`: a lowered ℕ-term at
-- the image of its variables is ι of its ℕ reading; the model fact about floors of percentages
-- is the hypothesis `PctDigital`.  Proofs use the laws of Core and Time and `pfold-bind`.

module Slides.Scalar.Hom where

open import Level using (0ℓ)
open import Data.Nat as ℕ using (ℕ; _∸_; _*_; _/_)
open import Data.Fin using (zero; suc)
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Container.Core using (Container; Shape; Position)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎ᶜ_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Function.Base using (_∘_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡P
import Data.Nat.Properties as ℕP
import Data.Rational.Properties as ℚP
open import Data.Product.Base using (_,_)

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pfold-hom)
open import Container.Lowering using (Lowering; lower; ret)
open import Slides.Scalar.Core
open import Slides.Scalar.Space
open import Slides.Scalar.Time
open import Slides.Scalar.Model.Nat
open import Slides.Scalar.Model.Rat

ι-hom : IsOrdMonHom natMon ratMon ι
ι-hom = record { h-0 = refl ; h-+ = ι-+ ; h-mono = ι-mono ; h-reflect = ι-reflect }
ι-scale-hom : IsScaleHom natScale ratScale ι ι
ι-scale-hom = record { h-· = ι-* }
ι-time-hom : IsTimeHom natTime ratTime ι
ι-time-hom = record { ord = ι-hom ; h-tick = λ _ → refl ; h-floor = Time.floor-tick ratTime }
ι-⊔ : ∀ a b → ι (a ℕ.⊔ b) ≡ ι a ℚ.⊔ ι b
ι-⊔ = IsOrdMonHom.h-⊔ ι-hom
ι-scale : ∀ r x → ι (Scale._·_ natScale r x) ≡ Scale._·_ ratScale (ι r) (ι x)
ι-scale = IsScaleHom.h-· ι-scale-hom
ι-sub : ∀ {a b} → b ℕ.≤ a → ι (a ∸ b) ≡ ι a ℚ.- ι b
ι-sub = IsOrdMonHom.h-sub ι-hom natSub ratSub
ι-sub-fails : ¬ (ι (0 ∸ 1) ≡ ι 0 ℚ.- ι 1)
ι-sub-fails ()
ι-pct-fails : ¬ (ι (Space.pct natSpace 50 1) ≡ Space.pct ratSpace 50 (ι 1))
ι-pct-fails ()
ι-hold : ∀ n → ι (Time.hold natTime n) ≡ Time.hold ratTime (ι n)
ι-hold = IsTimeHom.h-hold ι-time-hom
ι-rem : ∀ n → ι (Time.Rem.rem natTime natSub n) ≡ Time.Rem.rem ratTime ratSub (ι n)
ι-rem n = IsTimeHom.h-rem ι-time-hom natSub ratSub {n} ℕ.z≤n

-- Lowering

ScC : Container 0ℓ 0ℓ
ScC = SpaceC ⊎ᶜ TimeC

lowerS : Lowering ScC ScC
lowerS (inj₁ Minus)   = impure (inj₁ Minus , λ { zero → impure (inj₁ Max , pure) ; (suc zero) → pure (suc zero) })
lowerS (inj₁ (Pct p)) = impure (inj₂ Hold , λ _ → impure (inj₁ (Pct p) , pure))
lowerS s              = ret s

scNat : Handler ScC ℕ
scNat = spaceH natSpace ⊕ timeH natTime

scRat : Handler ScC ℚ
scRat = spaceH ratSpace ⊕ timeH ratTime

-- the model fact: the ℕ percentage is the floor of the ℚ one
PctDigital : Set
PctDigital = ∀ p n → ι (Space.pct natSpace p n) ≡ Time.hold ratTime (Space.pct ratSpace p (ι n))

module _ (pct-ok : PctDigital) where

  private
    cℚ : Congruent ScC (≡P.setoid ℚ) scRat
    cℚ = ⊕-cong (spaceCong ratSpace) (timeCong ratTime)

    map-select : ∀ {a b} (f : ℕ → ℚ) (d : Dec (a ℕ.≤ b)) x y →
                 f (OrdMon.select natMon d x y) ≡ OrdMon.select natMon d (f x) (f y)
    map-select f (yes _) x y = refl
    map-select f (no _)  x y = refl

    monus-max : ∀ a b → a ∸ b ≡ (a ℕ.⊔ b) ∸ b
    monus-max a b with ℕP.≤-total a b
    ... | inj₁ a≤b rewrite ℕP.m≤n⇒m⊔n≡n a≤b = trans (ℕP.m≤n⇒m∸n≡0 a≤b) (sym (ℕP.n∸n≡0 b))
    ... | inj₂ b≤a rewrite ℕP.m≥n⇒m⊔n≡m b≤a = refl

    -- ι of each ℕ command is the lowered command in ℚ
    cmd : ∀ a (v : Position ScC a → ℕ) →
          ι (scNat a v) ≡ pfold ScC scRat (λ q → ι (v q)) (lowerS a)
    cmd (inj₁ Zero)    v = refl
    cmd (inj₁ Plus)    v = ι-+ (v zero) (v (suc zero))
    cmd (inj₁ Max)     v = ι-⊔ (v zero) (v (suc zero))
    cmd (inj₁ Lt)      v = trans (map-select ι (v₀ ℕ.≤? v₁) v₂ v₃)
                             (IsOrdMonHom.h-select ι-hom {a = v₀} {b = v₁} (v₀ ℕ.≤? v₁) (ℚP._≤?_ (ι v₀) (ι v₁)) (ι v₂) (ι v₃))
      where v₀ = v zero ; v₁ = v (suc zero) ; v₂ = v (suc (suc zero)) ; v₃ = v (suc (suc (suc zero)))
    cmd (inj₁ Minus)   v = trans (cong ι (monus-max (v zero) (v (suc zero))))
                             (trans (ι-sub {v zero ℕ.⊔ v (suc zero)} {v (suc zero)} (ℕP.m≤n⊔m (v zero) (v (suc zero))))
                                    (cong (λ y → y ℚ.- ι (v (suc zero))) (ι-⊔ (v zero) (v (suc zero)))))
    cmd (inj₁ (Pct p)) v = pct-ok p (v _)
    cmd (inj₂ Hold)    v = ι-hold (v _)


  -- Digitisation: a lowered ℕ-term at the image of its variables is ι of its ℕ reading.
  digitise : ∀ {V : Set} (ρ : V → ℕ) (t : ScC ⋆ V) →
             ι (pfold ScC scNat ρ t) ≡ pfold ScC scRat (ι ∘ ρ) (lower lowerS t)
  digitise ρ t = pfold-hom (≡P.setoid ℚ) cℚ ι scNat lowerS cmd ρ t
