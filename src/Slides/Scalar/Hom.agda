{-# OPTIONS --safe --without-K #-}

-- The model homomorphism ι : ℕ → ℚ, the lowerings for what it does not preserve, and
-- digitisation.
--
-- ι preserves the ordered monoid (`ι-hom`: 0, +, order both ways, hence ⊔ and comparison
-- selects), the scaling (`ι-scale`) and the ticks (`ι-floor`, `ι-hold`), unconditionally.
-- Exact subtraction is preserved only where it is exact (`ι-sub`, hypothesis `b ≤ a`; it fails
-- otherwise, `ι-sub-fails`), and a percentage is not preserved (`ι-pct-fails`: ℕ takes the floor
-- of a product).  Those two commands are lowered (`lowerS`, a Kleisli map of `ScC = SpaceC ⊎
-- TimeC`): `a - b` to `(a ⊔ b) - b` (the monus in any model) and `pct p x` to `hold (pct p x)`
-- (the floor of the product).  `digitise`: a ℕ-term evaluated at the image of a tick is ι of
-- its ℕ reading, once lowered; the one model fact about floors of percentages is the
-- hypothesis `PctDigital`.  Proofs use only the laws of the theory records (Core, Time) and
-- `Container.Interpret.Plain` (`pfold-lower`, `pfold-hom`); ℚ is computed in only for the two
-- counterexamples.

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

open import Container.Interpret.Plain using (Handler; pfold; pfold-ext; pfold-hom; pfold-lower)
open import Container.Lowering using (Lowering; lower; ret)
open import Slides.Scalar.Core
open import Slides.Scalar.Space
open import Slides.Scalar.Time
open import Slides.Scalar.Model.Nat
open import Slides.Scalar.Model.Rat

ι-hom : IsOrdMonHom natMon ratMon ι
ι-hom = record { h-0 = refl ; h-+ = ι-+ ; h-mono = ι-mono ; h-reflect = ι-reflect }

ι-⊔ : ∀ a b → ι (a ℕ.⊔ b) ≡ ι a ℚ.⊔ ι b
ι-⊔ = IsOrdMonHom.h-⊔ ι-hom

ι-scale : ∀ r x → ι (Scale._·_ natScale r x) ≡ Scale._·_ ratScale (ι r) (ι x)
ι-scale = ι-*

ι-sub : ∀ {a b} → b ℕ.≤ a → ι (a ∸ b) ≡ ι a ℚ.- ι b
ι-sub = IsOrdMonHom.h-sub ι-hom natSub ratSub

ι-sub-fails : ¬ (ι (0 ∸ 1) ≡ ι 0 ℚ.- ι 1)
ι-sub-fails ()

ι-pct-fails : ¬ (ι (Space.pct natSpace 50 1) ≡ Space.pct ratSpace 50 (ι 1))
ι-pct-fails ()

ι-floor : ∀ n → ratFloor (ι n) ≡ n
ι-floor = Time.floor-tick ratTime

ι-hold : ∀ n → ι (Time.hold natTime n) ≡ Time.hold ratTime (ι n)
ι-hold n = sym (Time.hold-tick ratTime n)

------------------------------------------------------------------------
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
    cmd (inj₁ Plus)    v = ι-+ _ _
    cmd (inj₁ Max)     v = ι-⊔ _ _
    cmd (inj₁ Lt)      v = trans (map-select ι (_ ℕ.≤? _) _ _)
                             (IsOrdMonHom.h-select ι-hom (_ ℕ.≤? _) (ℚP._≤?_ _ _) _ _)
    cmd (inj₁ Minus)   v = trans (cong ι (monus-max (v zero) (v (suc zero))))
                             (trans (ι-sub (ℕP.m≤n⊔m (v zero) (v (suc zero)))) (cong (ℚ._- _) (ι-⊔ _ _)))
    cmd (inj₁ (Pct p)) v = pct-ok p (v _)
    cmd (inj₂ Hold)    v = ι-hold (v _)


  -- Digitisation.  A ℕ-term at the image of its variables' values is ι of its ℕ reading,
  -- once lowered; so a tick-clock term is read in ℚ at the image of a tick.
  digitise : ∀ {V : Set} (ρ : V → ℕ) (t : ScC ⋆ V) →
             ι (pfold ScC scNat ρ t) ≡ pfold ScC scRat (ι ∘ ρ) (lower lowerS t)
  digitise ρ t = trans
    (pfold-hom ι (λ a e → pfold-ext (≡P.setoid ℚ) cℚ e (lowerS a)) cmd ρ t)
    (sym (pfold-lower (≡P.setoid ℚ) cℚ lowerS (ι ∘ ρ) t))
