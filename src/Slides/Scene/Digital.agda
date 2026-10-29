{-# OPTIONS --safe --without-K #-}

-- The ℕ tick clock, read through ι.
--
-- A scene on the whole-tick clock has durations in ℕ, drivers that are terms of the Space and
-- Time signatures in the local tick (`Dn`), and leaves that are diagrams of such terms
-- attached by sides (`SLeaf`).  Mapped along `ι : ℕ → ℚ` (`Slides.Scene.Tick`) the durations
-- become ℚ durations and the scalars are *lowered* by `lowerS` (`a - b` to `(a ⊔ b) - b`, `pct`
-- to `hold (pct ..)`), and then
--
--     digital:   reading the mapped scene in ℚ at the tick `ι n`, and then forgetting the
--                lowering, is the ℕ reading at `n`, mapped by `ι`
--
-- with the leaf case by Step 2's `digitise` (not re-proved) and Step 3's naturality of layout
-- (`layoutH-nat`), the hypothesis on percentages being `PctDigital`.  Leaves must attach by sides
-- (`Sides`): `ι` does not preserve every percentage port.  Moving ℚ drivers (Coupling terms,
-- `Slides.Scene.Moving`) carry along `ι` exactly when they are exact at whole ticks; here the
-- ℕ drivers are digital terms, so this is the discrete clock of the legacy `RelN`.

open import Slides.Scalar.Hom using (PctDigital)

module Slides.Scene.Digital (pct-ok : PctDigital) where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe as Maybe
import Data.List.Properties as ListP
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Container.Core using (position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pfold-ext)
open import Container.Lowering using (lower)
open import Slides.Scalar.Core using (_⊕_; ⊕-cong)
open import Slides.Scalar.Time using (timeCong)
open import Slides.Scalar.Hom using (ScC; scNat; scRat; lowerS; ι-hom; ι-⊔; digitise)
open import Slides.Scalar.Model.Nat
open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ι)
open import Slides.Scalar.Space using (Space; spaceCong)
open import Slides.Diagram.Draw using (Layout; mkLayout; mapLayout; mapPt)
import Data.Nat as ℕ
open import Slides.Diagram.Geometry using (Port; side; at)
open import Slides.Diagram.Syntax
import Slides.Diagram.Layout natSpace as LN
import Slides.Diagram.Layout ratSpace as LQ
import Slides.Diagram.Place ratSpace as PQ
import Slides.Diagram.Natural natSpace ratSpace ι ι-hom as N
open import Slides.Scene.Syntax using (Scene; mapScene)

------------------------------------------------------------------------
-- The two clocks: drivers and leaves are scalar terms in one variable

Sc : Set
Sc = ScC ⋆ Maybe ℕ

Dn : Set
Dn = Sc

-- ℕ: the variable is the local tick, `just k` the constant `k`
valN : Dn → ℕ → ℕ
valN c τ = pfold ScC scNat (maybe (λ k → k) τ) c

-- ℚ: the lowered term, at the tick `τ`, constants read through `ι`
valuation : ℚ → Maybe ℕ → ℚ
valuation τ = maybe ι τ

valQ : Dn → ℚ → ℚ
valQ c τ = pfold ScC scRat (valuation τ) c

lowerD : Dn → Dn
lowerD = lower lowerS

cQ : Congruent ScC (≡P.setoid ℚ) scRat
cQ = ⊕-cong (spaceCong ratSpace) (timeCong ratTime)

-- the variable is the same after `ι`: the valuation of the lowered term at `ι τ`
val-ι : ∀ τ v → ι (maybe (λ k → k) τ v) ≡ valuation (ι τ) v
val-ι τ nothing  = refl
val-ι τ (just k) = refl

-- digitisation of terms: lowered, at `ι` of the valuation, is `ι` of the reading
digit-term : ∀ τ t → pfold ScC scRat (valuation (ι τ)) (lowerD t) ≡ ι (pfold ScC scNat (maybe (λ k → k) τ) t)
digit-term τ t = trans (sym (pfold-ext (≡P.setoid ℚ) cQ (val-ι τ) (lowerD t)))
                       (sym (digitise pct-ok (maybe (λ k → k) τ) t))

g-val : ∀ c τ → valQ (lowerD c) (ι τ) ≡ ι (valN c τ)
g-val c τ = digit-term τ c

------------------------------------------------------------------------
-- Leaves: diagrams of terms, attached by sides

IsSide : Port → Set
IsSide (side _) = ⊤
IsSide (at _ _) = ⊥

SidesOp : ∀ {S} → Op S → Set
SidesOp (Connect _ pa _ pb _) = IsSide pa × IsSide pb
SidesOp _                     = ⊤

SidesDia : ∀ {S} → Dia S → Set
SidesDia (pure ())
SidesDia (impure (o , k)) = SidesOp o × (∀ p → SidesDia (k p))

private
  portOK : ∀ p → IsSide p → N.PortNat p
  portOK (side s) _ = N.side-nat s
  portOK (at _ _) ()

  okOp : ∀ (f : Sc → ℕ) o → SidesOp o → N.OkOp (mapOp f o)
  okOp f (Rectangle _ _ _) _ = tt
  okOp f (Segment _ _ _)   _ = tt
  okOp f (Disc _ _)        _ = tt
  okOp f (Ellipse _ _ _)   _ = tt
  okOp f (Polyline _ _ _)  _ = tt
  okOp f (Text _ _ _ _ _)  _ = tt
  okOp f (Path _ _ _ _)    _ = tt
  okOp f (Spacer _ _)      _ = tt
  okOp f (Beside _)        _ = tt
  okOp f (Above _)         _ = tt
  okOp f Atop              _ = tt
  okOp f LabelAbove        _ = tt
  okOp f LabelBelow        _ = tt
  okOp f (Place _ _ _ _)   _ = tt
  okOp f (Overlay _ _)     _ = tt
  okOp f (Named _)         _ = tt
  okOp f (Connect _ pa _ pb _) (ha , hb) = portOK pa ha , portOK pb hb

-- A leaf, instantiated at a parameter, is laid out the same way before and after `ι`, if the
-- two scalar readings agree through `ι` (`e`): one equation per command, `layoutH-nat`, then the
-- scalars of the command agree.
module _ (f₁ : Sc → ℕ) (f₂ : Sc → ℚ) (e : ∀ x → ι (f₁ x) ≡ f₂ x) where

  digit : ∀ o (kk : arity o → Layout ℚ) →
          LQ.layoutH (mapOp ι (mapOp f₁ o)) (λ q → kk (position (mapC f₁) (position (mapC ι) q)))
          ≡ LQ.layoutH (mapOp f₂ o) (λ q → kk (position (mapC f₂) q))
  digit (Rectangle w h s) kk rewrite e w | e h = refl
  digit (Segment w h s)   kk = cong₂ (λ a b → PQ.segment a b s) (e w) (e h)
  digit (Disc r s)        kk = cong (λ a → PQ.disc a s) (e r)
  digit (Ellipse a b s)   kk = cong₂ (λ x y → PQ.ellipseL x y s) (e a) (e b)
  digit (Polyline c ps s) kk =
    cong (λ qs → PQ.polyline c qs s)
         (trans (sym (ListP.map-∘ ps)) (ListP.map-cong (λ p → cong₂ _,_ (e (proj₁ p)) (e (proj₂ p))) ps))
  digit (Text w h n t s)  kk rewrite e w | e h = refl
  digit (Path w h d s)    kk rewrite e w | e h = refl
  digit (Spacer w h)      kk rewrite e w | e h = refl
  digit (Beside _)        kk = refl
  digit (Above _)         kk = refl
  digit Atop              kk = refl
  digit LabelAbove        kk = refl
  digit LabelBelow        kk = refl
  digit (Place w h x y)   kk = cong₂ (λ (a : ℚ × ℚ) (b : ℚ × ℚ) → PQ.place (proj₁ a) (proj₂ a) (proj₁ b) (proj₂ b) (kk tt))
                                    (cong₂ _,_ (e w) (e h)) (cong₂ _,_ (e x) (e y))
  digit (Overlay w h)     kk rewrite e w | e h = refl
  digit (Named _)         kk = refl
  digit (Connect _ _ _ _ _) kk = refl

  leaf-ok : ∀ (a : Dia Sc) → SidesDia a →
            LQ.layout (mapDia f₂ a) ≡ mapLayout ι (LN.layout (mapDia f₁ a))
  leaf-ok (pure ())
  leaf-ok (impure (o , k)) (so , sks) =
    trans (LQ.layoutCong (mapOp f₂ o) (λ q → leaf-ok (k (position (mapC f₂) q)) (sks _)))
      (trans (sym (digit o kk))
             (sym (N.layoutH-nat (mapOp f₁ o) kN (okOp f₁ o so))))
    where
      kk : arity o → Layout ℚ
      kk p = mapLayout ι (LN.layout (mapDia f₁ (k p)))
      kN : arity (mapOp f₁ o) → Layout ℕ
      kN q = LN.layout (mapDia f₁ (k (position (mapC f₁) q)))

------------------------------------------------------------------------
-- The two readings of one scene

SLeaf : Set
SLeaf = Σ[ a ∈ Dia Sc ] SidesDia a

-- a leaf at the parameter `p`: its scalars read on each clock (ℚ: lowered, constants through `ι`)
evN : ℕ → Sc → ℕ
evN p = pfold ScC scNat (maybe (λ k → k) p)

evQ : ℚ → Sc → ℚ
evQ p t = pfold ScC scRat (valuation p) (lowerD t)

ℓN : SLeaf → ℕ → Layout ℕ
ℓN (a , _) p = LN.layout (mapDia (evN p) a)

ℓQ : SLeaf → ℚ → Layout ℚ
ℓQ (a , _) p = LQ.layout (mapDia (evQ p) a)

ℓ-ok : ∀ a p → ℓQ a (ι p) ≡ mapLayout ι (ℓN a p)
ℓ-ok (a , sides) p = leaf-ok (evN p) (evQ (ι p)) (λ t → sym (digit-term p t)) a sides

import Slides.Scene.Animation natSpace natTime valN as AN
import Slides.Scene.Animation ratSpace ratTime valQ as AQ

open import Slides.Scene.Tick {ℕ} {ℚ} {Dn} {Dn} {Layout ℕ} {Layout ℚ}
  (Space.ord natSpace) (Space.sub natSpace) (Space.ord ratSpace) (Space.sub ratSpace)
  ι ι-hom valN valQ lowerD g-val AN.layoutOverlay AQ.layoutOverlay (mapLayout ι) N.overlay-hom
  using (tick-hom)

import Slides.Scene.Sample {D = Dn} {Layout ℕ} (Space.ord natSpace) (Space.sub natSpace) valN AN.layoutOverlay as SN
import Slides.Scene.Sample {D = Dn} {Layout ℚ} (Space.ord ratSpace) (Space.sub ratSpace) valQ AQ.layoutOverlay as SQ

-- the frame of a scene at the whole tick `n`, on the ℕ clock
frameN : Scene ℕ Dn SLeaf → ℕ → Maybe (Layout ℕ)
frameN s n = proj₂ (SN.sample ℓN s) n nothing

-- ... and on the ℚ clock, at the tick `ι n`, of the scene mapped along `ι`
frameQ : Scene ℚ Dn SLeaf → ℕ → Maybe (Layout ℚ)
frameQ s n = proj₂ (SQ.sample ℓQ s) (ι n) nothing

-- The tick clock reading: the ℚ frame of the mapped scene at `ι n`, up to `ι`, is the ℕ frame.
digital : ∀ s n → frameQ (mapScene ι lowerD s) n ≡ Maybe.map (mapLayout ι) (frameN s n)
digital s n = proj₂ (tick-hom ℓN ℓQ ℓ-ok s) n nothing

-- and the durations map by `ι`
digital-duration : ∀ s → proj₁ (SQ.sample ℓQ (mapScene ι lowerD s)) ≡ ι (proj₁ (SN.sample ℓN s))
digital-duration s = proj₁ (tick-hom ℓN ℓQ ℓ-ok s)
