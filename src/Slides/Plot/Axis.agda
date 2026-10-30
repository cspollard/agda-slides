{-# OPTIONS --safe --without-K #-}

-- An axis: the map from data to whole pixels, over the theories already there.
--
-- Data live in a Time `K` (floor and whole ticks), with exact subtraction `Sub` and scaling by
-- ratios `Scale` (ℚ over itself is the model).  An axis shows the data range `lo … hi` on `extent`
-- pixels, `ratio` pixels per unit of data, and
--
--     px x = min extent (floor (ratio · (max lo x − lo)))
--
-- so a value below the range sits on the first pixel and one above it on the last (a total map:
-- clipping a point to the box is `px`, clipping a segment is `Clip`).  The laws, all from the
-- theories and none by computing in ℚ:
--
--   px-mono   x ≤ y → px x ≤ px y          px-lo   px lo ≡ 0
--   px-max    px x ≤ extent                px-hi   px hi ≡ extent
--
-- `ratio` being the pixels per unit is a model fact, carried by the axis (`span-ratio`), and
-- built for ℚ by `Slides.Plot.Axis.Rat`.  y is drawn downwards: `flipY` is `extent ∸ px`.

open import Slides.Scalar.Core using (OrdMon; Sub)
open import Slides.Scalar.Space using (Scale)
open import Slides.Scalar.Time using (Time)

module Slides.Plot.Axis {K : Set} (Tm : Time K) (Sb : Sub (Time.ord Tm)) (Sc : Scale (Time.ord Tm) K) where

open import Data.Nat as ℕ using (ℕ; _∸_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open Time Tm
open Sub Sb
open Scale Sc using (_·_; 0r; _≤r_; ·-dist; ·-mono)

-- the range, the pixels and the model fact that `ratio` is pixels per unit
record Axis : Set where
  field
    lo hi    : K
    extent   : ℕ
    ratio    : K
    lo≤hi    : lo ≤ hi
    ratio≥0  : 0r ≤r ratio
    span-ratio : ratio · (hi - lo) ≡ tick extent

module _ (a : Axis) where
  open Axis a

  -- the part of the range a value is in, in data units
  offset : K → K
  offset x = (lo ⊔ x) - lo

  px : K → ℕ
  px x = extent ℕ.⊓ floor (ratio · offset x)

  flipY : K → ℕ
  flipY x = extent ∸ px x

  private
    ⊔-mono : ∀ {x y} → x ≤ y → lo ⊔ x ≤ lo ⊔ y
    ⊔-mono x≤y = ⊔-lub (⊔-ub₁ lo _) (≤-trans x≤y (⊔-ub₂ lo _))

    -- subtracting a lower bound is monotone (from the exactness law and totality alone)
    sub-mono : ∀ {u v} → lo ≤ u → lo ≤ v → u ≤ v → u - lo ≤ v - lo
    sub-mono {u} {v} lo≤u lo≤v u≤v with ≤-total (u - lo) (v - lo)
    ... | inj₁ le = le
    ... | inj₂ ge = subst (λ z → u - lo ≤ z - lo) (≤-antisym u≤v v≤u) ≤-refl
      where v≤u : v ≤ u
            v≤u = subst (_≤ u) (sub-add lo≤v) (subst (lo + (v - lo) ≤_) (sub-add lo≤u) (+-mono ≤-refl ge))

    -- `lo ≤ w` makes `w - lo` non-negative (0 is not the least element of every ordered monoid)
    nonneg-sub : ∀ {w} → lo ≤ w → 0# ≤ w - lo
    nonneg-sub {w} lo≤w with ≤-total 0# (w - lo)
    ... | inj₁ ok = ok
    ... | inj₂ neg = subst (0# ≤_) (sym zero) ≤-refl
      where
        w≤lo : w ≤ lo
        w≤lo = subst₂ _≤_ (sub-add lo≤w) (+-idʳ lo) (+-mono (≤-refl {lo}) neg)
        zero : w - lo ≡ 0#
        zero = sym (+-cancelˡ lo 0# (w - lo) (trans (+-idʳ lo) (trans (sym (≤-antisym w≤lo lo≤w)) (sym (sub-add lo≤w)))))

    r0 : ∀ r → r · 0# ≡ 0#
    r0 r = sym (+-cancelˡ (r · 0#) 0# (r · 0#) (trans (+-idʳ _) (trans (cong (r ·_) (sym (+-idˡ 0#))) (·-dist r 0# 0#))))

    nonneg-scaled : ∀ x → 0# ≤ ratio · offset x
    nonneg-scaled x = subst (_≤ ratio · offset x) (r0 ratio) (·-mono ratio≥0 (nonneg-sub (⊔-ub₁ lo x)))

    floor-mono : ∀ {u v} → 0# ≤ u → u ≤ v → floor u ℕ.≤ floor v
    floor-mono 0≤u u≤v = proj₁ (floor-gal (≤-trans 0≤u u≤v)) (≤-trans (hold-≤ 0≤u) u≤v)

  px-max : ∀ x → px x ℕ.≤ extent
  px-max x = ℕP.m⊓n≤m extent _

  px-mono : ∀ {x y} → x ≤ y → px x ℕ.≤ px y
  px-mono {x} {y} x≤y =
    ℕP.⊓-mono-≤ ℕP.≤-refl
      (floor-mono (nonneg-scaled x) (·-mono ratio≥0 (sub-mono (⊔-ub₁ lo x) (⊔-ub₁ lo y) (⊔-mono x≤y))))

  px-lo : px lo ≡ 0
  px-lo = trans (cong (extent ℕ.⊓_) (trans (cong floor (trans (cong (ratio ·_) (trans (cong (_- lo) (⊔-≤ ≤-refl)) (sub-self lo))) (r0 ratio)))
                                       (trans (cong floor (sym tick-0)) (floor-tick 0))))
                (ℕP.⊓-zeroʳ extent)

  px-hi : px hi ≡ extent
  px-hi = trans (cong (extent ℕ.⊓_) (trans (cong floor (trans (cong (ratio ·_) (cong (_- lo) (⊔-≤ lo≤hi))) span-ratio)) (floor-tick extent)))
                (ℕP.⊓-idem extent)
