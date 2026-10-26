{-# OPTIONS --safe --without-K #-}

-- Valid layouts.  A layout is `Valid` when its width and height are non-negative
-- (`Slides.Diagram.Laws`); the unit laws of the empty diagram hold for exactly
-- those.  This module proves that every operation keeps a layout valid, so that
-- the unit laws apply to anything built from valid parts, and lifts the layout
-- laws to diagram terms.
--
-- What it needs of the scalar, beyond `IsLawful`, is `IsOrdered`: the sum and
-- the maximum respect non-negativity, `fromℕ` is non-negative, and the maximum is
-- idempotent.  (A commutative ring with an associative, commutative maximum alone
-- cannot prove these.)  ℤ and ℚ are ordered; ℕ is not covered (see `Laws`).

module Slides.Diagram.Valid where

open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤP
import Data.Rational as ℚ
import Data.Rational.Properties as ℚP
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong₂; cong; subst)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Laws using (IsLawful; lawfulℤ; lawfulℚ; module Proofs)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry using (VAlign; top; middle; bottom; Align; left; centred; right)
import Slides.Diagram.Geometry as Geo
import Slides.Diagram.Layout as Lay
open import Relation.Nullary using (¬_)
open import Slides.Diagram using (defaultStyle)
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Slides.Diagram.Syntax
  using ( Dia; Op; Rectangle; Disc; Segment; Text; Spacer; Beside; Above; Atop
        ; LabelAbove; LabelBelow; Place; Overlay; Named; Connect )
import Slides.Diagram.Notation as Nt

record IsOrdered {S : Set} (O : Ops S) (L : IsLawful O) : Set where
  open Ops O
  open IsLawful L
  field
    ⊔-idem       : ∀ x → (x ⊔ x) ≈ x
    -- non-negative: `0 ⊔ x ≈ x`
    nonneg-+     : ∀ {x y} → (0# ⊔ x) ≈ x → (0# ⊔ y) ≈ y → (0# ⊔ (x + y)) ≈ (x + y)
    fromℕ-nonneg : ∀ n → (0# ⊔ fromℕ n) ≈ fromℕ n

orderedℤ : IsOrdered intOps lawfulℤ
orderedℤ = record
  { ⊔-idem = ℤP.⊔-idem
  ; nonneg-+ = λ {x} {y} hx hy → ℤP.i≤j⇒i⊔j≡j (ℤP.+-mono-≤ (ℤP.i⊔j≡j⇒i≤j hx) (ℤP.i⊔j≡j⇒i≤j hy))
  ; fromℕ-nonneg = λ n → ℤP.i≤j⇒i⊔j≡j (ℤ.+≤+ ℕ.z≤n) }
  where import Data.Nat as ℕ

orderedℚ : IsOrdered ratOps lawfulℚ
orderedℚ = record
  { ⊔-idem = ℚP.⊔-idem
  ; nonneg-+ = λ {x} {y} hx hy → ℚP.p≤q⇒p⊔q≡q {ℚ.0ℚ} {x ℚ.+ y} (ℚP.+-mono-≤ {ℚ.0ℚ} {x} {ℚ.0ℚ} {y} (ℚP.p⊔q≡q⇒p≤q hx) (ℚP.p⊔q≡q⇒p≤q hy))
  ; fromℕ-nonneg = λ n → ℚP.p≤q⇒p⊔q≡q (ℚP.nonNegative⁻¹ (ℤ.+ n ℚ./ 1) {{nn n}}) }
  where nn : ∀ n → ℚ.NonNegative (ℤ.+ n ℚ./ 1)
        nn n = ℚP.normalize-nonNeg n 1

module For {S : Set} (O : Ops S) (L : IsLawful O) (Ord : IsOrdered O L) where
  open Ops O
  open IsLawful L
  open IsOrdered Ord
  open Proofs O L
  open import Slides.Diagram.Place O
  open import Slides.Diagram.Equality R.isEquivalence
  module N = Nt.NotationWith O

  ----------------------------------------------------------------------
  -- Non-negative sizes

  nonneg-0 : Nonneg 0#
  nonneg-0 = ⊔-idem 0#

  nonneg-⊔ : ∀ {x y} → Nonneg x → Nonneg y → Nonneg (x ⊔ y)
  nonneg-⊔ {x} {y} hx hy = R.trans (R.sym (⊔-assoc 0# x y)) (⊔-cong hx R.refl)

  ----------------------------------------------------------------------
  -- Every operation keeps a layout valid

  valid-empty : Valid empty
  valid-empty = nonneg-0 , nonneg-0

  valid-spacer : ∀ {w h} → Nonneg w → Nonneg h → Valid (spacer w h)
  valid-spacer nw nh = nw , nh

  valid-rectangle : ∀ {w h s} → Nonneg w → Nonneg h → Valid (rectangle w h s)
  valid-rectangle nw nh = nw , nh

  valid-segment : ∀ {w h s} → Nonneg w → Nonneg h → Valid (segment w h s)
  valid-segment nw nh = nw , nh

  valid-disc : ∀ {r s} → Nonneg r → Valid (disc r s)
  valid-disc nr = nonneg-+ nr nr , nonneg-+ nr nr

  valid-text : ∀ pct size t s → Valid (text pct size t s)
  valid-text pct size t s = fromℕ-nonneg _ , fromℕ-nonneg _

  valid-combine : ∀ {w h p a q b} → Nonneg w → Nonneg h → Valid (combine w h p a q b)
  valid-combine nw nh = nw , nh

  valid-atop : ∀ {a b} → Valid a → Valid b → Valid (atop a b)
  valid-atop (wa , ha) (wb , hb) = nonneg-⊔ wa wb , nonneg-⊔ ha hb

  valid-besideA : ∀ al {a b} → Valid a → Valid b → Valid (besideA al a b)
  valid-besideA al (wa , ha) (wb , hb) = nonneg-+ wa wb , nonneg-⊔ ha hb

  valid-aboveA : ∀ al {a b} → Valid a → Valid b → Valid (aboveA al a b)
  valid-aboveA al (wa , ha) (wb , hb) = nonneg-⊔ wa wb , nonneg-+ ha hb

  valid-labelAbove : ∀ {l d} → Valid l → Valid d → Valid (labelAbove l d)
  valid-labelAbove {l} {d} vl vd =
    valid-aboveA centred {l} {aboveA centred d (spacer 0# (height l))} vl
      (valid-aboveA centred {d} {spacer 0# (height l)} vd (valid-spacer {0#} {height l} nonneg-0 (proj₂ vl)))

  valid-labelBelow : ∀ {l d} → Valid l → Valid d → Valid (labelBelow l d)
  valid-labelBelow {l} {d} vl vd =
    valid-aboveA centred {spacer 0# (height l)} {aboveA centred d l} (valid-spacer {0#} {height l} nonneg-0 (proj₂ vl))
      (valid-aboveA centred {d} {l} vd vl)

  valid-overlay : ∀ {w h a b} → Nonneg w → Nonneg h → Valid (overlay w h a b)
  valid-overlay nw nh = nw , nh

  valid-place : ∀ {w h x y d} → Nonneg w → Nonneg h → Valid (place w h x y d)
  valid-place nw nh = nw , nh

  valid-named : ∀ n {d} → Valid d → Valid (named n d)
  valid-named n v = v

  valid-connectP : ∀ a pa b pb s {d} → Valid d → Valid (connectP a pa b pb s d)
  valid-connectP a pa b pb s {d} (nw , nh) with connectP-size a pa b pb s d
  ... | ew , eh , _ = subst Nonneg (sym ew) nw , subst Nonneg (sym eh) nh

  ----------------------------------------------------------------------
  -- Terms: a diagram is valid when its sized leaves are

  -- the only leaves that can break validity are the ones that carry a size
  OpOk : Op S → Set
  OpOk (Rectangle w h _) = Nonneg w × Nonneg h
  OpOk (Disc r _)        = Nonneg r
  OpOk (Segment w h _)   = Nonneg w × Nonneg h
  OpOk (Spacer w h)      = Nonneg w × Nonneg h
  OpOk (Place w h _ _)   = Nonneg w × Nonneg h
  OpOk (Overlay w h)     = Nonneg w × Nonneg h
  OpOk _                 = ⊤

  WellSized : Dia S → Set
  WellSized (pure ())
  WellSized (impure (o , k)) = OpOk o × (∀ p → WellSized (k p))

  valid-layout : ∀ d → WellSized d → Valid (LW.layout d)
  valid-layout (pure ())
  valid-layout (impure (Rectangle w h s , k)) ((nw , nh) , _) = valid-rectangle {w} {h} {s} nw nh
  valid-layout (impure (Disc r s , k)) (nr , _)             = valid-disc {r} {s} nr
  valid-layout (impure (Segment w h s , k)) ((nw , nh) , _) = valid-segment {w} {h} {s} nw nh
  valid-layout (impure (Text pct size t s , k)) _           = valid-text pct size t s
  valid-layout (impure (Spacer w h , k)) ((nw , nh) , _)    = valid-spacer {w} {h} nw nh
  valid-layout (impure (Beside al , k)) (_ , ok) =
    valid-besideA al {LW.layout (k zero)} {LW.layout (k (suc zero))} (valid-layout (k zero) (ok zero)) (valid-layout (k (suc zero)) (ok (suc zero)))
  valid-layout (impure (Above al , k)) (_ , ok) =
    valid-aboveA al {LW.layout (k zero)} {LW.layout (k (suc zero))} (valid-layout (k zero) (ok zero)) (valid-layout (k (suc zero)) (ok (suc zero)))
  valid-layout (impure (Atop , k)) (_ , ok) =
    valid-atop {LW.layout (k zero)} {LW.layout (k (suc zero))} (valid-layout (k zero) (ok zero)) (valid-layout (k (suc zero)) (ok (suc zero)))
  valid-layout (impure (LabelAbove , k)) (_ , ok) =
    valid-labelAbove {LW.layout (k zero)} {LW.layout (k (suc zero))} (valid-layout (k zero) (ok zero)) (valid-layout (k (suc zero)) (ok (suc zero)))
  valid-layout (impure (LabelBelow , k)) (_ , ok) =
    valid-labelBelow {LW.layout (k zero)} {LW.layout (k (suc zero))} (valid-layout (k zero) (ok zero)) (valid-layout (k (suc zero)) (ok (suc zero)))
  valid-layout (impure (Overlay w h , k)) ((nw , nh) , _) = valid-overlay {w} {h} {LW.layout (k zero)} {LW.layout (k (suc zero))} nw nh
  valid-layout (impure (Place w h x y , k)) ((nw , nh) , _) = valid-place {w} {h} {x} {y} {LW.layout (k tt)} nw nh
  valid-layout (impure (Named n , k)) (_ , ok) = valid-named n {LW.layout (k tt)} (valid-layout (k tt) (ok tt))
  valid-layout (impure (Connect a pa b pb s , k)) (_ , ok) = valid-connectP a pa b pb s {LW.layout (k tt)} (valid-layout (k tt) (ok tt))

  ----------------------------------------------------------------------
  -- Congruence: the combinators respect `≈ᴸ`

  sub-cong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a - b) ≈ (a′ - b′)
  sub-cong ea eb = R.trans (sub≈ _ _) (R.trans (+-cong ea (R.-‿cong eb)) (R.sym (sub≈ _ _)))

  vo-cong : ∀ al {o o′ i i′} → o ≈ o′ → i ≈ i′ → valignOffset al o i ≈ valignOffset al o′ i′
  vo-cong top    eo ei = R.refl
  vo-cong middle eo ei = sub-cong eo ei
  vo-cong bottom eo ei = +-cong (sub-cong eo ei) (sub-cong eo ei)

  ao-cong : ∀ al {o o′ i i′} → o ≈ o′ → i ≈ i′ → alignOffset al o i ≈ alignOffset al o′ i′
  ao-cong left    eo ei = R.refl
  ao-cong centred eo ei = sub-cong eo ei
  ao-cong right   eo ei = +-cong (sub-cong eo ei) (sub-cong eo ei)

  shiftDraw-cong₂ : ∀ p {x y} → x ≈ᵈ y → shiftDraw′ p x ≈ᵈ shiftDraw′ p y
  shiftDraw-cong₂ p (rect≈ a b c d)  = rect≈ (+-cong a R.refl) (+-cong b R.refl) c d
  shiftDraw-cong₂ p (circle≈ a b c)  = circle≈ (+-cong a R.refl) (+-cong b R.refl) c
  shiftDraw-cong₂ p (line≈ a b c d)  =
    line≈ (+-cong a R.refl) (+-cong b R.refl) (+-cong c R.refl) (+-cong d R.refl)
  shiftDraw-cong₂ p (arrow≈ a b c d) =
    arrow≈ (+-cong a R.refl) (+-cong b R.refl) (+-cong c R.refl) (+-cong d R.refl)
  shiftDraw-cong₂ p (label≈ a b)     = label≈ (+-cong a R.refl) (+-cong b R.refl)

  shiftAnchor-cong₂ : ∀ p {x y} → x ≈ᵃ y → shiftAnchor′ p x ≈ᵃ shiftAnchor′ p y
  shiftAnchor-cong₂ p {n , box l t w h} {m , box l′ t′ w′ h′} (e , box≈ a b c d) =
    e , box≈ (+-cong a R.refl) (+-cong b R.refl) c d

  map-shift-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ {xs ys} → Pointwise _≈ᵈ_ xs ys →
                   Pointwise _≈ᵈ_ (map (shiftDraw′ p) xs) (map (shiftDraw′ p′) ys)
  map-shift-cong e []        = []
  map-shift-cong {p} {p′} e {x ∷ xs} {y ∷ ys} (xy ∷ r) =
    ≈ᵈ-trans (shiftDraw-cong e x) (shiftDraw-cong₂ p′ xy) ∷ map-shift-cong e r

  map-shiftA-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ {xs ys} → Pointwise _≈ᵃ_ xs ys →
                    Pointwise _≈ᵃ_ (map (shiftAnchor′ p) xs) (map (shiftAnchor′ p′) ys)
  map-shiftA-cong e []        = []
  map-shiftA-cong {p} {p′} e {x ∷ xs} {y ∷ ys} (xy ∷ r) =
    IsEquivalence.trans ≈ᵃ-isEquivalence (shiftAnchor-cong e x) (shiftAnchor-cong₂ p′ xy) ∷ map-shiftA-cong e r

  combine-cong : ∀ {w w′ h h′ p p′ q q′ a a′ b b′} →
                 w ≈ w′ → h ≈ h′ → p ≈ₚ p′ → q ≈ₚ q′ → a ≈ᴸ a′ → b ≈ᴸ b′ →
                 combine w h p a q b ≈ᴸ combine w′ h′ p′ a′ q′ b′
  combine-cong ew eh ep eq ea eb =
    layout≈ ew eh
      (PW.++⁺ (map-shift-cong ep (_≈ᴸ_.draws≈ ea)) (map-shift-cong eq (_≈ᴸ_.draws≈ eb)))
      (PW.++⁺ (map-shiftA-cong ep (_≈ᴸ_.anchors≈ ea)) (map-shiftA-cong eq (_≈ᴸ_.anchors≈ eb)))

  besideA-cong : ∀ al {a a′ b b′} → a ≈ᴸ a′ → b ≈ᴸ b′ → besideA al a b ≈ᴸ besideA al a′ b′
  besideA-cong al ea eb =
    combine-cong (+-cong wa wb) eh (R.refl , vo-cong al eh ha) (+-cong wa wa , vo-cong al eh hb) ea eb
    where wa = _≈ᴸ_.width≈ ea ; ha = _≈ᴸ_.height≈ ea
          wb = _≈ᴸ_.width≈ eb ; hb = _≈ᴸ_.height≈ eb
          eh = ⊔-cong ha hb

  aboveA-cong : ∀ al {a a′ b b′} → a ≈ᴸ a′ → b ≈ᴸ b′ → aboveA al a b ≈ᴸ aboveA al a′ b′
  aboveA-cong al ea eb =
    combine-cong ew (+-cong ha hb) (ao-cong al ew wa , R.refl) (ao-cong al ew wb , +-cong ha ha) ea eb
    where wa = _≈ᴸ_.width≈ ea ; ha = _≈ᴸ_.height≈ ea
          wb = _≈ᴸ_.width≈ eb ; hb = _≈ᴸ_.height≈ eb
          ew = ⊔-cong wa wb

  atop-cong : ∀ {a a′ b b′} → a ≈ᴸ a′ → b ≈ᴸ b′ → atop a b ≈ᴸ atop a′ b′
  atop-cong ea eb =
    combine-cong ew eh (sub-cong ew wa , sub-cong eh ha) (sub-cong ew wb , sub-cong eh hb) ea eb
    where wa = _≈ᴸ_.width≈ ea ; ha = _≈ᴸ_.height≈ ea
          wb = _≈ᴸ_.width≈ eb ; hb = _≈ᴸ_.height≈ eb
          ew = ⊔-cong wa wb ; eh = ⊔-cong ha hb

  ----------------------------------------------------------------------
  -- Laws of diagram terms, up to `≈ᴸ` of their layouts

  -- (`layout` of a connective is the connective of the layouts, by computation)
  lay : Dia S → Layout S
  lay = LW.layout

  -- `∥`, `═` and `⊙` associate
  ∥-assoc-term : ∀ a b c → lay (a Nt.∥ (b Nt.∥ c)) ≈ᴸ lay ((a Nt.∥ b) Nt.∥ c)
  ∥-assoc-term a b c = ∥-assoc Geo.middle (lay a) (lay b) (lay c)

  ═-assoc-term : ∀ a b c → lay (a Nt.═ (b Nt.═ c)) ≈ᴸ lay ((a Nt.═ b) Nt.═ c)
  ═-assoc-term a b c = ═-assoc centred (lay a) (lay b) (lay c)

  ⊙-assoc-term : ∀ a b c → lay (a Nt.⊙ (b Nt.⊙ c)) ≈ᴸ lay ((a Nt.⊙ b) Nt.⊙ c)
  ⊙-assoc-term a b c = ⊙-assoc (lay a) (lay b) (lay c)

  -- the empty diagram is a unit of every connective, for a valid diagram
  ∥-unitˡ-term : ∀ a → Valid (lay a) → lay (N.empty Nt.∥ a) ≈ᴸ lay a
  ∥-unitˡ-term a v = ∥-unitˡ Geo.middle (lay a) v
  ∥-unitʳ-term : ∀ a → Valid (lay a) → lay (a Nt.∥ N.empty) ≈ᴸ lay a
  ∥-unitʳ-term a v = ∥-unitʳ Geo.middle (lay a) v
  ═-unitˡ-term : ∀ a → Valid (lay a) → lay (N.empty Nt.═ a) ≈ᴸ lay a
  ═-unitˡ-term a v = ═-unitˡ centred (lay a) v
  ═-unitʳ-term : ∀ a → Valid (lay a) → lay (a Nt.═ N.empty) ≈ᴸ lay a
  ═-unitʳ-term a v = ═-unitʳ centred (lay a) v
  ⊙-unitˡ-term : ∀ a → Valid (lay a) → lay (N.empty Nt.⊙ a) ≈ᴸ lay a
  ⊙-unitˡ-term a v = ⊙-unitˡ (lay a) v
  ⊙-unitʳ-term : ∀ a → Valid (lay a) → lay (a Nt.⊙ N.empty) ≈ᴸ lay a
  ⊙-unitʳ-term a v = ⊙-unitʳ (lay a) v

  -- and for a diagram whose sized leaves are non-negative, validity is automatic
  ∥-unitˡ-wf : ∀ a → WellSized a → lay (N.empty Nt.∥ a) ≈ᴸ lay a
  ∥-unitˡ-wf a w = ∥-unitˡ-term a (valid-layout a w)

  -- gaps add: `↔ m ∥ ↔ n ≈ ↔ (m + n)`, whatever the alignment (no scalar is positive
  -- or negative here: a gap draws nothing), and the like for `↕`; gaps overlaid
  -- or stacked across take the maximum
  gap-∥ : ∀ al m n → lay (Nt.besideA al (N.↔ m) (N.↔ n)) ≈ᴸ lay (N.↔ (m + n))
  gap-∥ al m n = layout≈ R.refl (⊔-idem 0#) [] []

  gap-═ : ∀ al m n → lay (Nt.aboveA al (N.↕ m) (N.↕ n)) ≈ᴸ lay (N.↕ (m + n))
  gap-═ al m n = layout≈ (⊔-idem 0#) R.refl [] []

  gap-⊙ : ∀ m n → lay (N.↔ m Nt.⊙ N.↔ n) ≈ᴸ lay (N.↔ (m ⊔ n))
  gap-⊙ m n = layout≈ R.refl (⊔-idem 0#) [] []

  gap-═↔ : ∀ al m n → lay (Nt.aboveA al (N.↔ m) (N.↔ n)) ≈ᴸ lay (N.↔ (m ⊔ n))
  gap-═↔ al m n = layout≈ R.refl (+-identityʳ 0#) [] []

  -- a margin of nothing changes nothing, for a valid diagram
  margin-zero : ∀ d → Valid (lay d) → lay (N.margin 0# 0# 0# 0# d) ≈ᴸ lay d
  margin-zero d v = ≈-trans (besideA-cong Geo.middle ≈ᴸ-refl inner) (∥-unitˡ Geo.middle (lay d) v)
    where
      open IsEquivalence ≈ᴸ-isEquivalence using () renaming (refl to ≈ᴸ-refl; trans to ≈-trans)
      vertical : aboveA centred empty (aboveA centred (lay d) empty) ≈ᴸ lay d
      vertical = ≈-trans (aboveA-cong centred ≈ᴸ-refl (═-unitʳ centred (lay d) v)) (═-unitˡ centred (lay d) v)
      inner : besideA Geo.middle (aboveA centred empty (aboveA centred (lay d) empty)) empty ≈ᴸ lay d
      inner = ≈-trans (besideA-cong Geo.middle vertical ≈ᴸ-refl) (∥-unitʳ Geo.middle (lay d) v)

  margin-zero-wf : ∀ d → WellSized d → lay (N.margin 0# 0# 0# 0# d) ≈ᴸ lay d
  margin-zero-wf d w = margin-zero d (valid-layout d w)

module ForInts = For intOps lawfulℤ orderedℤ
module ForRats = For ratOps lawfulℚ orderedℚ

import Slides.Diagram.Laws as Laws
import Slides.Diagram.Place intOps as PI

-- the hypotheses on sized leaves are needed: in ℤ a rectangle of width -1 is not valid
invalid-rectangle : ¬ Laws.ForInts.Valid (PI.rectangle (ℤ.-[1+ 0 ]) (ℤ.+ 1) defaultStyle)
invalid-rectangle (nw , _) = case nw of λ ()
  where open import Function using (case_of_)
