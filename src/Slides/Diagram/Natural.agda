{-# OPTIONS --safe --without-K #-}

-- Layout is natural in the scalar.
--
-- For an order embedding `h : S → T` of ordered monoids (`IsOrdMonHom`: `0`, `+`, order and its
-- reflection; the join and the exact differences follow, `Slides.Scalar.Core`),
--
--     layout_T (mapDia h d) ≡ mapLayout h (layout_S d)
--
-- for every diagram whose connection ports `h` carries (`layout-natural-ok`): every `side`
-- port, and, if `h` also preserves percentages (`PctNat`), every port (`layout-natural`).
-- The map of ℕ into ℚ preserves percentages only where they are exact, so it uses the first
-- form for diagrams that attach by sides.  Layout subtracts only a smaller size from a larger
-- (centring), which is exactly where `h` preserves `-`, so no hypothesis on the diagram is
-- needed for it.
--
--      d : Dia S ──layout_S──▶ Layout S
--        │ mapDia h               │ mapLayout h
--        ▼                        ▼
--      Dia T ────layout_T────▶ Layout T
--
-- Proof: one equation per placement operation (`*-nat`), then the generic fusion of
-- `Container.Interpret.Plain` (`pfold-translate` for `mapDia`, `pfold-rel` for `mapLayout`).

open import Slides.Scalar.Core using (OrdMon; IsOrdMonHom)
open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Natural {S T : Set} (Sp : Space S) (Tp : Space T) (h : S → T)
         (H : IsOrdMonHom (Space.ord Sp) (Space.ord Tp) h) where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (position)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pfold-translate; pfold-rel)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Syntax
import Slides.Diagram.Place Sp as PS
import Slides.Diagram.Place Tp as PT
import Slides.Diagram.Layout Sp as LS
import Slides.Diagram.Layout Tp as LT

private
  module A = Space Sp
  module B = Space Tp
open IsOrdMonHom H

hsub : ∀ {a b} → b A.≤ a → h (a A.- b) ≡ h a B.- h b
hsub = h-sub (Space.sub Sp) (Space.sub Tp)

dbl-nat : ∀ x → h (PS.dbl x) ≡ PT.dbl (h x)
dbl-nat x = h-+ x x

valign-nat : ∀ al {o i} → i A.≤ o → h (PS.valignOffset al o i) ≡ PT.valignOffset al (h o) (h i)
valign-nat top    _ = h-0
valign-nat middle p = hsub p
valign-nat bottom p = trans (dbl-nat _) (cong PT.dbl (hsub p))

align-nat : ∀ al {o i} → i A.≤ o → h (PS.alignOffset al o i) ≡ PT.alignOffset al (h o) (h i)
align-nat left    _ = h-0
align-nat centred p = hsub p
align-nat right   p = trans (dbl-nat _) (cong PT.dbl (hsub p))

------------------------------------------------------------------------
-- Shifting, framing, overlaying: only `+` is used

shiftDraw-nat : ∀ dx dy d → mapDraw h (PS.shiftDraw dx dy d) ≡ PT.shiftDraw (h dx) (h dy) (mapDraw h d)
shiftDraw-nat dx dy (rect x y w ht s)   rewrite h-+ x dx | h-+ y dy = refl
shiftDraw-nat dx dy (circle x y r s)    rewrite h-+ x dx | h-+ y dy = refl
shiftDraw-nat dx dy (line a b c d s)    rewrite h-+ a dx | h-+ b dy | h-+ c dx | h-+ d dy = refl
shiftDraw-nat dx dy (arrow a b c d s)   rewrite h-+ a dx | h-+ b dy | h-+ c dx | h-+ d dy = refl
shiftDraw-nat dx dy (label x y n t s)   rewrite h-+ x dx | h-+ y dy = refl
shiftDraw-nat dx dy (path x y d s)      rewrite h-+ x dx | h-+ y dy = refl
shiftDraw-nat dx dy (group x y ds)      rewrite h-+ x dx | h-+ y dy = refl

mapDraws-shift : ∀ dx dy ds → mapDraws h (map (PS.shiftDraw dx dy) ds) ≡ map (PT.shiftDraw (h dx) (h dy)) (mapDraws h ds)
mapDraws-shift dx dy []       = refl
mapDraws-shift dx dy (d ∷ ds) = cong₂ _∷_ (shiftDraw-nat dx dy d) (mapDraws-shift dx dy ds)

mapDraws-++ : ∀ xs ys → mapDraws h (xs ++ ys) ≡ mapDraws h xs ++ mapDraws h ys
mapDraws-++ []       ys = refl
mapDraws-++ (x ∷ xs) ys = cong (mapDraw h x ∷_) (mapDraws-++ xs ys)

shiftAnchor-nat : ∀ dx dy a → mapAnchor h (PS.shiftAnchor dx dy a) ≡ PT.shiftAnchor (h dx) (h dy) (mapAnchor h a)
shiftAnchor-nat dx dy (n , box l t w ht) rewrite h-+ l dx | h-+ t dy = refl

anchors-shift : ∀ dx dy as → map (mapAnchor h) (map (PS.shiftAnchor dx dy) as) ≡ map (PT.shiftAnchor (h dx) (h dy)) (map (mapAnchor h) as)
anchors-shift dx dy []       = refl
anchors-shift dx dy (a ∷ as) = cong₂ _∷_ (shiftAnchor-nat dx dy a) (anchors-shift dx dy as)

anchors-++ : ∀ (xs ys : List (String × Box S)) → map (mapAnchor h) (xs ++ ys) ≡ map (mapAnchor h) xs ++ map (mapAnchor h) ys
anchors-++ []       ys = refl
anchors-++ (x ∷ xs) ys = cong (mapAnchor h x ∷_) (anchors-++ xs ys)

inFrame-nat : ∀ w ht dx dy l →
  mapLayout h (PS.inFrame w ht dx dy l) ≡ PT.inFrame (h w) (h ht) (h dx) (h dy) (mapLayout h l)
inFrame-nat w ht dx dy (mkLayout _ _ ds as) =
  cong₂ (mkLayout (h w) (h ht)) (mapDraws-shift dx dy ds) (anchors-shift dx dy as)

overlay-nat : ∀ w ht a b →
  mapLayout h (PS.overlay w ht a b) ≡ PT.overlay (h w) (h ht) (mapLayout h a) (mapLayout h b)
overlay-nat w ht (mkLayout _ _ d₁ a₁) (mkLayout _ _ d₂ a₂) =
  cong₂ (mkLayout (h w) (h ht)) (mapDraws-++ d₁ d₂) (anchors-++ a₁ a₂)

combine-nat : ∀ w ht px py qx qy a b →
  mapLayout h (PS.combine w ht (px , py) a (qx , qy) b)
    ≡ PT.combine (h w) (h ht) (h px , h py) (mapLayout h a) (h qx , h qy) (mapLayout h b)
combine-nat w ht px py qx qy a b =
  trans (overlay-nat w ht (PS.inFrame w ht px py a) (PS.inFrame w ht qx qy b))
        (cong₂ (PT.overlay (h w) (h ht)) (inFrame-nat w ht px py a) (inFrame-nat w ht qx qy b))

place-nat : ∀ w ht x y l →
  mapLayout h (PS.place w ht x y l) ≡ PT.place (h w) (h ht) (h x) (h y) (mapLayout h l)
place-nat w ht x y l = trans (inFrame-nat w ht _ _ l) (cong₂ (λ u v → PT.inFrame (h w) (h ht) u v (mapLayout h l)) (dbl-nat x) (dbl-nat y))

------------------------------------------------------------------------
-- Primitives

disc-nat : ∀ r s → mapLayout h (PS.disc r s) ≡ PT.disc (h r) s
disc-nat r s rewrite dbl-nat r = refl

segment-nat : ∀ w ht s → mapLayout h (PS.segment w ht s) ≡ PT.segment (h w) (h ht) s
segment-nat w ht s rewrite h-0 | dbl-nat w | dbl-nat ht = refl

rectangle-nat : ∀ w ht s → mapLayout h (PS.rectangle w ht s) ≡ PT.rectangle (h w) (h ht) s
rectangle-nat w ht s rewrite h-0 = refl

pathL-nat : ∀ w ht d s → mapLayout h (PS.pathL w ht d s) ≡ PT.pathL (h w) (h ht) d s
pathL-nat w ht d s rewrite h-0 = refl

------------------------------------------------------------------------
-- Connectives: `-` only where the minuend is the larger

-- `combine`, with the images of the frame and the positions given by equations
combine-nat′ : ∀ {w ht px py qx qy w′ ht′ px′ py′ qx′ qy′} a b →
  h w ≡ w′ → h ht ≡ ht′ → h px ≡ px′ → h py ≡ py′ → h qx ≡ qx′ → h qy ≡ qy′ →
  mapLayout h (PS.combine w ht (px , py) a (qx , qy) b)
    ≡ PT.combine w′ ht′ (px′ , py′) (mapLayout h a) (qx′ , qy′) (mapLayout h b)
combine-nat′ {w} {ht} {px} {py} {qx} {qy} a b refl refl refl refl refl refl = combine-nat w ht px py qx qy a b

-- the join, then a difference from it
⊔-sub₁ : ∀ a b → h ((a A.⊔ b) A.- a) ≡ (h a B.⊔ h b) B.- h a
⊔-sub₁ a b = trans (hsub (A.⊔-ub₁ a b)) (cong (B._- h a) (h-⊔ a b))

⊔-align₁ : ∀ al a b → h (PS.alignOffset al (a A.⊔ b) a) ≡ PT.alignOffset al (h a B.⊔ h b) (h a)
⊔-align₁ al a b = trans (align-nat al (A.⊔-ub₁ a b)) (cong (λ o → PT.alignOffset al o (h a)) (h-⊔ a b))

⊔-align₂ : ∀ al a b → h (PS.alignOffset al (a A.⊔ b) b) ≡ PT.alignOffset al (h a B.⊔ h b) (h b)
⊔-align₂ al a b = trans (align-nat al (A.⊔-ub₂ a b)) (cong (λ o → PT.alignOffset al o (h b)) (h-⊔ a b))

⊔-valign₁ : ∀ al a b → h (PS.valignOffset al (a A.⊔ b) a) ≡ PT.valignOffset al (h a B.⊔ h b) (h a)
⊔-valign₁ al a b = trans (valign-nat al (A.⊔-ub₁ a b)) (cong (λ o → PT.valignOffset al o (h a)) (h-⊔ a b))

⊔-valign₂ : ∀ al a b → h (PS.valignOffset al (a A.⊔ b) b) ≡ PT.valignOffset al (h a B.⊔ h b) (h b)
⊔-valign₂ al a b = trans (valign-nat al (A.⊔-ub₂ a b)) (cong (λ o → PT.valignOffset al o (h b)) (h-⊔ a b))

atop-nat : ∀ a b → mapLayout h (PS.atop a b) ≡ PT.atop (mapLayout h a) (mapLayout h b)
atop-nat a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) =
  combine-nat′ a b (h-⊔ wa wb) (h-⊔ ha hb) (⊔-sub₁ wa wb) (⊔-sub₁ ha hb)
    (trans (hsub (A.⊔-ub₂ wa wb)) (cong (B._- h wb) (h-⊔ wa wb)))
    (trans (hsub (A.⊔-ub₂ ha hb)) (cong (B._- h hb) (h-⊔ ha hb)))

besideA-nat : ∀ al a b → mapLayout h (PS.besideA al a b) ≡ PT.besideA al (mapLayout h a) (mapLayout h b)
besideA-nat al a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) =
  combine-nat′ a b (h-+ wa wb) (h-⊔ ha hb) h-0 (⊔-valign₁ al ha hb) (dbl-nat wa) (⊔-valign₂ al ha hb)

aboveA-nat : ∀ al a b → mapLayout h (PS.aboveA al a b) ≡ PT.aboveA al (mapLayout h a) (mapLayout h b)
aboveA-nat al a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) =
  combine-nat′ a b (h-⊔ wa wb) (h-+ ha hb) (⊔-align₁ al wa wb) h-0 (⊔-align₂ al wa wb) (dbl-nat ha)

labelAbove-nat : ∀ l d → mapLayout h (PS.labelAbove l d) ≡ PT.labelAbove (mapLayout h l) (mapLayout h d)
labelAbove-nat l@(mkLayout wl hl _ _) d@(mkLayout wd hd _ _) =
  combine-nat′ l d (h-⊔ wl wd) (trans (h-+ hl _) (cong (h hl B.+_) (h-+ hd hl)))
    (⊔-align₁ centred wl wd) h-0 (⊔-align₂ centred wl wd) (dbl-nat hl)

labelBelow-nat : ∀ l d → mapLayout h (PS.labelBelow l d) ≡ PT.labelBelow (mapLayout h l) (mapLayout h d)
labelBelow-nat l@(mkLayout wl hl _ _) d@(mkLayout wd hd _ _) =
  combine-nat′ d l (h-⊔ wl wd) (trans (h-+ hl _) (cong (h hl B.+_) (h-+ hd hl)))
    (⊔-align₂ centred wl wd) (dbl-nat hl) (⊔-align₁ centred wl wd)
    (trans (dbl-nat (hl A.+ hd)) (cong PT.dbl (h-+ hl hd)))

------------------------------------------------------------------------
-- Names and connections

named-nat : ∀ n l → mapLayout h (PS.named n l) ≡ PT.named n (mapLayout h l)
named-nat n (mkLayout w ht ds as) rewrite h-0 = refl

find-map : ∀ n as → PT.findAnchor n (map (mapAnchor h) as) ≡ Maybe.map (mapBox h) (PS.findAnchor n as)
find-map n []             = refl
find-map n ((m , b) ∷ as) with n ≟ m
... | yes _ = refl
... | no _  = find-map n as

-- a port is carried when the point it names is
PortNat : Port → Set
PortNat p = ∀ b → PT.portPoint p (mapBox h b) ≡ (h (proj₁ (PS.portPoint p b)) , h (proj₂ (PS.portPoint p b)))

side-nat : ∀ s → PortNat (side s)
side-nat north  (box l t w ht) rewrite h-+ l w = refl
side-nat south  (box l t w ht) rewrite h-+ l w | h-+ t (PS.dbl ht) | dbl-nat ht = refl
side-nat east   (box l t w ht) rewrite h-+ l (PS.dbl w) | h-+ t ht | dbl-nat w = refl
side-nat west   (box l t w ht) rewrite h-+ t ht = refl
side-nat middle (box l t w ht) rewrite h-+ l w | h-+ t ht = refl

-- `h` preserves percentages
PctNat : Set
PctNat = ∀ p x → h (A.pct p x) ≡ B.pct p (h x)

at-nat : PctNat → ∀ s p → PortNat (at s p)
at-nat pn north  p (box l t w ht) rewrite h-+ l (A.pct p (PS.dbl w)) | pn p (PS.dbl w) | dbl-nat w = refl
at-nat pn south  p (box l t w ht) rewrite h-+ l (A.pct p (PS.dbl w)) | pn p (PS.dbl w) | dbl-nat w
                                        | h-+ t (PS.dbl ht) | dbl-nat ht = refl
at-nat pn east   p (box l t w ht) rewrite h-+ l (PS.dbl w) | dbl-nat w | h-+ t (A.pct p (PS.dbl ht))
                                        | pn p (PS.dbl ht) | dbl-nat ht = refl
at-nat pn west   p (box l t w ht) rewrite h-+ t (A.pct p (PS.dbl ht)) | pn p (PS.dbl ht) | dbl-nat ht = refl
at-nat pn middle p b              = side-nat middle b

connectArrow-nat : ∀ pa pb s ma mb → PortNat pa → PortNat pb →
  mapDraws h (PS.connectArrow pa pb s ma mb)
    ≡ PT.connectArrow pa pb s (Maybe.map (mapBox h) ma) (Maybe.map (mapBox h) mb)
connectArrow-nat pa pb s (just ba) (just bb) npa npb rewrite npa ba | npb bb = refl
connectArrow-nat pa pb s (just _)  nothing   _ _ = refl
connectArrow-nat pa pb s nothing   _         _ _ = refl

connectP-nat : ∀ a pa b pb s l → PortNat pa → PortNat pb →
  mapLayout h (PS.connectP a pa b pb s l) ≡ PT.connectP a pa b pb s (mapLayout h l)
connectP-nat a pa b pb s (mkLayout w ht ds as) npa npb
  rewrite find-map a as | find-map b as | mapDraws-++ ds (PS.connectArrow pa pb s (PS.findAnchor a as) (PS.findAnchor b as))
        | connectArrow-nat pa pb s (PS.findAnchor a as) (PS.findAnchor b as) npa npb = refl

------------------------------------------------------------------------
-- One command at a time

OkOp : Op S → Set
OkOp (Connect _ pa _ pb _) = PortNat pa × PortNat pb
OkOp _                     = ⊤

layoutH-nat : ∀ o k → OkOp o →
  mapLayout h (LS.layoutH o k) ≡ LT.layoutH (mapOp h o) (λ q → mapLayout h (k (position (mapC h) q)))
layoutH-nat (Rectangle w ht s) k _ = rectangle-nat w ht s
layoutH-nat (Segment w ht s)   k _ = segment-nat w ht s
layoutH-nat (Disc r s)         k _ = disc-nat r s
layoutH-nat (Text w ht n t s)  k _ rewrite h-0 = refl
layoutH-nat (Path w ht d s)    k _ = pathL-nat w ht d s
layoutH-nat (Spacer w ht)      k _ = refl
layoutH-nat (Beside al)        k _ = besideA-nat al (k zero) (k (suc zero))
layoutH-nat (Above al)         k _ = aboveA-nat al (k zero) (k (suc zero))
layoutH-nat Atop               k _ = atop-nat (k zero) (k (suc zero))
layoutH-nat LabelAbove         k _ = labelAbove-nat (k zero) (k (suc zero))
layoutH-nat LabelBelow         k _ = labelBelow-nat (k zero) (k (suc zero))
layoutH-nat (Place w ht x y)   k _ = place-nat w ht x y (k tt)
layoutH-nat (Overlay w ht)     k _ = overlay-nat w ht (k zero) (k (suc zero))
layoutH-nat (Named n)          k _ = named-nat n (k tt)
layoutH-nat (Connect a pa b pb s) k (npa , npb) = connectP-nat a pa b pb s (k tt) npa npb

------------------------------------------------------------------------
-- Whole diagrams

-- the ports of a diagram are all carried
OkDia : Dia S → Set
OkDia (pure ())
OkDia (impure (o , k)) = OkOp o × (∀ q → OkDia (k q))

layout-natural-ok : ∀ t → OkDia t → LT.layout (mapDia h t) ≡ mapLayout h (LS.layout t)
layout-natural-ok (pure ())
layout-natural-ok (impure (o , k)) (ok , oks) =
  trans (LT.layoutCong (mapOp h o) (λ q → layout-natural-ok (k (position (mapC h) q)) (oks _)))
        (sym (layoutH-nat o (λ q → LS.layout (k q)) ok))

-- every port is carried when `h` preserves percentages: no condition on the diagram
module _ (pn : PctNat) where
  private
    portNat : ∀ p → PortNat p
    portNat (side s) = side-nat s
    portNat (at s p) = at-nat pn s p

    okOp : ∀ o → OkOp o
    okOp (Rectangle _ _ _)   = tt
    okOp (Segment _ _ _)     = tt
    okOp (Disc _ _)          = tt
    okOp (Text _ _ _ _ _)    = tt
    okOp (Path _ _ _ _)      = tt
    okOp (Spacer _ _)        = tt
    okOp (Beside _)          = tt
    okOp (Above _)           = tt
    okOp Atop                = tt
    okOp LabelAbove          = tt
    okOp LabelBelow          = tt
    okOp (Place _ _ _ _)     = tt
    okOp (Overlay _ _)       = tt
    okOp (Named _)           = tt
    okOp (Connect _ pa _ pb _) = portNat pa , portNat pb

    pullH : Handler (DiagramC S) (Layout T)
    pullH o k = LT.layoutH (mapOp h o) (λ q → k (position (mapC h) q))

    pullCong : Congruent (DiagramC S) (≡P.setoid (Layout T)) pullH
    pullCong o e = LT.layoutCong (mapOp h o) (λ q → e (position (mapC h) q))

  layout-natural : ∀ t → LT.layout (mapDia h t) ≡ mapLayout h (LS.layout t)
  layout-natural t =
    trans (pfold-translate (≡P.setoid (Layout T)) LT.layoutCong (mapC h) (λ ()) t)
          (sym (pfold-rel (λ l l′ → mapLayout h l ≡ l′) (λ o k k′ e → trans (layoutH-nat o k (okOp o)) (pullCong o e)) (λ ()) t))
