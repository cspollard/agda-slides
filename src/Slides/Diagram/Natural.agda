{-# OPTIONS --safe --without-K #-}

-- Layout is natural in the scalar: changing units (ℕ to ℚ, say) before or after placing gives
-- the same picture.
--
-- For an order embedding `h : S → T` of ordered monoids (`IsOrdMonHom`: `0`, `+`, order and its
-- reflection; the join and exact differences follow, `Slides.Scalar.Core`),
--
--     layout_T (mapDia h d) ≡ mapLayout h (layout_S d)
--
-- for every diagram whose connection ports `h` carries (`layout-natural-ok`): every `side`
-- port, and, if `h` also preserves percentages (`PctNat`), every port (`layout-natural`).
-- ℕ into ℚ preserves percentages only where exact, hence the first form for diagrams that
-- attach by sides.  Centring subtracts only a smaller size from a larger, exactly where `h`
-- preserves `-`, so layout itself needs no hypothesis.
--
--      d : Dia S ──layout_S──▶ Layout S
--        │ mapDia h               │ mapLayout h
--        ▼                        ▼
--      Dia T ────layout_T────▶ Layout T
--
-- Proof: one equation per placement operation (`*-nat`), then the generic fusion of
-- `Container.Interpret.Plain` (`pfold-rel-translate`: the relation is `mapLayout h l ≡ l′`).

open import Slides.Scalar.Core using (OrdMon; IsOrdMonHom)
open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Natural {S T : Set} (Sp : Space S) (Tp : Space T) (h : S → T)
         (H : IsOrdMonHom (Space.ord Sp) (Space.ord Tp) h) where

open import Data.Fin using (zero; suc)
open import Function.Nary.NonDependent using (congₙ)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
import Data.List.Properties as ListP
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold-rel-translate)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Syntax hiding (ellipse)
import Slides.Diagram.Place Sp as PS
import Slides.Diagram.Place Tp as PT
import Slides.Diagram.Layout Sp as LS
open import Slides.Diagram.Overlay using (IsOverlayHom)
import Slides.Diagram.Laws Sp as LawsS
import Slides.Diagram.Laws Tp as LawsT
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

-- Shifting, framing, overlaying: only `+` is used

-- `map` commutes with a pointwise-natural change of the elements
map-nat : ∀ {A B C D : Set} (f : A → B) (g : B → D) (f′ : A → C) (g′ : C → D) →
          (∀ x → g (f x) ≡ g′ (f′ x)) → ∀ xs → map g (map f xs) ≡ map g′ (map f′ xs)
map-nat f g f′ g′ e xs = trans (map-fuse e xs) (sym (map-fuse (λ _ → refl) xs))

shiftDraw-nat : ∀ dx dy d → mapDraw h (PS.shiftDraw dx dy d) ≡ PT.shiftDraw (h dx) (h dy) (mapDraw h d)
shiftDraw-nat dx dy (rect x y w ht s)   = cong₂ (λ u v → rect u v (h w) (h ht) s) (h-+ x dx) (h-+ y dy)
shiftDraw-nat dx dy (circle x y r s)    = cong₂ (λ u v → circle u v (h r) s) (h-+ x dx) (h-+ y dy)
shiftDraw-nat dx dy (ellipse x y a b s) = cong₂ (λ u v → ellipse u v (h a) (h b) s) (h-+ x dx) (h-+ y dy)
shiftDraw-nat dx dy (poly c ps s)       =
  cong (λ qs → poly c qs s) (map-nat (PS.shiftPt dx dy) (mapPt h) (mapPt h) (PT.shiftPt (h dx) (h dy)) (λ p → cong₂ _,_ (h-+ _ dx) (h-+ _ dy)) ps)
shiftDraw-nat dx dy (line a b c d s)    =
  congₙ 4 (λ a′ b′ c′ d′ → line a′ b′ c′ d′ s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
shiftDraw-nat dx dy (arrow a b c d s)   =
  congₙ 4 (λ a′ b′ c′ d′ → arrow a′ b′ c′ d′ s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
shiftDraw-nat dx dy (label x y n t s)   = cong₂ (λ u v → label u v n t s) (h-+ x dx) (h-+ y dy)
shiftDraw-nat dx dy (path x y d s)      = cong₂ (λ u v → Draw.path u v d s) (h-+ x dx) (h-+ y dy)

mapDraws-shift : ∀ dx dy ds → map (mapDraw h) (map (PS.shiftDraw dx dy) ds) ≡ map (PT.shiftDraw (h dx) (h dy)) (map (mapDraw h) ds)
mapDraws-shift dx dy = map-nat _ _ _ _ (shiftDraw-nat dx dy)

shiftAnchor-nat : ∀ dx dy a → mapAnchor h (PS.shiftAnchor dx dy a) ≡ PT.shiftAnchor (h dx) (h dy) (mapAnchor h a)
shiftAnchor-nat dx dy (n , box l t w ht) = cong₂ (λ u v → n , box u v (h w) (h ht)) (h-+ l dx) (h-+ t dy)

anchors-shift : ∀ dx dy as → map (mapAnchor h) (map (PS.shiftAnchor dx dy) as) ≡ map (PT.shiftAnchor (h dx) (h dy)) (map (mapAnchor h) as)
anchors-shift dx dy = map-nat _ _ _ _ (shiftAnchor-nat dx dy)

inFrame-nat : ∀ w ht dx dy l →
  mapLayout h (PS.inFrame w ht dx dy l) ≡ PT.inFrame (h w) (h ht) (h dx) (h dy) (mapLayout h l)
inFrame-nat w ht dx dy (mkLayout _ _ ds as) =
  cong₂ (mkLayout (h w) (h ht)) (mapDraws-shift dx dy ds) (anchors-shift dx dy as)

overlay-nat : ∀ w ht a b →
  mapLayout h (PS.overlay w ht a b) ≡ PT.overlay (h w) (h ht) (mapLayout h a) (mapLayout h b)
overlay-nat w ht (mkLayout _ _ d₁ a₁) (mkLayout _ _ d₂ a₂) =
  cong₂ (mkLayout (h w) (h ht)) (ListP.map-++ (mapDraw h) d₁ d₂) (ListP.map-++ (mapAnchor h) a₁ a₂)

-- layouts overlay the same way before and after `h`
overlay-hom : IsOverlayHom LawsS.layoutOverlay LawsT.layoutOverlay (mapLayout h)
overlay-hom = record { F-⊙ = λ { x@(mkLayout wa ha _ _) y@(mkLayout wb hb _ _) →
  trans (overlay-nat (wa A.⊔ wb) (ha A.⊔ hb) x y)
        (cong₂ (λ w ht → PT.overlay w ht (mapLayout h x) (mapLayout h y)) (h-⊔ wa wb) (h-⊔ ha hb)) } }

combine-nat : ∀ w ht px py qx qy a b →
  mapLayout h (PS.combine w ht (px , py) a (qx , qy) b)
    ≡ PT.combine (h w) (h ht) (h px , h py) (mapLayout h a) (h qx , h qy) (mapLayout h b)
combine-nat w ht px py qx qy a b =
  trans (overlay-nat w ht (PS.inFrame w ht px py a) (PS.inFrame w ht qx qy b))
        (cong₂ (PT.overlay (h w) (h ht)) (inFrame-nat w ht px py a) (inFrame-nat w ht qx qy b))

place-nat : ∀ w ht x y l →
  mapLayout h (PS.place w ht x y l) ≡ PT.place (h w) (h ht) (h x) (h y) (mapLayout h l)
place-nat w ht x y l = trans (inFrame-nat w ht _ _ l) (cong₂ (λ u v → PT.inFrame (h w) (h ht) u v (mapLayout h l)) (dbl-nat x) (dbl-nat y))

-- Primitives

disc-nat : ∀ r s → mapLayout h (PS.disc r s) ≡ PT.disc (h r) s
disc-nat r s = cong (λ z → mkLayout z z (circle z z (h r) s ∷ []) []) (dbl-nat r)

ellipse-nat : ∀ a b s → mapLayout h (PS.ellipseL a b s) ≡ PT.ellipseL (h a) (h b) s
ellipse-nat a b s = cong₂ (λ u v → mkLayout u v (ellipse u v (h a) (h b) s ∷ []) []) (dbl-nat a) (dbl-nat b)

-- the extent of the points is carried: `h` preserves `0` and the join
extent-nat : ∀ (g : S × S → S) (g′ : T × T → T) → (∀ p → h (g p) ≡ g′ (mapPt h p)) →
             ∀ ps → h (PS.extent (map g ps)) ≡ PT.extent (map g′ (map (mapPt h) ps))
extent-nat g g′ e []       = h-0
extent-nat g g′ e (p ∷ ps) = trans (h-⊔ (g p) _) (cong₂ B._⊔_ (e p) (extent-nat g g′ e ps))

polyline-nat : ∀ c ps s → mapLayout h (PS.polyline c ps s) ≡ PT.polyline c (map (mapPt h) ps) s
polyline-nat c ps s =
  congₙ 3 (λ w ht qs → mkLayout w ht (poly c qs s ∷ []) [])
    (extent-nat proj₁ proj₁ (λ _ → refl) ps) (extent-nat proj₂ proj₂ (λ _ → refl) ps)
    (map-nat PS.dblPt (mapPt h) (mapPt h) PT.dblPt (λ p → cong₂ _,_ (dbl-nat _) (dbl-nat _)) ps)

segment-nat : ∀ w ht s → mapLayout h (PS.segment w ht s) ≡ PT.segment (h w) (h ht) s
segment-nat w ht s =
  congₙ 3 (λ z u v → mkLayout (h w) (h ht) (line z z u v s ∷ []) []) h-0 (dbl-nat w) (dbl-nat ht)

rectangle-nat : ∀ w ht s → mapLayout h (PS.rectangle w ht s) ≡ PT.rectangle (h w) (h ht) s
rectangle-nat w ht s = cong (λ z → mkLayout (h w) (h ht) (rect z z (h w) (h ht) s ∷ []) []) h-0

pathL-nat : ∀ w ht d s → mapLayout h (PS.pathL w ht d s) ≡ PT.pathL (h w) (h ht) d s
pathL-nat w ht d s = cong (λ z → mkLayout (h w) (h ht) (Draw.path z z d s ∷ []) []) h-0

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

-- Names and connections

named-nat : ∀ n l → mapLayout h (PS.named n l) ≡ PT.named n (mapLayout h l)
named-nat n (mkLayout w ht ds as) =
  cong (λ z → mkLayout (h w) (h ht) (map (mapDraw h) ds) ((n , box z z (h w) (h ht)) ∷ map (mapAnchor h) as)) h-0

find-map : ∀ n as → PT.findAnchor n (map (mapAnchor h) as) ≡ Maybe.map (mapBox h) (PS.findAnchor n as)
find-map n []             = refl
find-map n ((m , b) ∷ as) with n ≟ m
... | yes _ = refl
... | no _  = find-map n as

-- a port is carried when the point it names is
PortNat : Port → Set
PortNat p = ∀ b → PT.portPoint p (mapBox h b) ≡ (h (proj₁ (PS.portPoint p b)) , h (proj₂ (PS.portPoint p b)))

-- the x or y of a port: an offset from the box's edge, by half a side or `dbl` of it
plus-dbl : ∀ l w → h (l A.+ PS.dbl w) ≡ h l B.+ PT.dbl (h w)
plus-dbl l w = trans (h-+ l _) (cong (h l B.+_) (dbl-nat w))

side-nat : ∀ s → PortNat (side s)
side-nat north  (box l t w ht) = cong₂ _,_ (sym (h-+ l w)) refl
side-nat south  (box l t w ht) = cong₂ _,_ (sym (h-+ l w)) (sym (plus-dbl t ht))
side-nat east   (box l t w ht) = cong₂ _,_ (sym (plus-dbl l w)) (sym (h-+ t ht))
side-nat west   (box l t w ht) = cong₂ _,_ refl (sym (h-+ t ht))
side-nat middle (box l t w ht) = cong₂ _,_ (sym (h-+ l w)) (sym (h-+ t ht))

-- `h` preserves percentages
PctNat : Set
PctNat = ∀ p x → h (A.pct p x) ≡ B.pct p (h x)

-- an offset of a percentage of `dbl w` from `l`
plus-pct : PctNat → ∀ l p w → h (l A.+ A.pct p (PS.dbl w)) ≡ h l B.+ B.pct p (PT.dbl (h w))
plus-pct pn l p w = trans (h-+ l _) (cong (h l B.+_) (trans (pn p _) (cong (B.pct p) (dbl-nat w))))

at-nat : PctNat → ∀ s p → PortNat (at s p)
at-nat pn north  p (box l t w ht) = cong₂ _,_ (sym (plus-pct pn l p w)) refl
at-nat pn south  p (box l t w ht) = cong₂ _,_ (sym (plus-pct pn l p w)) (sym (plus-dbl t ht))
at-nat pn east   p (box l t w ht) = cong₂ _,_ (sym (plus-dbl l w)) (sym (plus-pct pn t p ht))
at-nat pn west   p (box l t w ht) = cong₂ _,_ refl (sym (plus-pct pn t p ht))
at-nat pn middle p b              = side-nat middle b

connectArrow-nat : ∀ pa pb s ma mb → PortNat pa → PortNat pb →
  map (mapDraw h) (PS.connectArrow pa pb s ma mb)
    ≡ PT.connectArrow pa pb s (Maybe.map (mapBox h) ma) (Maybe.map (mapBox h) mb)
connectArrow-nat pa pb s (just ba) (just bb) npa npb =
  sym (cong₂ (λ p q → arrow (proj₁ p) (proj₂ p) (proj₁ q) (proj₂ q) s ∷ []) (npa ba) (npb bb))
connectArrow-nat pa pb s (just _)  nothing   _ _ = refl
connectArrow-nat pa pb s nothing   _         _ _ = refl

connectP-nat : ∀ a pa b pb s l → PortNat pa → PortNat pb →
  mapLayout h (PS.connectP a pa b pb s l) ≡ PT.connectP a pa b pb s (mapLayout h l)
connectP-nat a pa b pb s (mkLayout w ht ds as) npa npb
  = cong (λ ds′ → mkLayout (h w) (h ht) ds′ (map (mapAnchor h) as))
      (trans (ListP.map-++ (mapDraw h) ds (PS.connectArrow pa pb s (PS.findAnchor a as) (PS.findAnchor b as)))
        (cong (map (mapDraw h) ds ++_)
          (trans (connectArrow-nat pa pb s (PS.findAnchor a as) (PS.findAnchor b as) npa npb)
            (cong₂ (PT.connectArrow pa pb s) (sym (find-map a as)) (sym (find-map b as))))))

-- One command at a time

OkOp : Op S → Set
OkOp (Connect _ pa _ pb _) = PortNat pa × PortNat pb
OkOp _                     = ⊤

layoutH-nat : ∀ o k → OkOp o →
  mapLayout h (LS.layoutH o k) ≡ LT.layoutH (mapOp h o) (λ q → mapLayout h (k q))
layoutH-nat (Rectangle w ht s) k _ = rectangle-nat w ht s
layoutH-nat (Segment w ht s)   k _ = segment-nat w ht s
layoutH-nat (Disc r s)         k _ = disc-nat r s
layoutH-nat (Text w ht n t s)  k _ = refl
layoutH-nat (Ellipse a b s)      k _ = ellipse-nat a b s
layoutH-nat (Polyline c ps s)  k _ = polyline-nat c ps s
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

-- Whole diagrams

-- the ports of a diagram are all carried
OkDia : Dia S → Set
OkDia (pure ())
OkDia (impure (o , k)) = OkOp o × (∀ q → OkDia (k q))

layout-natural-ok : ∀ t → OkDia t → LT.layout (mapDia h t) ≡ mapLayout h (LS.layout t)
layout-natural-ok (pure ())
layout-natural-ok (impure (o , k)) (ok , oks) =
  trans (LT.layoutCong (mapOp h o) (λ q → layout-natural-ok (k q) (oks _)))
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
    okOp (Ellipse _ _ _)     = tt
    okOp (Polyline _ _ _)    = tt
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

  layout-natural : ∀ t → LT.layout (mapDia h t) ≡ mapLayout h (LS.layout t)
  layout-natural t = sym (pfold-rel-translate (mapC h) (λ l l′ → mapLayout h l ≡ l′)
    (λ o k k′ e → trans (layoutH-nat o k (okOp o)) (LT.layoutCong (mapOp h o) (λ q → e q)))
    (λ ()) t)
