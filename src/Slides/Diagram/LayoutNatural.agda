{-# OPTIONS --safe --without-K #-}

-- Layout is natural in the scalar.
--
-- For an `Ops`-homomorphism `h : S → T` (`Slides.Diagram.Scalar.IsOpsHom`: it preserves
-- `0#`, `+`, `-`, `⊔`, `fromℕ`, `percentOf` as `_≡_`),
--
--     mapLayout h (layout_S d) ≡ layout_T (mapDia h d)
--
-- for every diagram `d : Dia S` (`layout-natural`): laying a diagram out and then
-- sending every coordinate through `h` is the same as sending the sizes of the
-- diagram through `h` first.  The proof is a fold-fusion: each operation of
-- `Slides.Diagram.Place` commutes with `h` (the lemmas below, one per operation), and
-- `layoutAlgebra` and `rescale h` are written case by case from them.
--
-- What is *required* of `h`: exactly the six equations of `IsOpsHom`.  No order, no
-- injectivity and no condition on where `-` is applied: layout only computes with the
-- operations, and each is preserved on the nose.  (That the layout is *valid*, with
-- sizes and offsets non-negative, is a different matter, `Slides.Diagram.Valid`.
-- Preserving `-` is what the ℕ monus asks of an evaluation; for `Slides.Diagram.Expr`
-- it holds because both sides interpret `-` by the same monus.)
--
-- The consequence used by the page player: `h = eval ρ : Expr V → ℕ` (an
-- `Ops`-homomorphism by `Slides.Diagram.Expr.eval-hom`) gives
--
--     mapLayout (eval ρ) (layout_Expr tmpl) ≡ layout_ℕ (mapDia (eval ρ) tmpl)
--
-- so a template laid out once, symbolically, and evaluated, is the layout of the
-- instance (`layout-eval`).

module Slides.Diagram.LayoutNatural where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; _*_; _/_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram using (Style)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open import Slides.Diagram.Scalar using (Ops; IsOpsHom; natOps)
open import Slides.Diagram.Syntax
open import Slides.Diagram.TextMetrics using (textWidth)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Bool using (true; false)
import Slides.Diagram.Place as Place
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Expr using (Expr; exprOps; eval; eval-hom)

private
  mapPair : ∀ {S T : Set} → (S → T) → S × S → T × T
  mapPair f (x , y) = f x , f y

  -- `map` commutes with a family of equations
  map-comm : ∀ {A B C D : Set} (f : A → C) (g : A → B) (f′ : B → D) (g′ : C → D) →
             (∀ x → f′ (g x) ≡ g′ (f x)) → ∀ xs → map f′ (map g xs) ≡ map g′ (map f xs)
  map-comm f g f′ g′ eq []       = refl
  map-comm f g f′ g′ eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-comm f g f′ g′ eq xs)

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
  cong₄ f refl refl refl refl = refl

module _ {S T : Set} (O : Ops S) (P : Ops T) (h : S → T) (Hom : IsOpsHom O P h) where
  private
    module PS = Place O
    module PT = Place P
    module OS = Ops O
    module OT = Ops P
  open IsOpsHom Hom

  h-dbl : ∀ x → h (OS.dbl x) ≡ OT.dbl (h x)
  h-dbl x = h-+ x x

  ----------------------------------------------------------------------
  -- Shifting and framing

  shiftDraw-natural : ∀ dx dy d → mapDraw h (PS.shiftDraw dx dy d) ≡ PT.shiftDraw (h dx) (h dy) (mapDraw h d)
  shiftDraw-natural dx dy (rect x y w ht s)  = cong₂ (λ a b → rect a b (h w) (h ht) s) (h-+ x dx) (h-+ y dy)
  shiftDraw-natural dx dy (circle x y r s)   = cong₂ (λ a b → circle a b (h r) s) (h-+ x dx) (h-+ y dy)
  shiftDraw-natural dx dy (line a b c d s)   =
    cong₄ (λ p q r t → line p q r t s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
  shiftDraw-natural dx dy (arrow a b c d s)  =
    cong₄ (λ p q r t → arrow p q r t s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
  shiftDraw-natural dx dy (label x y n t s)  = cong₂ (λ a b → label a b n t s) (h-+ x dx) (h-+ y dy)

  shiftAnchor-natural : ∀ dx dy a → mapAnchor h (PS.shiftAnchor dx dy a) ≡ PT.shiftAnchor (h dx) (h dy) (mapAnchor h a)
  shiftAnchor-natural dx dy (n , box l tp w ht) = cong₂ (λ a b → n , box a b (h w) (h ht)) (h-+ l dx) (h-+ tp dy)

  inFrame-natural : ∀ w ht dx dy d →
    mapLayout h (PS.inFrame w ht dx dy d) ≡ PT.inFrame (h w) (h ht) (h dx) (h dy) (mapLayout h d)
  inFrame-natural w ht dx dy d =
    cong₂ (layout (h w) (h ht))
      (map-comm (mapDraw h) (PS.shiftDraw dx dy) (mapDraw h) (PT.shiftDraw (h dx) (h dy)) (shiftDraw-natural dx dy) (Layout.draws d))
      (map-comm (mapAnchor h) (PS.shiftAnchor dx dy) (mapAnchor h) (PT.shiftAnchor (h dx) (h dy)) (shiftAnchor-natural dx dy) (Layout.anchors d))

  overlay-natural : ∀ w ht a b →
    mapLayout h (PS.overlay w ht a b) ≡ PT.overlay (h w) (h ht) (mapLayout h a) (mapLayout h b)
  overlay-natural w ht a b =
    cong₂ (layout (h w) (h ht)) (LP.map-++ (mapDraw h) (Layout.draws a) (Layout.draws b))
                                (LP.map-++ (mapAnchor h) (Layout.anchors a) (Layout.anchors b))

  combine-natural : ∀ w ht px py qx qy a b →
    mapLayout h (PS.combine w ht (px , py) a (qx , qy) b)
    ≡ PT.combine (h w) (h ht) (h px , h py) (mapLayout h a) (h qx , h qy) (mapLayout h b)
  combine-natural w ht px py qx qy a b =
    trans (overlay-natural w ht (PS.inFrame w ht px py a) (PS.inFrame w ht qx qy b))
          (cong₂ (PT.overlay (h w) (h ht)) (inFrame-natural w ht px py a) (inFrame-natural w ht qx qy b))

  ----------------------------------------------------------------------
  -- Primitives

  rectangle-natural : ∀ w ht s → mapLayout h (PS.rectangle w ht s) ≡ PT.rectangle (h w) (h ht) s
  rectangle-natural w ht s rewrite h-0 = refl

  disc-natural : ∀ r s → mapLayout h (PS.disc r s) ≡ PT.disc (h r) s
  disc-natural r s rewrite h-dbl r = refl

  segment-natural : ∀ w ht s → mapLayout h (PS.segment w ht s) ≡ PT.segment (h w) (h ht) s
  segment-natural w ht s rewrite h-0 | h-dbl w | h-dbl ht = refl

  text-natural : ∀ pct size t s → mapLayout h (PS.text pct size t s) ≡ PT.text pct size t s
  text-natural pct size t s
    rewrite h-fromℕ ((textWidth size t * pct) / 100) | h-fromℕ ((size * 3) / 2) = refl

  spacer-natural : ∀ w ht → mapLayout h (PS.spacer w ht) ≡ PT.spacer (h w) (h ht)
  spacer-natural w ht = refl

  ----------------------------------------------------------------------
  -- Combining

  valignOffset-natural : ∀ al outer inner →
    h (PS.valignOffset al outer inner) ≡ PT.valignOffset al (h outer) (h inner)
  valignOffset-natural top    outer inner = h-0
  valignOffset-natural middle outer inner = h-- outer inner
  valignOffset-natural bottom outer inner = trans (h-dbl (outer OS.- inner)) (cong OT.dbl (h-- outer inner))

  alignOffset-natural : ∀ al outer inner →
    h (PS.alignOffset al outer inner) ≡ PT.alignOffset al (h outer) (h inner)
  alignOffset-natural left    outer inner = h-0
  alignOffset-natural centred outer inner = h-- outer inner
  alignOffset-natural right   outer inner = trans (h-dbl (outer OS.- inner)) (cong OT.dbl (h-- outer inner))

  atop-natural : ∀ a b → mapLayout h (PS.atop a b) ≡ PT.atop (mapLayout h a) (mapLayout h b)
  atop-natural a b =
    trans (combine-natural W H (W OS.- wa) (H OS.- ha) (W OS.- wb) (H OS.- hb) a b) eq
    where
      wa = Layout.width a ; ha = Layout.height a ; wb = Layout.width b ; hb = Layout.height b
      W = wa OS.⊔ wb ; H = ha OS.⊔ hb
      eq : PT.combine (h W) (h H) (h (W OS.- wa) , h (H OS.- ha)) (mapLayout h a)
                      (h (W OS.- wb) , h (H OS.- hb)) (mapLayout h b)
           ≡ PT.atop (mapLayout h a) (mapLayout h b)
      eq rewrite h-- W wa | h-- H ha | h-- W wb | h-- H hb | h-⊔ wa wb | h-⊔ ha hb = refl

  besideA-natural : ∀ al a b → mapLayout h (PS.besideA al a b) ≡ PT.besideA al (mapLayout h a) (mapLayout h b)
  besideA-natural al a b =
    trans (combine-natural W H OS.0# (PS.valignOffset al H ha) (OS.dbl wa) (PS.valignOffset al H hb) a b) eq
    where
      wa = Layout.width a ; ha = Layout.height a ; wb = Layout.width b ; hb = Layout.height b
      W = wa OS.+ wb ; H = ha OS.⊔ hb
      eq : PT.combine (h W) (h H) (h OS.0# , h (PS.valignOffset al H ha)) (mapLayout h a)
                      (h (OS.dbl wa) , h (PS.valignOffset al H hb)) (mapLayout h b)
           ≡ PT.besideA al (mapLayout h a) (mapLayout h b)
      eq rewrite h-0 | valignOffset-natural al H ha | valignOffset-natural al H hb
               | h-dbl wa | h-+ wa wb | h-⊔ ha hb = refl

  aboveA-natural : ∀ al a b → mapLayout h (PS.aboveA al a b) ≡ PT.aboveA al (mapLayout h a) (mapLayout h b)
  aboveA-natural al a b =
    trans (combine-natural W H (PS.alignOffset al W wa) OS.0# (PS.alignOffset al W wb) (OS.dbl ha) a b) eq
    where
      wa = Layout.width a ; ha = Layout.height a ; wb = Layout.width b ; hb = Layout.height b
      W = wa OS.⊔ wb ; H = ha OS.+ hb
      eq : PT.combine (h W) (h H) (h (PS.alignOffset al W wa) , h OS.0#) (mapLayout h a)
                      (h (PS.alignOffset al W wb) , h (OS.dbl ha)) (mapLayout h b)
           ≡ PT.aboveA al (mapLayout h a) (mapLayout h b)
      eq rewrite h-0 | alignOffset-natural al W wa | alignOffset-natural al W wb
               | h-dbl ha | h-+ ha hb | h-⊔ wa wb = refl

  spacer-0 : ∀ x → mapLayout h (PS.spacer OS.0# x) ≡ PT.spacer OT.0# (h x)
  spacer-0 x rewrite h-0 = refl

  labelAbove-natural : ∀ l d → mapLayout h (PS.labelAbove l d) ≡ PT.labelAbove (mapLayout h l) (mapLayout h d)
  labelAbove-natural l d =
    trans (aboveA-natural centred l (PS.aboveA centred d sp))
      (cong (PT.aboveA centred (mapLayout h l))
        (trans (aboveA-natural centred d sp)
          (cong (PT.aboveA centred (mapLayout h d)) (spacer-0 (Layout.height l)))))
    where sp = PS.spacer OS.0# (Layout.height l)

  labelBelow-natural : ∀ l d → mapLayout h (PS.labelBelow l d) ≡ PT.labelBelow (mapLayout h l) (mapLayout h d)
  labelBelow-natural l d =
    trans (aboveA-natural centred sp (PS.aboveA centred d l))
      (cong₂ (PT.aboveA centred) (spacer-0 (Layout.height l)) (aboveA-natural centred d l))
    where sp = PS.spacer OS.0# (Layout.height l)

  ----------------------------------------------------------------------
  -- Names and connections

  named-natural : ∀ n d → mapLayout h (PS.named n d) ≡ PT.named n (mapLayout h d)
  named-natural n d rewrite h-0 = refl

  findAnchor-natural : ∀ n as →
    PT.findAnchor n (map (mapAnchor h) as) ≡ Maybe.map (mapBox h) (PS.findAnchor n as)
  findAnchor-natural n []            = refl
  findAnchor-natural n ((m , b) ∷ as) with ⌊ n ≟ m ⌋
  ... | true  = refl
  ... | false = findAnchor-natural n as

  portPoint-natural : ∀ p b → PT.portPoint p (mapBox h b) ≡ mapPair h (PS.portPoint p b)
  portPoint-natural (side north)  (box l tp w ht) = cong₂ _,_ (sym (h-+ l w)) refl
  portPoint-natural (side south)  (box l tp w ht) =
    cong₂ _,_ (sym (h-+ l w)) (trans (cong (h tp OT.+_) (sym (h-dbl ht))) (sym (h-+ tp (OS.dbl ht))))
  portPoint-natural (side east)   (box l tp w ht) =
    cong₂ _,_ (trans (cong (h l OT.+_) (sym (h-dbl w))) (sym (h-+ l (OS.dbl w)))) (sym (h-+ tp ht))
  portPoint-natural (side west)   (box l tp w ht) = cong₂ _,_ refl (sym (h-+ tp ht))
  portPoint-natural (side middle) (box l tp w ht) = cong₂ _,_ (sym (h-+ l w)) (sym (h-+ tp ht))
  portPoint-natural (at north q)  (box l tp w ht) =
    cong₂ _,_ (trans (cong (h l OT.+_) (trans (cong (OT.percentOf q) (sym (h-dbl w))) (sym (h-percentOf q (OS.dbl w)))))
                     (sym (h-+ l (OS.percentOf q (OS.dbl w))))) refl
  portPoint-natural (at south q)  (box l tp w ht) =
    cong₂ _,_ (trans (cong (h l OT.+_) (trans (cong (OT.percentOf q) (sym (h-dbl w))) (sym (h-percentOf q (OS.dbl w)))))
                     (sym (h-+ l (OS.percentOf q (OS.dbl w)))))
              (trans (cong (h tp OT.+_) (sym (h-dbl ht))) (sym (h-+ tp (OS.dbl ht))))
  portPoint-natural (at east q)   (box l tp w ht) =
    cong₂ _,_ (trans (cong (h l OT.+_) (sym (h-dbl w))) (sym (h-+ l (OS.dbl w))))
              (trans (cong (h tp OT.+_) (trans (cong (OT.percentOf q) (sym (h-dbl ht))) (sym (h-percentOf q (OS.dbl ht)))))
                     (sym (h-+ tp (OS.percentOf q (OS.dbl ht)))))
  portPoint-natural (at west q)   (box l tp w ht) =
    cong₂ _,_ refl
              (trans (cong (h tp OT.+_) (trans (cong (OT.percentOf q) (sym (h-dbl ht))) (sym (h-percentOf q (OS.dbl ht)))))
                     (sym (h-+ tp (OS.percentOf q (OS.dbl ht)))))
  portPoint-natural (at middle q) b               = portPoint-natural (side middle) b

  connectP-natural : ∀ a pa b pb s d →
    mapLayout h (PS.connectP a pa b pb s d) ≡ PT.connectP a pa b pb s (mapLayout h d)
  connectP-natural a pa b pb s d
    rewrite findAnchor-natural a (Layout.anchors d) | findAnchor-natural b (Layout.anchors d)
    with PS.findAnchor a (Layout.anchors d) | PS.findAnchor b (Layout.anchors d)
  ... | just ba | just bb
    rewrite portPoint-natural pa ba | portPoint-natural pb bb =
    cong₂ (layout (h (Layout.width d)) (h (Layout.height d)))
          (trans (LP.map-++ (mapDraw h) (Layout.draws d) (arrow (proj₁ (PS.portPoint pa ba)) (proj₂ (PS.portPoint pa ba))
                                                               (proj₁ (PS.portPoint pb bb)) (proj₂ (PS.portPoint pb bb)) s ∷ [])) refl)
          refl
  ... | just _  | nothing = refl
  ... | nothing | _       = refl

  ----------------------------------------------------------------------
  -- The theorem

  private
    module LS = LayoutWith O
    module LT = LayoutWith P

  layout-natural : ∀ d → mapLayout h (LS.layout d) ≡ LT.layout (mapDia h d)
  layout-natural (pure ())
  layout-natural (impure (Rectangle w ht s , k)) = rectangle-natural w ht s
  layout-natural (impure (Disc r s , k))         = disc-natural r s
  layout-natural (impure (Segment w ht s , k))   = segment-natural w ht s
  layout-natural (impure (Text pct size t s , k)) = text-natural pct size t s
  layout-natural (impure (Spacer w ht , k))      = spacer-natural w ht
  layout-natural (impure (Beside al , k))        =
    trans (besideA-natural al (LS.layout (k zero)) (LS.layout (k (suc zero)))) (cong₂ (PT.besideA al) (layout-natural (k zero)) (layout-natural (k (suc zero))))
  layout-natural (impure (Above al , k))         =
    trans (aboveA-natural al (LS.layout (k zero)) (LS.layout (k (suc zero)))) (cong₂ (PT.aboveA al) (layout-natural (k zero)) (layout-natural (k (suc zero))))
  layout-natural (impure (Atop , k))             =
    trans (atop-natural (LS.layout (k zero)) (LS.layout (k (suc zero)))) (cong₂ PT.atop (layout-natural (k zero)) (layout-natural (k (suc zero))))
  layout-natural (impure (LabelAbove , k))       =
    trans (labelAbove-natural (LS.layout (k zero)) (LS.layout (k (suc zero)))) (cong₂ PT.labelAbove (layout-natural (k zero)) (layout-natural (k (suc zero))))
  layout-natural (impure (LabelBelow , k))       =
    trans (labelBelow-natural (LS.layout (k zero)) (LS.layout (k (suc zero)))) (cong₂ PT.labelBelow (layout-natural (k zero)) (layout-natural (k (suc zero))))
  layout-natural (impure (Named n , k))          =
    trans (named-natural n (LS.layout (k tt))) (cong (PT.named n) (layout-natural (k tt)))
  layout-natural (impure (Connect a pa b pb s , k)) =
    trans (connectP-natural a pa b pb s (LS.layout (k tt))) (cong (PT.connectP a pa b pb s) (layout-natural (k tt)))

------------------------------------------------------------------------
-- Templates: lay out once, evaluate later

-- a diagram over symbolic sizes, laid out in `Expr V` and evaluated at an assignment, is the
-- layout of the diagram with those sizes evaluated
layout-eval : ∀ {V} (ρ : V → ℕ) (d : Dia (Expr V)) →
  mapLayout (eval ρ) (LayoutWith.layout exprOps d) ≡ LayoutWith.layout natOps (mapDia (eval ρ) d)
layout-eval ρ = layout-natural exprOps natOps (eval ρ) (eval-hom ρ)
