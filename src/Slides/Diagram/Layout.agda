{-# OPTIONS --safe --without-K #-}

-- The placement fold: `layout d = pfold layoutH d`, the handler of the layout signature reading
-- a diagram (a description: which frames sit where, relative to each other) into a `Layout` (a
-- drawing: frames resolved, primitives at absolute positions, named boxes recorded).
--
--   primitives       a frame of the stored size with at most one drawing
--   Beside Above     frames touch; sizes add in one direction, join in the other
--   Atop             both centred in the larger frame, the second drawn second
--   LabelAbove/Below caption, diagram, room of the caption's height
--   Place Overlay    the frame is declared, the children are not centred
--   Named Connect    the child's geometry, plus a name, or one arrow
--
-- Generic laws (congruence, bind, fusion along a change of scalar) come from
-- `Container.Interpret.Plain`; the specific ones are in `Laws`, `Natural`, `Names`.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Layout {S : Set} (Sp : Space S) where

open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Syntax
import Slides.Diagram.Place Sp as P

layoutH : Handler (DiagramC S) (Layout S)
layoutH (Rectangle w h s)     k = P.rectangle w h s
layoutH (Segment w h s)       k = P.segment w h s
layoutH (Disc r s)            k = P.disc r s
layoutH (Ellipse a b s)       k = P.ellipseL a b s
layoutH (Polyline c ps s)     k = P.polyline c ps s
layoutH (Text w h n t s)      k = P.text w h n t s
layoutH (Path w h d s)        k = P.pathL w h d s
layoutH (Spacer w h)          k = P.spacer w h
layoutH (Beside al)           k = P.besideA al (k zero) (k (suc zero))
layoutH (Above al)            k = P.aboveA al (k zero) (k (suc zero))
layoutH Atop                  k = P.atop (k zero) (k (suc zero))
layoutH LabelAbove            k = P.labelAbove (k zero) (k (suc zero))
layoutH LabelBelow            k = P.labelBelow (k zero) (k (suc zero))
layoutH (Place w h x y)       k = P.place w h x y (k tt)
layoutH (Overlay w h)         k = P.overlay w h (k zero) (k (suc zero))
layoutH (Named n)             k = P.named n (k tt)
layoutH (Connect a pa b pb s) k = P.connectP a pa b pb s (k tt)

layout : Dia S → Layout S
layout = pfold (DiagramC S) layoutH (λ ())

layoutCong : Congruent (DiagramC S) (≡P.setoid (Layout S)) layoutH
layoutCong (Rectangle _ _ _)   e = refl
layoutCong (Segment _ _ _)     e = refl
layoutCong (Disc _ _)          e = refl
layoutCong (Ellipse _ _ _)     e = refl
layoutCong (Polyline _ _ _)    e = refl
layoutCong (Text _ _ _ _ _)    e = refl
layoutCong (Path _ _ _ _)      e = refl
layoutCong (Spacer _ _)        e = refl
layoutCong (Beside al)         e = cong₂ (P.besideA al) (e zero) (e (suc zero))
layoutCong (Above al)          e = cong₂ (P.aboveA al) (e zero) (e (suc zero))
layoutCong Atop                e = cong₂ P.atop (e zero) (e (suc zero))
layoutCong LabelAbove          e = cong₂ P.labelAbove (e zero) (e (suc zero))
layoutCong LabelBelow          e = cong₂ P.labelBelow (e zero) (e (suc zero))
layoutCong (Place w h x y)     e = cong (P.place w h x y) (e tt)
layoutCong (Overlay w h)       e = cong₂ (P.overlay w h) (e zero) (e (suc zero))
layoutCong (Named n)           e = cong (P.named n) (e tt)
layoutCong (Connect a pa b pb s) e = cong (P.connectP a pa b pb s) (e tt)
