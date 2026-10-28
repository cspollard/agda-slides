{-# OPTIONS --safe --without-K #-}

-- A second fold of diagrams: which names are declared, and which names a `connect` cannot find.
--
-- `dangling d` lists the names that a `connect` refers to and that no `named` inside *that
-- connect's own diagram* declares; such a connection draws nothing, so a deck can assert
-- `dangling d ≡ []` (by `refl`) and have a misspelled name fail to typecheck.
-- `Slides.Diagram.Names.Soundness` proves that this guarantees every connection is drawn, and
-- that the declared names are exactly the names of the anchors of the layout.  Names do not
-- depend on sizes: the handler ignores the scalar entirely (`usage-mapDia`).
--
--   named "a" ─┐        usage = (declared names, names a connect could not find)
--              ├─ connect "a" "b"  ⇒  the second component is [] when both are declared below
--   named "b" ─┘

module Slides.Diagram.Names where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Container.Core using (position)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pfold-rel-translate)
open import Slides.Diagram.Syntax

Usage : Set
Usage = List String × List String

member : String → List String → Bool
member x []       = false
member x (y ∷ ys) = if ⌊ x ≟ y ⌋ then true else member x ys

private
  both : Usage → Usage → Usage
  both (d , r) (d′ , r′) = d ++ d′ , r ++ r′

-- declared names are in the order the layout keeps its anchors
usageH : ∀ {S} → Handler (DiagramC S) Usage
usageH (Rectangle _ _ _)   k = [] , []
usageH (Segment _ _ _)     k = [] , []
usageH (Disc _ _)          k = [] , []
usageH (Text _ _ _ _ _)    k = [] , []
usageH (Path _ _ _ _)      k = [] , []
usageH (Spacer _ _)        k = [] , []
usageH (Beside _)          k = both (k zero) (k (suc zero))
usageH (Above _)           k = both (k zero) (k (suc zero))
usageH Atop                k = both (k zero) (k (suc zero))
usageH LabelAbove          k = both (k zero) (k (suc zero))
usageH LabelBelow          k = both (k (suc zero)) (k zero)
usageH (Place _ _ _ _)     k = k tt
usageH (Overlay _ _)       k = both (k zero) (k (suc zero))
usageH (Named n)           k = n ∷ proj₁ (k tt) , proj₂ (k tt)
usageH (Connect a _ b _ _) k =
  proj₁ (k tt) , proj₂ (k tt) ++ filterᵇ (λ r → not (member r (proj₁ (k tt)))) (a ∷ b ∷ [])

usage : ∀ {S} → Dia S → Usage
usage = pfold (DiagramC _) usageH (λ ())

declared dangling : ∀ {S} → Dia S → List String
declared d = proj₁ (usage d)
dangling d = proj₂ (usage d)

usageCong : ∀ {S} → Congruent (DiagramC S) (≡P.setoid Usage) usageH
usageCong (Rectangle _ _ _)   e = refl
usageCong (Segment _ _ _)     e = refl
usageCong (Disc _ _)          e = refl
usageCong (Text _ _ _ _ _)    e = refl
usageCong (Path _ _ _ _)      e = refl
usageCong (Spacer _ _)        e = refl
usageCong (Beside _)          e rewrite e zero | e (suc zero) = refl
usageCong (Above _)           e rewrite e zero | e (suc zero) = refl
usageCong Atop                e rewrite e zero | e (suc zero) = refl
usageCong LabelAbove          e rewrite e zero | e (suc zero) = refl
usageCong LabelBelow          e rewrite e zero | e (suc zero) = refl
usageCong (Place _ _ _ _)     e = e tt
usageCong (Overlay _ _)       e rewrite e zero | e (suc zero) = refl
usageCong (Named _)           e rewrite e tt = refl
usageCong (Connect _ _ _ _ _) e rewrite e tt = refl

-- names do not depend on sizes
usage-mapDia : ∀ {S T} (f : S → T) (d : Dia S) → usage (mapDia f d) ≡ usage d
usage-mapDia f d =
  pfold-rel-translate (mapC f) (λ x y → y ≡ x)
    (λ o k k′ e → trans (usageCong (mapOp f o) (λ q → e (position (mapC f) q))) (same o k)) (λ ()) d
  where
    same : ∀ o k → usageH (mapOp f o) (λ q → k (position (mapC f) q)) ≡ usageH o k
    same (Rectangle _ _ _)   k = refl
    same (Segment _ _ _)     k = refl
    same (Disc _ _)          k = refl
    same (Text _ _ _ _ _)    k = refl
    same (Path _ _ _ _)      k = refl
    same (Spacer _ _)        k = refl
    same (Beside _)          k = refl
    same (Above _)           k = refl
    same Atop                k = refl
    same LabelAbove          k = refl
    same LabelBelow          k = refl
    same (Place _ _ _ _)     k = refl
    same (Overlay _ _)       k = refl
    same (Named _)           k = refl
    same (Connect _ _ _ _ _) k = refl
