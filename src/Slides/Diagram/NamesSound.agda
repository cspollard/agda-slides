{-# OPTIONS --safe --without-K #-}

-- `Slides.Diagram.Names.dangling` is sound: if it reports nothing, every
-- `connect` in the diagram draws an arrow (and none is silently dropped).
--
-- Two facts, each an induction over the diagram that mirrors `fold`:
--
--   * `names-fusion`: the declared names `Names` computes are exactly the names
--     of the anchors of the laid-out diagram (`anchorNames (layout d)`), in the
--     same order;
--   * `soundness`: `dangling d ≡ []` implies `Draws d`, which says that each
--     `connect` node, laid out over its own child, appends one arrow.
--
-- Neither needs anything of the scalar beyond `Ops`.

open import Slides.Diagram.Scalar using (Ops)

module Slides.Diagram.NamesSound {S : Set} (O : Ops S) where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
import Data.List.Properties as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram using (Style)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry using (Port; centred)
open import Slides.Diagram.Names
open import Slides.Diagram.Syntax
  using ( Dia; Algebra; fold; arity; Op; Rectangle; Disc; Segment; Text; Spacer; Raw
        ; Beside; Above; Atop; LabelAbove; LabelBelow; Named; Connect )
import Slides.Diagram.Layout as Lay
open import Slides.Diagram.Place O
open Ops O using (0#; fromℕ; _+_; _-_; _⊔_; dbl)
module LW = Lay.LayoutWith O

anchorNames : Layout S → List String
anchorNames l = map proj₁ (Layout.anchors l)

------------------------------------------------------------------------
-- Names survive the layout operations

names-inFrame : ∀ w h dx dy l → anchorNames (inFrame w h dx dy l) ≡ anchorNames l
names-inFrame w h dx dy l =
  trans (sym (L.map-∘ (Layout.anchors l))) (L.map-cong (λ { (n , b) → refl }) (Layout.anchors l))

names-combine : ∀ w h p a q b → anchorNames (combine w h p a q b) ≡ anchorNames a ++ anchorNames b
names-combine w h p a q b =
  trans (L.map-++ proj₁ (Layout.anchors (inFrame w h (proj₁ p) (proj₂ p) a))
                        (Layout.anchors (inFrame w h (proj₁ q) (proj₂ q) b)))
        (cong₂ _++_ (names-inFrame w h (proj₁ p) (proj₂ p) a) (names-inFrame w h (proj₁ q) (proj₂ q) b))

names-besideA : ∀ al a b → anchorNames (besideA al a b) ≡ anchorNames a ++ anchorNames b
names-besideA al a b =
  names-combine (width a + width b) (height a ⊔ height b)
    (0# , valignOffset al (height a ⊔ height b) (height a)) a
    (dbl (width a) , valignOffset al (height a ⊔ height b) (height b)) b

names-atop : ∀ a b → anchorNames (atop a b) ≡ anchorNames a ++ anchorNames b
names-atop a b =
  names-combine (width a ⊔ width b) (height a ⊔ height b)
    ((width a ⊔ width b) - width a , (height a ⊔ height b) - height a) a
    ((width a ⊔ width b) - width b , (height a ⊔ height b) - height b) b

names-above : ∀ al a b → anchorNames (aboveA al a b) ≡ anchorNames a ++ anchorNames b
names-above al a b =
  names-combine (width a ⊔ width b) (height a + height b)
    (alignOffset al (width a ⊔ width b) (width a) , 0#) a
    (alignOffset al (width a ⊔ width b) (width b) , dbl (height a)) b

names-labelAbove : ∀ lbl d → anchorNames (labelAbove lbl d) ≡ anchorNames lbl ++ anchorNames d
names-labelAbove lbl d =
  trans (names-above centred lbl (aboveA centred d (spacer 0# (height lbl))))
        (cong (anchorNames lbl ++_)
          (trans (names-above centred d (spacer 0# (height lbl))) (L.++-identityʳ (anchorNames d))))

names-labelBelow : ∀ lbl d → anchorNames (labelBelow lbl d) ≡ anchorNames d ++ anchorNames lbl
names-labelBelow lbl d =
  trans (names-above centred (spacer 0# (height lbl)) (aboveA centred d lbl))
        (names-above centred d lbl)

names-connectP : ∀ a pa b pb s l → Layout.anchors (connectP a pa b pb s l) ≡ Layout.anchors l
names-connectP a pa b pb s l with findAnchor a (Layout.anchors l) | findAnchor b (Layout.anchors l)
... | just _  | just _  = refl
... | just _  | nothing = refl
... | nothing | _       = refl

------------------------------------------------------------------------
-- The declared names are the anchors' names

names-fusion : ∀ d → anchorNames (LW.layout d) ≡ proj₁ (fold namesAlgebra d)
names-fusion (pure ())
names-fusion (impure (Rectangle _ _ _ , _)) = refl
names-fusion (impure (Disc _ _ , _))        = refl
names-fusion (impure (Segment _ _ _ , _))   = refl
names-fusion (impure (Text _ _ _ _ , _))    = refl
names-fusion (impure (Spacer _ _ , _))      = refl
names-fusion (impure (Raw _ _ _ , _))       = refl
names-fusion (impure (Beside al , k)) =
  trans (names-besideA al (LW.layout (k zero)) (LW.layout (k (suc zero)))) (cong₂ _++_ (names-fusion (k zero)) (names-fusion (k (suc zero))))
names-fusion (impure (Above al , k)) =
  trans (names-above al (LW.layout (k zero)) (LW.layout (k (suc zero)))) (cong₂ _++_ (names-fusion (k zero)) (names-fusion (k (suc zero))))
names-fusion (impure (Atop , k)) =
  trans (names-atop (LW.layout (k zero)) (LW.layout (k (suc zero)))) (cong₂ _++_ (names-fusion (k zero)) (names-fusion (k (suc zero))))
names-fusion (impure (LabelAbove , k)) =
  trans (names-labelAbove (LW.layout (k zero)) (LW.layout (k (suc zero)))) (cong₂ _++_ (names-fusion (k zero)) (names-fusion (k (suc zero))))
names-fusion (impure (LabelBelow , k)) =
  trans (names-labelBelow (LW.layout (k zero)) (LW.layout (k (suc zero)))) (cong₂ _++_ (names-fusion (k (suc zero))) (names-fusion (k zero)))
names-fusion (impure (Named n , k)) = cong (n ∷_) (names-fusion (k tt))
names-fusion (impure (Connect a pa b pb s , k)) =
  trans (cong (map proj₁) (names-connectP a pa b pb s (LW.layout (k tt)))) (names-fusion (k tt))

------------------------------------------------------------------------
-- A connection whose names are declared draws an arrow

just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

anchor-lookup : ∀ x as → x ∈ map proj₁ as → ∃ λ b → findAnchor x as ≡ just b
anchor-lookup x ((m , b) ∷ as) p with x ≟ m
... | yes _ = b , refl
... | no x≢m with p
...   | here x≡m  = ⊥-elim (x≢m x≡m)
...   | there p′  = anchor-lookup x as p′

-- the arrow `connectP` appends
Arrow : String → Port → String → Port → Style → Layout S → Set
Arrow a pa b pb s l =
  Σ (S × S) λ p → Σ (S × S) λ q →
    Layout.draws (connectP a pa b pb s l)
      ≡ Layout.draws l ++ arrow (proj₁ p) (proj₂ p) (proj₁ q) (proj₂ q) s ∷ []

connectP-arrow : ∀ a pa b pb s l → a ∈ anchorNames l → b ∈ anchorNames l → Arrow a pa b pb s l
connectP-arrow a pa b pb s l ia ib
  with findAnchor a (Layout.anchors l) in ea | findAnchor b (Layout.anchors l) in eb
... | just ba | just bb = portPoint pa ba , portPoint pb bb , refl
... | just ba | nothing = ⊥-elim (just≢nothing (trans (sym (proj₂ (anchor-lookup b _ ib))) eb))
... | nothing | _       = ⊥-elim (just≢nothing (trans (sym (proj₂ (anchor-lookup a _ ia))) ea))

------------------------------------------------------------------------
-- Soundness

-- every `connect` node, laid out over its own child, appends an arrow
Draws : Dia S → Set
Draws (pure ())
Draws (impure (Rectangle _ _ _ , _)) = ⊤
Draws (impure (Disc _ _ , _))        = ⊤
Draws (impure (Segment _ _ _ , _))   = ⊤
Draws (impure (Text _ _ _ _ , _))    = ⊤
Draws (impure (Spacer _ _ , _))      = ⊤
Draws (impure (Raw _ _ _ , _))       = ⊤
Draws (impure (Beside _ , k))        = (i : Fin 2) → Draws (k i)
Draws (impure (Above _ , k))         = (i : Fin 2) → Draws (k i)
Draws (impure (Atop , k))            = (i : Fin 2) → Draws (k i)
Draws (impure (LabelAbove , k))      = (i : Fin 2) → Draws (k i)
Draws (impure (LabelBelow , k))      = (i : Fin 2) → Draws (k i)
Draws (impure (Named _ , k))         = Draws (k tt)
Draws (impure (Connect a pa b pb s , k)) =
  Draws (k tt) × Arrow a pa b pb s (LW.layout (k tt))

cons≢nil : ∀ {A : Set} {x : A} {xs} → x ∷ xs ≡ [] → ⊥
cons≢nil ()

not-false : ∀ {x} → not x ≡ false → x ≡ true
not-false {true}  _ = refl
not-false {false} ()

filterᵇ-∷ : ∀ (p : String → Bool) x xs → filterᵇ p (x ∷ xs) ≡ [] → p x ≡ false × filterᵇ p xs ≡ []
filterᵇ-∷ p x xs h with p x in eq
... | false = refl , h
... | true  = ⊥-elim (cons≢nil h)

-- both of the connected names are declared when none is reported
resolved : ∀ a b d →
  filterᵇ (λ r → not (member r d)) (a ∷ b ∷ []) ≡ [] → member a d ≡ true × member b d ≡ true
resolved a b d h with filterᵇ-∷ (λ r → not (member r d)) a (b ∷ []) h
... | pa , h′ with filterᵇ-∷ (λ r → not (member r d)) b [] h′
... | pb , _ = not-false pa , not-false pb

member-∈ : ∀ x xs → member x xs ≡ true → x ∈ xs
member-∈ x (y ∷ ys) h with x ≟ y
... | yes x≡y = here x≡y
... | no _    = there (member-∈ x ys h)

fin2 : ∀ {P : Fin 2 → Set} → P zero → P (suc zero) → ∀ i → P i
fin2 p q zero          = p
fin2 p q (suc zero)    = q

++ˡ : ∀ {xs ys : List String} → xs ++ ys ≡ [] → xs ≡ []
++ˡ {xs} {ys} = L.++-conicalˡ xs ys

++ʳ : ∀ {xs ys : List String} → xs ++ ys ≡ [] → ys ≡ []
++ʳ {xs} {ys} = L.++-conicalʳ xs ys

soundness : ∀ d → dangling d ≡ [] → Draws d
soundness (pure ())
soundness (impure (Rectangle _ _ _ , _)) _ = tt
soundness (impure (Disc _ _ , _)) _        = tt
soundness (impure (Segment _ _ _ , _)) _   = tt
soundness (impure (Text _ _ _ _ , _)) _    = tt
soundness (impure (Spacer _ _ , _)) _      = tt
soundness (impure (Raw _ _ _ , _)) _       = tt
soundness (impure (Beside _ , k)) h = fin2 (soundness (k zero) (++ˡ h)) (soundness (k (suc zero)) (++ʳ h))
soundness (impure (Above _ , k)) h = fin2 (soundness (k zero) (++ˡ h)) (soundness (k (suc zero)) (++ʳ h))
soundness (impure (Atop , k)) h = fin2 (soundness (k zero) (++ˡ h)) (soundness (k (suc zero)) (++ʳ h))
soundness (impure (LabelAbove , k)) h = fin2 (soundness (k zero) (++ˡ h)) (soundness (k (suc zero)) (++ʳ h))
soundness (impure (LabelBelow , k)) h = fin2 (soundness (k zero) (++ʳ h)) (soundness (k (suc zero)) (++ˡ h))
soundness (impure (Named _ , k)) h = soundness (k tt) h
soundness (impure (Connect a pa b pb s , k)) h =
  soundness (k tt) (L.++-conicalˡ _ _ h)
  , connectP-arrow a pa b pb s (LW.layout (k tt))
      (subst (a ∈_) (sym (names-fusion (k tt))) (member-∈ a _ (proj₁ r)))
      (subst (b ∈_) (sym (names-fusion (k tt))) (member-∈ b _ (proj₂ r)))
  where r = resolved a b (proj₁ (fold namesAlgebra (k tt))) (L.++-conicalʳ _ _ h)
