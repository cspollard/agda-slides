{-# OPTIONS --safe --without-K #-}

-- `Slides.Diagram.Names.dangling` is sound: if it reports nothing, every `connect` in the
-- diagram draws an arrow (none is silently dropped).  Two facts:
--
--   * `names-fusion`: the declared names of the usage fold are the names of the anchors of the
--     layout, in order (placement keeps the anchors of its children in order);
--   * `soundness`: `dangling d ≡ []` implies `Draws d`: each `connect`, laid out over its own
--     child, appends one arrow.
--
--   dangling d ≡ []  ──soundness──▶  Draws d
--        │ names-fusion                  ▲ connectP-arrow (both names are anchors)
--        └── declared d ≡ anchor names of (layout d) ─┘
--
-- Nothing is asked of the scalar beyond `Space`.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Names.Soundness {S : Set} (Sp : Space S) where

open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
import Data.List.Properties as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Container.Interpret.Plain using (pfold-rel)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry using (Port; centred)
open import Slides.Diagram.Syntax
open import Slides.Diagram.Names
import Slides.Diagram.Place Sp as P
open Space Sp using (0#; _-_; _⊔_; _+_)
open import Slides.Diagram.Layout Sp using (layoutH; layout)

anchorNames : Layout S → List String
anchorNames l = map proj₁ (Layout.anchors l)

-- Names survive the placement operations

names-inFrame : ∀ w h dx dy l → anchorNames (P.inFrame w h dx dy l) ≡ anchorNames l
names-inFrame w h dx dy (mkLayout _ _ ds as) = go as
  where go : ∀ as → map proj₁ (map (P.shiftAnchor dx dy) as) ≡ map proj₁ as
        go []             = refl
        go ((n , b) ∷ as) = cong (n ∷_) (go as)

names-++ : ∀ (a b : List (String × Box S)) → map proj₁ (a ++ b) ≡ map proj₁ a ++ map proj₁ b
names-++ a b = L.map-++ proj₁ a b

names-placed : ∀ pl a b → anchorNames (P.placed pl a b) ≡ anchorNames a ++ anchorNames b
names-placed (P.placement (w , h) (px , py) (qx , qy)) a b =
  trans (names-++ (Layout.anchors (P.inFrame w h px py a)) (Layout.anchors (P.inFrame w h qx qy b)))
        (cong₂ _++_ (names-inFrame w h px py a) (names-inFrame w h qx qy b))

-- each binary connective places its children (`Slides.Diagram.Place`), the first child first
names-besideA : ∀ al a b → anchorNames (P.besideA al a b) ≡ anchorNames a ++ anchorNames b
names-besideA al a b = names-placed (P.besideP al (P.frameOf a) (P.frameOf b)) a b

names-aboveA : ∀ al a b → anchorNames (P.aboveA al a b) ≡ anchorNames a ++ anchorNames b
names-aboveA al a b = names-placed (P.aboveP al (P.frameOf a) (P.frameOf b)) a b

names-atop : ∀ a b → anchorNames (P.atop a b) ≡ anchorNames a ++ anchorNames b
names-atop a b = names-placed (P.atopP (P.frameOf a) (P.frameOf b)) a b

names-labelAbove : ∀ l d → anchorNames (P.labelAbove l d) ≡ anchorNames l ++ anchorNames d
names-labelAbove l d = names-placed (P.labelAboveP (P.frameOf l) (P.frameOf d)) l d

names-labelBelow : ∀ l d → anchorNames (P.labelBelow l d) ≡ anchorNames d ++ anchorNames l
names-labelBelow l d = names-placed (P.labelBelowP (P.frameOf l) (P.frameOf d)) d l

names-fusion : ∀ t → anchorNames (layout t) ≡ declared t
names-fusion = pfold-rel (λ l u → anchorNames l ≡ proj₁ u) hom (λ ())
  where
    two : ∀ {a b c d : List String} → a ≡ c → b ≡ d → a ++ b ≡ c ++ d
    two = cong₂ _++_
    hom : ∀ (o : Op S) (L : arity (proj₁ o) → Layout S) (U : arity (proj₁ o) → Usage) → (∀ q → anchorNames (L q) ≡ proj₁ (U q)) → anchorNames (layoutH o L) ≡ proj₁ (usageH o U)
    hom (Rectangle _ _ _) L U e = refl
    hom (Segment _ _ _)   L U e = refl
    hom (Disc _ _)        L U e = refl
    hom (Ellipse _ _ _)   L U e = refl
    hom (Polyline _ _ _)  L U e = refl
    hom (Text _ _ _ _ _)  L U e = refl
    hom (Path _ _ _ _)    L U e = refl
    hom (Spacer _ _)      L U e = refl
    hom (Beside al)       L U e = trans (names-besideA al (L zero) (L (suc zero))) (two (e zero) (e (suc zero)))
    hom (Above al)        L U e = trans (names-aboveA al (L zero) (L (suc zero))) (two (e zero) (e (suc zero)))
    hom Atop              L U e = trans (names-atop (L zero) (L (suc zero))) (two (e zero) (e (suc zero)))
    hom LabelAbove        L U e = trans (names-labelAbove (L zero) (L (suc zero))) (two (e zero) (e (suc zero)))
    hom LabelBelow        L U e = trans (names-labelBelow (L zero) (L (suc zero))) (two (e (suc zero)) (e zero))
    hom (Place w h x y)   L U e = trans (names-inFrame w h _ _ (L tt)) (e tt)
    hom (Overlay _ _)     L U e = trans (names-++ (Layout.anchors (L zero)) (Layout.anchors (L (suc zero)))) (two (e zero) (e (suc zero)))
    hom (Named n)         L U e = cong (n ∷_) (e tt)
    hom (Connect _ _ _ _ _) L U e = e tt

-- A connection whose names are declared draws an arrow

just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

anchor-lookup : ∀ x as → x ∈ map proj₁ as → ∃ λ b → P.findAnchor x as ≡ just b
anchor-lookup x ((m , b) ∷ as) p with x ≟ m
... | yes _ = b , refl
... | no x≢m with p
...   | here x≡m  = ⊥-elim (x≢m x≡m)
...   | there p′  = anchor-lookup x as p′

-- the arrow `connectP` appends
Arrow : String → Port → String → Port → Style → Layout S → Set
Arrow a pa b pb s l =
  Σ (S × S) λ p → Σ (S × S) λ q →
    Layout.draws (P.connectP a pa b pb s l) ≡ Layout.draws l ++ arrow (proj₁ p) (proj₂ p) (proj₁ q) (proj₂ q) s ∷ []

connectP-arrow : ∀ a pa b pb s l → a ∈ anchorNames l → b ∈ anchorNames l → Arrow a pa b pb s l
connectP-arrow a pa b pb s (mkLayout w h ds as) ia ib
  with anchor-lookup a as ia | anchor-lookup b as ib
... | ba , fa | bb , fb rewrite fa | fb = P.portPoint pa ba , P.portPoint pb bb , refl

-- the anchors of a connection are its child's: a connection never declares a name
connectP-anchors : ∀ a pa b pb s l → Layout.anchors (P.connectP a pa b pb s l) ≡ Layout.anchors l
connectP-anchors a pa b pb s l = refl

-- Soundness

-- every `connect` node, laid out over its own child, appends an arrow
Draws : Dia S → Set
Draws (pure ())
Draws (impure (Connect a pa b pb s , k)) = Draws (k tt) × Arrow a pa b pb s (layout (k tt))
Draws (impure (o , k))                   = ∀ q → Draws (k q)

private
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
  resolved : ∀ a b d → filterᵇ (λ r → not (member r d)) (a ∷ b ∷ []) ≡ [] → member a d ≡ true × member b d ≡ true
  resolved a b d h with filterᵇ-∷ (λ r → not (member r d)) a (b ∷ []) h
  ... | pa , h′ with filterᵇ-∷ (λ r → not (member r d)) b [] h′
  ... | pb , _ = not-false pa , not-false pb

  member-∈ : ∀ x xs → member x xs ≡ true → x ∈ xs
  member-∈ x (y ∷ ys) h with x ≟ y
  ... | yes x≡y = here x≡y
  ... | no _    = there (member-∈ x ys h)

  fin2 : ∀ {P : Fin 2 → Set} → P zero → P (suc zero) → ∀ i → P i
  fin2 p q zero       = p
  fin2 p q (suc zero) = q

  ++ˡ : ∀ {xs ys : List String} → xs ++ ys ≡ [] → xs ≡ []
  ++ˡ {xs} {ys} = L.++-conicalˡ xs ys

  ++ʳ : ∀ {xs ys : List String} → xs ++ ys ≡ [] → ys ≡ []
  ++ʳ {xs} {ys} = L.++-conicalʳ xs ys

  -- a command with nothing dangling has nothing dangling in any child
  clean : ∀ (o : Op S) (U : arity (proj₁ o) → Usage) → proj₂ (usageH o U) ≡ [] → ∀ q → proj₂ (U q) ≡ []
  clean (Rectangle _ _ _) U h ()
  clean (Segment _ _ _)   U h ()
  clean (Disc _ _)        U h ()
  clean (Ellipse _ _ _)   U h ()
  clean (Polyline _ _ _)  U h ()
  clean (Text _ _ _ _ _)  U h ()
  clean (Path _ _ _ _)    U h ()
  clean (Spacer _ _)      U h ()
  clean (Beside _)        U h = fin2 (++ˡ h) (++ʳ h)
  clean (Above _)         U h = fin2 (++ˡ h) (++ʳ h)
  clean Atop              U h = fin2 (++ˡ h) (++ʳ h)
  clean LabelAbove        U h = fin2 (++ˡ h) (++ʳ h)
  clean LabelBelow        U h = fin2 (++ʳ h) (++ˡ h)
  clean (Place _ _ _ _)   U h = λ _ → h
  clean (Overlay _ _)     U h = fin2 (++ˡ h) (++ʳ h)
  clean (Named _)         U h = λ _ → h
  clean (Connect _ _ _ _ _) U h = λ _ → L.++-conicalˡ _ _ h

soundness : ∀ t → dangling t ≡ [] → Draws t
soundness (pure ())
soundness (impure (Connect a pa b pb s , k)) h =
  soundness (k tt) (L.++-conicalˡ _ _ h)
  , connectP-arrow a pa b pb s (layout (k tt))
      (subst (a ∈_) (sym (names-fusion (k tt))) (member-∈ a _ (proj₁ r)))
      (subst (b ∈_) (sym (names-fusion (k tt))) (member-∈ b _ (proj₂ r)))
  where r = resolved a b (declared (k tt)) (L.++-conicalʳ _ _ h)
soundness (impure (Rectangle _ _ _ , k)) h = λ ()
soundness (impure (Segment _ _ _ , k)) h = λ ()
soundness (impure (Disc _ _ , k)) h = λ ()
soundness (impure (Ellipse _ _ _ , k)) h = λ ()
soundness (impure (Polyline _ _ _ , k)) h = λ ()
soundness (impure (Text _ _ _ _ _ , k)) h = λ ()
soundness (impure (Path _ _ _ _ , k)) h = λ ()
soundness (impure (Spacer _ _ , k)) h = λ ()
soundness (impure (Beside al , k)) h = λ q → soundness (k q) (clean (Beside al) (λ q → usage (k q)) h q)
soundness (impure (Above al , k)) h = λ q → soundness (k q) (clean (Above al) (λ q → usage (k q)) h q)
soundness (impure (Atop , k)) h = λ q → soundness (k q) (clean Atop (λ q → usage (k q)) h q)
soundness (impure (LabelAbove , k)) h = λ q → soundness (k q) (clean LabelAbove (λ q → usage (k q)) h q)
soundness (impure (LabelBelow , k)) h = λ q → soundness (k q) (clean LabelBelow (λ q → usage (k q)) h q)
soundness (impure (Place w ht x y , k)) h = λ q → soundness (k q) (clean (Place w ht x y) (λ q → usage (k q)) h q)
soundness (impure (Overlay w ht , k)) h = λ q → soundness (k q) (clean (Overlay w ht) (λ q → usage (k q)) h q)
soundness (impure (Named n , k)) h = λ q → soundness (k q) (clean (Named n) (λ q → usage (k q)) h q)
