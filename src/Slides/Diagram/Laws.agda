{-# OPTIONS --safe --without-K #-}

-- Laws of placement over a `Space`.
--
-- `size d` is a fold of its own that never builds a drawing: beside adds widths and joins
-- heights, above the reverse, atop joins both.
--
--     size (beside a b) = (wa + wb , ha ⊔ hb)      size (above a b) = (wa ⊔ wb , ha + hb)
--
--   * `size-layout`: the frame of `layout d` is `size d`, so sizes of connectives can be
--     reasoned about without layouts (`size-beside-assoc`, `size-above-assoc`,
--     `size-atop-assoc`, `size-atop-comm`, `size-labels`, `size-disc-ellipse`, `size-polygon`);
--   * translation is an action on layouts (`shift-zero`, `shift-shift`);
--   * annotations are invisible: `size-named`, `size-connect`, `named-frame`.
--
-- Associativity of beside and above: `Assoc`; of atop, and commutativity up to the order of
-- the drawings: `Commute`; non-negative frames and the unit `spacer 0 0`: `Valid`.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Laws {S : Set} (Sp : Space S) where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeSemigroup; CommutativeMonoid)
import Algebra.Construct.DirectProduct as DP
import Relation.Binary.PropositionalEquality.Properties as ≡P
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Container.Interpret.Plain using (Handler; pfold; pfold-rel)
open import Slides.Diagram.Draw
open import Slides.Diagram.Overlay using (Overlays)
import Data.List.Properties as ListP
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Slides.Diagram.Syntax hiding (ellipse)
import Slides.Diagram.Syntax as D
open Space Sp
import Slides.Diagram.Place Sp as P
open P using (dbl)
open import Slides.Diagram.Layout Sp using (layoutH; layout)

-- Size is a fold into envelope monoids (Yorgey): the sizes of the connectives are products of the
-- semigroups (S,+) and (S,⊔), so their laws are the semigroup laws

sumSG joinSG : CommutativeSemigroup 0ℓ 0ℓ
sumSG  = CommutativeMonoid.commutativeSemigroup commutativeMonoid
joinSG = record
  { Carrier = S ; _≈_ = _≡_ ; _∙_ = _⊔_
  ; isCommutativeSemigroup = record
      { isSemigroup = record { isMagma = record { isEquivalence = ≡P.isEquivalence ; ∙-cong = cong₂ _⊔_ } ; assoc = ⊔-assoc }
      ; comm = ⊔-comm } }

-- beside: widths add, heights join; above the reverse; atop joins both
besideSG aboveSG atopSG : CommutativeSemigroup 0ℓ 0ℓ
besideSG = DP.commutativeSemigroup sumSG joinSG
aboveSG  = DP.commutativeSemigroup joinSG sumSG
atopSG   = DP.commutativeSemigroup joinSG joinSG

private
  module B = CommutativeSemigroup besideSG
  module A = CommutativeSemigroup aboveSG
  module T = CommutativeSemigroup atopSG

-- the size of the connective is the product operation
_∙ᵇ_ _∙ᵃ_ _∙ᵗ_ : S × S → S × S → S × S
_∙ᵇ_ = B._∙_
_∙ᵃ_ = A._∙_
_∙ᵗ_ = T._∙_

sizeH : Handler (DiagramC S) (S × S)
sizeH (Rectangle w h _) k = w , h
sizeH (Segment w h _)   k = w , h
sizeH (Disc r _)        k = dbl r , dbl r
sizeH (Ellipse a b _)   k = dbl a , dbl b
sizeH (Polyline _ ps _) k = P.extent (map proj₁ ps) , P.extent (map proj₂ ps)
sizeH (Text w h _ _ _)  k = w , h
sizeH (Path w h _ _)    k = w , h
sizeH (Spacer w h)      k = w , h
sizeH (Beside _)        k = k zero ∙ᵇ k (suc zero)
sizeH (Above _)         k = k zero ∙ᵃ k (suc zero)
sizeH Atop              k = k zero ∙ᵗ k (suc zero)
sizeH LabelAbove        k = proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) + (proj₂ (k (suc zero)) + proj₂ (k zero))
sizeH LabelBelow        k = proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) + (proj₂ (k (suc zero)) + proj₂ (k zero))
sizeH (Place w h _ _)   k = w , h
sizeH (Overlay w h)     k = w , h
sizeH (Named _)         k = k tt
sizeH (Connect _ _ _ _ _) k = k tt

size : Dia S → S × S
size = pfold (DiagramC S) sizeH (λ ())

-- the frame of a layout is the size of its diagram
size-layout : ∀ t → (P.width (layout t) , P.height (layout t)) ≡ size t
size-layout = pfold-rel (λ l z → (P.width l , P.height l) ≡ z) hom (λ ())
  where
    hom : ∀ o k k′ → (∀ q → (P.width (k q) , P.height (k q)) ≡ k′ q) →
          (P.width (layoutH o k) , P.height (layoutH o k)) ≡ sizeH o k′
    hom (Rectangle _ _ _) k k′ e = refl
    hom (Segment _ _ _)   k k′ e = refl
    hom (Disc _ _)        k k′ e = refl
    hom (Ellipse _ _ _)   k k′ e = refl
    hom (Polyline _ _ _)  k k′ e = refl
    hom (Text _ _ _ _ _)  k k′ e = refl
    hom (Path _ _ _ _)    k k′ e = refl
    hom (Spacer _ _)      k k′ e = refl
    hom (Beside _)        k k′ e = cong₂ _∙ᵇ_ (e zero) (e (suc zero))
    hom (Above _)         k k′ e = cong₂ _∙ᵃ_ (e zero) (e (suc zero))
    hom Atop              k k′ e = cong₂ _∙ᵗ_ (e zero) (e (suc zero))
    hom LabelAbove        k k′ e = cong₂ (λ a b → proj₁ a ⊔ proj₁ b , proj₂ a + (proj₂ b + proj₂ a)) (e zero) (e (suc zero))
    hom LabelBelow        k k′ e = cong₂ (λ a b → proj₁ a ⊔ proj₁ b , proj₂ a + (proj₂ b + proj₂ a)) (e zero) (e (suc zero))
    hom (Place _ _ _ _)   k k′ e = refl
    hom (Overlay _ _)     k k′ e = refl
    hom (Named _)         k k′ e = trans (cong₂ _,_ refl refl) (e tt)
    hom (Connect _ _ _ _ _) k k′ e = e tt

-- Layouts overlay in the join of their frames, the drawings and anchors concatenating
ovl : Layout S → Layout S → Layout S
ovl a b = P.overlay (P.width a ⊔ P.width b) (P.height a ⊔ P.height b) a b

layoutOverlay : Overlays (Layout S)
layoutOverlay = record { _⊙_ = ovl ; ⊙-assoc = assoc }
  where
    assoc : ∀ a b c → ovl (ovl a b) c ≡ ovl a (ovl b c)
    assoc (mkLayout wa ha da aa) (mkLayout wb hb db ab) (mkLayout wc hc dc ac)
      = cong₂ (λ (w , h) (d , a) → mkLayout w h d a) (cong₂ _,_ (⊔-assoc wa wb wc) (⊔-assoc ha hb hc))
                                                       (cong₂ _,_ (ListP.++-assoc da db dc) (ListP.++-assoc aa ab ac))

-- the monoid laws of the envelope semigroups, as laws of the sizes
size-beside-assoc : ∀ a b c → size (beside (beside a b) c) ≡ size (beside a (beside b c))
size-beside-assoc a b c = uncurry (cong₂ _,_) (B.assoc (size a) (size b) (size c))

size-above-assoc : ∀ a b c → size (above (above a b) c) ≡ size (above a (above b c))
size-above-assoc a b c = uncurry (cong₂ _,_) (A.assoc (size a) (size b) (size c))

size-atop-assoc : ∀ a b c → size (atop (atop a b) c) ≡ size (atop a (atop b c))
size-atop-assoc a b c = uncurry (cong₂ _,_) (T.assoc (size a) (size b) (size c))

size-atop-comm : ∀ a b → size (atop a b) ≡ size (atop b a)
size-atop-comm a b = uncurry (cong₂ _,_) (T.comm (size a) (size b))

-- a caption above or below takes the same room
size-labels : ∀ l d → size (labelAbove l d) ≡ size (labelBelow l d)
size-labels l d = refl

-- Ellipses and polylines.  A disc is the ellipse with equal radii; a polygon is the polyline with
-- the same points (closing changes the ink, not the frame); the frame of a polyline is the extent
-- of its points from the origin (no points, no extent) and reaches every point.
size-ellipse : ∀ a b s → size (D.ellipse a b s) ≡ (dbl a , dbl b)
size-ellipse a b s = refl

size-disc-ellipse : ∀ r s → size (disc r s) ≡ size (D.ellipse r r s)
size-disc-ellipse r s = refl

size-polyline-nil : ∀ s → size (polyline [] s) ≡ (0# , 0#)
size-polyline-nil s = refl

size-polyline-cons : ∀ x y ps s → size (polyline ((x , y) ∷ ps) s) ≡ (x ⊔ proj₁ (size (polyline ps s)) , y ⊔ proj₂ (size (polyline ps s)))
size-polyline-cons x y ps s = refl

size-polygon : ∀ ps s → size (polygon ps s) ≡ size (polyline ps s)
size-polygon ps s = refl

extent-ub : ∀ {x xs} → x ∈ xs → x ≤ P.extent xs
extent-ub (here refl) = ⊔-ub₁ _ _
extent-ub (there m)   = ≤-trans (extent-ub m) (⊔-ub₂ _ _)

polyline-reaches : ∀ p ps s → p ∈ ps →
  proj₁ p ≤ proj₁ (size (polyline ps s)) × proj₂ p ≤ proj₂ (size (polyline ps s))
polyline-reaches p ps s m = extent-ub (∈-map⁺ proj₁ m) , extent-ub (∈-map⁺ proj₂ m)

-- annotations are invisible to size
size-named : ∀ n d → size (named n d) ≡ size d
size-named n d = refl

size-connect : ∀ a pa b pb s d → size (connectP a pa b pb s d) ≡ size d
size-connect a pa b pb s d = refl

-- Translation is an action

-- an action of the translations (S×S, ⊕) on a type: shifting by nothing does nothing, and
-- shifting twice is shifting by the sum.  Drawings, anchors, lists of them, and layouts act.
infixl 6 _⊕_
_⊕_ : S × S → S × S → S × S
p ⊕ o = proj₁ p + proj₁ o , proj₂ p + proj₂ o

record Action (X : Set) : Set where
  field
    act      : S × S → X → X
    act-zero : ∀ x → act (0# , 0#) x ≡ x
    act-⊕    : ∀ p o x → act o (act p x) ≡ act (p ⊕ o) x

listAct : ∀ {X} → Action X → Action (List X)
listAct A = record
  { act = λ p → map (act p)
  ; act-zero = λ xs → trans (ListP.map-cong act-zero xs) (ListP.map-id xs)
  ; act-⊕ = λ p o xs → trans (sym (ListP.map-∘ xs)) (ListP.map-cong (act-⊕ p o) xs) }
  where open Action A

_×ᵃ_ : ∀ {X Y} → Action X → Action Y → Action (X × Y)
A ×ᵃ B = record
  { act = λ p (x , y) → Aˣ.act p x , Bˣ.act p y
  ; act-zero = λ (x , y) → cong₂ _,_ (Aˣ.act-zero x) (Bˣ.act-zero y)
  ; act-⊕ = λ p o (x , y) → cong₂ _,_ (Aˣ.act-⊕ p o x) (Bˣ.act-⊕ p o y) }
  where module Aˣ = Action A; module Bˣ = Action B

drawAct : Action (Draw S)
drawAct = record { act = λ p → P.shiftDraw (proj₁ p) (proj₂ p) ; act-zero = zero′ ; act-⊕ = λ p o → shift′ (proj₁ p) (proj₂ p) (proj₁ o) (proj₂ o) }
  where
    zero′ : ∀ d → P.shiftDraw 0# 0# d ≡ d
    zero′ (rect x y w h s)   = cong₂ (λ x y → rect x y w h s) (+-idʳ x) (+-idʳ y)
    zero′ (circle x y r s)   = cong₂ (λ x y → circle x y r s) (+-idʳ x) (+-idʳ y)
    zero′ (ellipse x y a b s) = cong₂ (λ x y → ellipse x y a b s) (+-idʳ x) (+-idʳ y)
    zero′ (poly c ps s)      = cong (λ qs → poly c qs s) (trans (ListP.map-cong (λ p → cong₂ _,_ (+-idʳ (proj₁ p)) (+-idʳ (proj₂ p))) ps) (ListP.map-id ps))
    zero′ (line a b c d s)   = cong₂ (λ (a , b) (c , d) → line a b c d s) (cong₂ _,_ (+-idʳ a) (+-idʳ b)) (cong₂ _,_ (+-idʳ c) (+-idʳ d))
    zero′ (arrow a b c d s)  = cong₂ (λ (a , b) (c , d) → arrow a b c d s) (cong₂ _,_ (+-idʳ a) (+-idʳ b)) (cong₂ _,_ (+-idʳ c) (+-idʳ d))
    zero′ (label x y n t s)  = cong₂ (λ x y → label x y n t s) (+-idʳ x) (+-idʳ y)
    zero′ (path x y d s)     = cong₂ (λ x y → Draw.path x y d s) (+-idʳ x) (+-idʳ y)
    shift′ : ∀ c d a b e → P.shiftDraw a b (P.shiftDraw c d e) ≡ P.shiftDraw (c + a) (d + b) e
    shift′ c d a b (rect x y w h s)   = cong₂ (λ x y → rect x y w h s) (+-assoc x c a) (+-assoc y d b)
    shift′ c d a b (circle x y r s)   = cong₂ (λ x y → circle x y r s) (+-assoc x c a) (+-assoc y d b)
    shift′ c d a b (ellipse x y p q s) = cong₂ (λ x y → ellipse x y p q s) (+-assoc x c a) (+-assoc y d b)
    shift′ c d a b (poly cl ps s)     = cong (λ qs → poly cl qs s) (trans (sym (ListP.map-∘ ps)) (ListP.map-cong (λ p → cong₂ _,_ (+-assoc (proj₁ p) c a) (+-assoc (proj₂ p) d b)) ps))
    shift′ c d a b (line x y z u s)   = cong₂ (λ (x , y) (z , u) → line x y z u s) (cong₂ _,_ (+-assoc x c a) (+-assoc y d b)) (cong₂ _,_ (+-assoc z c a) (+-assoc u d b))
    shift′ c d a b (arrow x y z u s)  = cong₂ (λ (x , y) (z , u) → arrow x y z u s) (cong₂ _,_ (+-assoc x c a) (+-assoc y d b)) (cong₂ _,_ (+-assoc z c a) (+-assoc u d b))
    shift′ c d a b (label x y n t s)  = cong₂ (λ x y → label x y n t s) (+-assoc x c a) (+-assoc y d b)
    shift′ c d a b (path x y e s)     = cong₂ (λ x y → Draw.path x y e s) (+-assoc x c a) (+-assoc y d b)

anchorAct : Action (String × Box S)
anchorAct = record { act = λ p → P.shiftAnchor (proj₁ p) (proj₂ p) ; act-zero = zero′ ; act-⊕ = λ p o → shift′ (proj₁ p) (proj₂ p) (proj₁ o) (proj₂ o) }
  where
    zero′ : ∀ x → P.shiftAnchor 0# 0# x ≡ x
    zero′ (n , box l t w h) = cong₂ (λ l t → n , box l t w h) (+-idʳ l) (+-idʳ t)
    shift′ : ∀ c d a b x → P.shiftAnchor a b (P.shiftAnchor c d x) ≡ P.shiftAnchor (c + a) (d + b) x
    shift′ c d a b (n , box l t w h) = cong₂ (λ l t → n , box l t w h) (+-assoc l c a) (+-assoc t d b)

-- what a layout holds besides its frame: the drawings and the anchors
Items : Set
Items = List (Draw S) × List (String × Box S)

itemsAct : Action Items
itemsAct = listAct drawAct ×ᵃ listAct anchorAct

items : Layout S → Items
items l = Layout.draws l , Layout.anchors l

-- shifting a layout (inside its own frame) is the action on its items
shift-items : ∀ dx dy l → items (P.shift dx dy l) ≡ Action.act itemsAct (dx , dy) (items l)
shift-items dx dy l = refl

shift-zero : ∀ l → P.shift 0# 0# l ≡ l
shift-zero (mkLayout w h ds as) = cong (λ (d , a) → mkLayout w h d a) (Action.act-zero itemsAct (ds , as))

-- naming changes nothing visible: same frame, same drawings
named-frame : ∀ n l → (P.width (P.named n l) , P.height (P.named n l) , Layout.draws (P.named n l))
                      ≡ (P.width l , P.height l , Layout.draws l)
named-frame n l = refl
