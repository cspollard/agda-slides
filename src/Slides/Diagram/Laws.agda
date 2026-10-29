{-# OPTIONS --safe --without-K #-}

-- Laws of placement over a `Space`.
--
--   * size is synthesised: the frame of `layout d` is `size d`, a fold of its own that
--     never builds a drawing (`size-layout`); so the connectives' sizes can be reasoned about
--     without layouts (`size-beside-assoc`, `size-above-assoc`, `size-atop-assoc`,
--     `size-atop-comm`, `size-labels`);
--   * translation is an action on layouts: `shift 0 0 l ≡ l`, `shift a b (shift c d l) ≡
--     shift (c + a) (d + b) l` (`shift-zero`, `shift-shift`);
--   * annotations do not change a layout's frame or drawings (`named-frame`).
--
-- Associativity of beside and above is `Slides.Diagram.Assoc`; validity (non-negative frames) and the
-- units of the empty diagram, which hold for non-negative sizes only, are `Slides.Diagram.Valid`.  Not
-- claimed (the legacy proved it over a ring, `Place/Properties/Commute`): commutativity of `atop` up to
-- a permutation of the drawings.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Laws {S : Set} (Sp : Space S) where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Container.Interpret.Plain using (Handler; pfold; pfold-rel)
open import Slides.Diagram.Draw
open import Slides.Diagram.Overlay using (Overlays)
import Data.List.Properties as ListP
open import Slides.Diagram.Syntax
open Space Sp
import Slides.Diagram.Place Sp as P
open P using (dbl)
open import Slides.Diagram.Layout Sp using (layoutH; layout)

------------------------------------------------------------------------
-- Size is a fold

sizeH : Handler (DiagramC S) (S × S)
sizeH (Rectangle w h _) k = w , h
sizeH (Segment w h _)   k = w , h
sizeH (Disc r _)        k = dbl r , dbl r
sizeH (Text w h _ _ _)  k = w , h
sizeH (Path w h _ _)    k = w , h
sizeH (Spacer w h)      k = w , h
sizeH (Beside _)        k = proj₁ (k zero) + proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
sizeH (Above _)         k = proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) + proj₂ (k (suc zero))
sizeH Atop              k = proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
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
    hom (Text _ _ _ _ _)  k k′ e = refl
    hom (Path _ _ _ _)    k k′ e = refl
    hom (Spacer _ _)      k k′ e = refl
    hom (Beside _)        k k′ e rewrite sym (e zero) | sym (e (suc zero)) = refl
    hom (Above _)         k k′ e rewrite sym (e zero) | sym (e (suc zero)) = refl
    hom Atop              k k′ e rewrite sym (e zero) | sym (e (suc zero)) = refl
    hom LabelAbove        k k′ e rewrite sym (e zero) | sym (e (suc zero)) = refl
    hom LabelBelow        k k′ e rewrite sym (e zero) | sym (e (suc zero)) = refl
    hom (Place _ _ _ _)   k k′ e = refl
    hom (Overlay _ _)     k k′ e = refl
    hom (Named _)         k k′ e = trans (cong₂ _,_ refl refl) (e tt)
    hom (Connect _ _ _ _ _) k k′ e = e tt

------------------------------------------------------------------------
-- Sizes of connectives, from the laws of `+` and `⊔`

⊔-comm : ∀ a b → a ⊔ b ≡ b ⊔ a
⊔-comm a b = ≤-antisym (⊔-lub (⊔-ub₂ b a) (⊔-ub₁ b a)) (⊔-lub (⊔-ub₂ a b) (⊔-ub₁ a b))

⊔-assoc : ∀ a b c → (a ⊔ b) ⊔ c ≡ a ⊔ (b ⊔ c)
⊔-assoc a b c = ≤-antisym
  (⊔-lub (⊔-lub (⊔-ub₁ a _) (≤-trans (⊔-ub₁ b c) (⊔-ub₂ a _))) (≤-trans (⊔-ub₂ b c) (⊔-ub₂ a _)))
  (⊔-lub (≤-trans (⊔-ub₁ a b) (⊔-ub₁ _ c)) (⊔-lub (≤-trans (⊔-ub₂ a b) (⊔-ub₁ _ c)) (⊔-ub₂ _ c)))

-- Layouts overlay in the join of their frames, the drawings and anchors concatenating
ovl : Layout S → Layout S → Layout S
ovl a b = P.overlay (P.width a ⊔ P.width b) (P.height a ⊔ P.height b) a b

layoutOverlay : Overlays (Layout S)
layoutOverlay = record { _⊙_ = ovl ; ⊙-assoc = assoc }
  where
    assoc : ∀ a b c → ovl (ovl a b) c ≡ ovl a (ovl b c)
    assoc (mkLayout wa ha da aa) (mkLayout wb hb db ab) (mkLayout wc hc dc ac)
      rewrite ⊔-assoc wa wb wc | ⊔-assoc ha hb hc | ListP.++-assoc da db dc | ListP.++-assoc aa ab ac = refl

size-beside-assoc : ∀ a b c → size (beside (beside a b) c) ≡ size (beside a (beside b c))
size-beside-assoc a b c =
  cong₂ _,_ (+-assoc _ _ _) (⊔-assoc _ _ _)

size-above-assoc : ∀ a b c → size (above (above a b) c) ≡ size (above a (above b c))
size-above-assoc a b c = cong₂ _,_ (⊔-assoc _ _ _) (+-assoc _ _ _)

size-atop-assoc : ∀ a b c → size (atop (atop a b) c) ≡ size (atop a (atop b c))
size-atop-assoc a b c = cong₂ _,_ (⊔-assoc _ _ _) (⊔-assoc _ _ _)

size-atop-comm : ∀ a b → size (atop a b) ≡ size (atop b a)
size-atop-comm a b = cong₂ _,_ (⊔-comm _ _) (⊔-comm _ _)

-- a caption above or below takes the same room
size-labels : ∀ l d → size (labelAbove l d) ≡ size (labelBelow l d)
size-labels l d = refl

-- annotations are invisible to size
size-named : ∀ n d → size (named n d) ≡ size d
size-named n d = refl

size-connect : ∀ a pa b pb s d → size (connectP a pa b pb s d) ≡ size d
size-connect a pa b pb s d = refl

------------------------------------------------------------------------
-- Translation is an action

shiftDraw-zero : ∀ d → P.shiftDraw 0# 0# d ≡ d
shiftDraw-zero (rect x y w h s)   rewrite +-idʳ x | +-idʳ y = refl
shiftDraw-zero (circle x y r s)   rewrite +-idʳ x | +-idʳ y = refl
shiftDraw-zero (line a b c d s)   rewrite +-idʳ a | +-idʳ b | +-idʳ c | +-idʳ d = refl
shiftDraw-zero (arrow a b c d s)  rewrite +-idʳ a | +-idʳ b | +-idʳ c | +-idʳ d = refl
shiftDraw-zero (label x y n t s)  rewrite +-idʳ x | +-idʳ y = refl
shiftDraw-zero (path x y d s)     rewrite +-idʳ x | +-idʳ y = refl
shiftDraw-zero (group x y ds)     rewrite +-idʳ x | +-idʳ y = refl

shiftDraw-shift : ∀ a b c d e → P.shiftDraw a b (P.shiftDraw c d e) ≡ P.shiftDraw (c + a) (d + b) e
shiftDraw-shift a b c d (rect x y w h s)   rewrite +-assoc x c a | +-assoc y d b = refl
shiftDraw-shift a b c d (circle x y r s)   rewrite +-assoc x c a | +-assoc y d b = refl
shiftDraw-shift a b c d (line x y z u s)   rewrite +-assoc x c a | +-assoc y d b | +-assoc z c a | +-assoc u d b = refl
shiftDraw-shift a b c d (arrow x y z u s)  rewrite +-assoc x c a | +-assoc y d b | +-assoc z c a | +-assoc u d b = refl
shiftDraw-shift a b c d (label x y n t s)  rewrite +-assoc x c a | +-assoc y d b = refl
shiftDraw-shift a b c d (path x y e s)     rewrite +-assoc x c a | +-assoc y d b = refl
shiftDraw-shift a b c d (group x y ds)     rewrite +-assoc x c a | +-assoc y d b = refl

shiftAnchor-zero : ∀ x → P.shiftAnchor 0# 0# x ≡ x
shiftAnchor-zero (n , box l t w h) rewrite +-idʳ l | +-idʳ t = refl

shiftAnchor-shift : ∀ a b c d x → P.shiftAnchor a b (P.shiftAnchor c d x) ≡ P.shiftAnchor (c + a) (d + b) x
shiftAnchor-shift a b c d (n , box l t w h) rewrite +-assoc l c a | +-assoc t d b = refl

map-pointwise : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
map-pointwise e []       = refl
map-pointwise e (x ∷ xs) = cong₂ _∷_ (e x) (map-pointwise e xs)

map-id : ∀ {A : Set} {f : A → A} → (∀ x → f x ≡ x) → ∀ xs → map f xs ≡ xs
map-id e []       = refl
map-id e (x ∷ xs) = cong₂ _∷_ (e x) (map-id e xs)

map-map : ∀ {A B C : Set} (f : B → C) (g : A → B) (h : A → C) → (∀ x → f (g x) ≡ h x) → ∀ xs → map f (map g xs) ≡ map h xs
map-map f g h e []       = refl
map-map f g h e (x ∷ xs) = cong₂ _∷_ (e x) (map-map f g h e xs)

shift-zero : ∀ l → P.shift 0# 0# l ≡ l
shift-zero (mkLayout w h ds as) = cong₂ (mkLayout w h) (map-id shiftDraw-zero ds) (map-id shiftAnchor-zero as)

shift-shift : ∀ a b c d l → P.shift a b (P.shift c d l) ≡ P.shift (c + a) (d + b) l
shift-shift a b c d (mkLayout w h ds as) =
  cong₂ (mkLayout w h) (map-map _ _ _ (shiftDraw-shift a b c d) ds) (map-map _ _ _ (shiftAnchor-shift a b c d) as)

-- naming changes nothing visible: same frame, same drawings
named-frame : ∀ n l → (P.width (P.named n l) , P.height (P.named n l) , Layout.draws (P.named n l))
                      ≡ (P.width l , P.height l , Layout.draws l)
named-frame n l = refl
