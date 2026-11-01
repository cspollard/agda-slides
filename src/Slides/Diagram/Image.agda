{-# OPTIONS --safe --without-K #-}

-- The meaning of a layout as an image (`plans/Image.md` §4), generic in the meaning of a primitive.
--
-- A layout is a display list: its drawings in order, the later on top.  Given the image
-- `prim d : Image (S × S)` of one drawing, valued in a monoid `A` whose product is "then" (the
-- later on top, as `ovl` draws the second over the first),
--
--     ⟦ l ⟧[ prim ] = prim d₁ ∙ (prim d₂ ∙ … ∙ ε)      the fold of `Layout.draws l`
--
-- The frame and anchors do not draw.  Laws, all from the list structure (`Semantics.Image`):
--   * `⟦ ovl x y ⟧ ≈ ⟦ x ⟧ ∙ ⟦ y ⟧` (`⟦⟧-ovl`; overlay moves nothing, it concatenates), and the
--     drawings form a monoid homomorphism into images (`draws-isMonoidHomomorphism`);
--   * translation: `⟦ shift dx dy l ⟧ ≈ (dx , dy) · ⟦ l ⟧` (`⟦⟧-shift`), for a `prim` equivariant
--     for the action on drawings (`Equivariant`);
--   * change of scalar: `⟦ mapLayout ι l ⟧ (ι p) ≈ ⟦ l ⟧ p` (`⟦⟧-map`), for a natural `prim`.
--
-- Translation acts on images by reindexing along the inverse, `(v · im) p = im (p − v)`.  A
-- `Space` has only exact subtraction (ℕ has no negatives), so the inverse is data: a `Translation`
-- is `back v : Point → Point` with the action laws.  Over a group (ℚ², ℤ²) `back v p = p − v`.
-- No concrete `prim`, no plot support, no SVG here.

open import Algebra.Bundles using (Monoid)
open import Slides.Scalar.Space using (Space)

open import Level using (Level)

module Slides.Diagram.Image {c ℓ : Level} (M : Monoid c ℓ) where

open import Data.List.Base using (map)
open import Function.Base using (_$_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import Slides.Diagram.Draw
import Slides.Diagram.Place as P
import Slides.Diagram.Laws as L
open import Semantics.Image M

Point : Set → Set
Point S = S × S

⟦_⟧[_] : ∀ {S} → Layout S → (Draw S → Image (Point S)) → Image (Point S)
⟦ l ⟧[ prim ] = denote prim (Layout.draws l)

-- change of scalar: reading the points of the image of `mapLayout ι l` through `ι` gives the
-- image of `l`, if `prim` is natural.  No structure on the scalars is needed.
module _ {S T : Set} (ι : S → T) (primS : Draw S → Image (Point S)) (primT : Draw T → Image (Point T)) where
  private ι² = λ (p : Point S) → ι (proj₁ p) , ι (proj₂ p)

  ⟦⟧-map : (∀ d → reindex ι² (primT (mapDraw ι d)) ≈ primS d) → ∀ l →
           reindex ι² ⟦ mapLayout ι l ⟧[ primT ] ≈ ⟦ l ⟧[ primS ]
  ⟦⟧-map nat l = IMon.sym $ denote-rel R primS primT (mapDraw ι) (λ p → Monoid.refl M)
      (λ {_} {a′} {_} {b′} ra rb → IMon.trans (IMon.∙-cong ra rb) (IMon.sym (reindex-∙ ι² a′ b′))) (λ d → IMon.sym (nat d)) (Layout.draws l)
    where R = λ a a′ → a ≈ reindex ι² a′

module _ {S : Set} (Sp : Space S) (prim : Draw S → Image (Point S)) where
  open Space Sp using (0#)
  open L Sp using (drawAct; _⊕_; ovl; Action)

  private ⟦_⟧ = λ l → ⟦ l ⟧[ prim ]

  -- overlay is the product of images, the order kept
  ⟦⟧-ovl : ∀ x y → ⟦ ovl x y ⟧ ≈ ⟦ x ⟧ ∙ ⟦ y ⟧
  ⟦⟧-ovl x y = denote-++ prim (Layout.draws x) (Layout.draws y)

  -- the drawings of a layout form a monoid homomorphism into images
  draws-isMonoidHomomorphism = denote-isMonoidHomomorphism prim

  -- a translation, as the inverse it reindexes along
  record Translation : Set where
    field
      back      : Point S → Point S → Point S
      back-zero : ∀ q → back (0# , 0#) q ≡ q
      back-⊕    : ∀ p o q → back p (back o q) ≡ back (p ⊕ o) q

    shiftIm : Point S → Image (Point S) → Image (Point S)
    shiftIm v = reindex (back v)

    shiftIm-zero : ∀ im → shiftIm (0# , 0#) im ≈ im
    shiftIm-zero im q = Monoid.reflexive M (cong im (back-zero q))

    shiftIm-⊕ : ∀ p o im → shiftIm o (shiftIm p im) ≈ shiftIm (p ⊕ o) im
    shiftIm-⊕ p o im q = Monoid.reflexive M (cong im (back-⊕ p o q))

    -- the action on images is by monoid homomorphisms
    shiftIm-∙ : ∀ v a b → shiftIm v (a ∙ b) ≈ shiftIm v a ∙ shiftIm v b
    shiftIm-∙ v = reindex-∙ (back v)

    -- the meaning of a drawing moves with it
    Equivariant : Set ℓ
    Equivariant = ∀ v d → prim (Action.act drawAct v d) ≈ shiftIm v (prim d)

    -- ... so the meaning of a list of drawings, and of a shifted layout, move with them
    denote-shift : Equivariant → ∀ v ds →
      denote prim (map (Action.act drawAct v) ds) ≈ shiftIm v (denote prim ds)
    denote-shift eqv v ds = denote-rel R prim prim (Action.act drawAct v)
        (IMon.sym (reindex-ε (back v)))
        (λ {a} {_} {b} ra rb → IMon.trans (IMon.∙-cong ra rb) (IMon.sym (shiftIm-∙ v a b)))
        (λ d → eqv v d) ds
      where R = λ a b → b ≈ shiftIm v a

    ⟦⟧-shift : Equivariant → ∀ dx dy l → ⟦ P.shift Sp dx dy l ⟧ ≈ shiftIm (dx , dy) ⟦ l ⟧
    ⟦⟧-shift eqv dx dy l = denote-shift eqv (dx , dy) (Layout.draws l)
