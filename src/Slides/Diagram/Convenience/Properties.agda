{-# OPTIONS --safe --without-K #-}

-- The laws of the convenience combinators, from the laws of the connectives
-- (`Slides.Diagram.Assoc`, `Slides.Diagram.Laws`): joining lists with a gap is compatible with
-- appending them, so a row (column) may be cut anywhere into two rows (columns) with a gap
-- between; a gap has the size it says; gaps add; and, for a valid diagram, zero margins vanish
-- (`Slides.Diagram.Valid`: the layout of the empty diagram is a unit).

open import Data.Nat.Base using (ℕ)
open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Convenience.Properties {S : Set} (Sp : Space S) (fromℕ : ℕ → S) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open Space Sp
import Slides.Diagram.Syntax as D
import Slides.Diagram.Place Sp as P
open import Slides.Diagram.Layout Sp using (layout)
open import Slides.Diagram.Laws Sp using (size)
open import Slides.Diagram.Assoc Sp using (besideSG; aboveSG)
open import Algebra.Structures using (IsSemigroup)
import Slides.Diagram.Convenience as C
import Slides.Diagram.Valid Sp as V
open C using (_∥_; _═_; _⊙_)
open import Slides.Diagram.Geometry using (middle; centred)
open C using (cat)
open C.ConvenienceWith 0# fromℕ

-- a gap is as wide (high) as it says
size-↔ : ∀ n → size (↔ n) ≡ (n , 0#)
size-↔ n = refl

size-↕ : ∀ n → size (↕ n) ≡ (0# , n)
size-↕ n = refl

-- cutting a joined list anywhere (`cat`): a row or a column, the layout of either is that of the
-- two parts with a separator between them.  Only associativity is used, so one statement serves
-- every alignment of both connectives.
cut : ∀ {X Y : Set} {_∙_ : X → X → X} {_∙′_ : Y → Y → Y} → IsSemigroup _≡_ _∙′_ →
      (φ : X → Y) → (∀ a b → φ (a ∙ b) ≡ φ a ∙′ φ b) → ∀ g x xs y ys →
      φ (cat _∙_ g x (xs ++ y ∷ ys)) ≡ φ (cat _∙_ g x xs ∙ (g ∙ cat _∙_ g y ys))
cut {_∙_ = _∙_} {_∙′_} sg φ hom g x []       y ys = refl
cut {_∙_ = _∙_} {_∙′_} sg φ hom g x (z ∷ xs) y ys = begin
  φ (x ∙ (g ∙ cat _∙_ g z (xs ++ y ∷ ys)))                  ≡⟨ hom _ _ ⟩
  φ x ∙′ φ (g ∙ cat _∙_ g z (xs ++ y ∷ ys))                  ≡⟨ cong (φ x ∙′_) (hom _ _) ⟩
  φ x ∙′ (φ g ∙′ φ (cat _∙_ g z (xs ++ y ∷ ys)))
    ≡⟨ cong (λ t → φ x ∙′ (φ g ∙′ t)) (trans (cut sg φ hom g z xs y ys) (hom _ _)) ⟩
  φ x ∙′ (φ g ∙′ (φ C ∙′ φ (g ∙ R)))                        ≡⟨ cong (λ t → φ x ∙′ (φ g ∙′ (φ C ∙′ t))) (hom _ _) ⟩
  φ x ∙′ (φ g ∙′ (φ C ∙′ (φ g ∙′ φ R)))                     ≡⟨ cong (φ x ∙′_) (sym (assoc _ _ _)) ⟩
  φ x ∙′ ((φ g ∙′ φ C) ∙′ (φ g ∙′ φ R))                     ≡⟨ sym (assoc _ _ _) ⟩
  (φ x ∙′ (φ g ∙′ φ C)) ∙′ (φ g ∙′ φ R)
    ≡⟨ sym (cong₂ _∙′_ (trans (hom _ _) (cong (φ x ∙′_) (hom _ _))) (hom _ _)) ⟩
  φ (x ∙ (g ∙ C)) ∙′ φ (g ∙ R)                              ≡⟨ sym (hom _ _) ⟩
  φ ((x ∙ (g ∙ C)) ∙ (g ∙ R))                               ∎
  where open IsSemigroup sg using (assoc)
        C = cat _∙_ g z xs
        R = cat _∙_ g y ys

hcat-++ : ∀ al g x xs y ys → layout (hcatA al g (x ∷ xs ++ y ∷ ys))
  ≡ layout (D.besideA al (hcatA al g (x ∷ xs)) (D.besideA al (↔ g) (hcatA al g (y ∷ ys))))
hcat-++ al g x xs y ys = cut (besideSG al) layout (λ _ _ → refl) (↔ g) x xs y ys

vcat-++ : ∀ al g x xs y ys → layout (vcatA al g (x ∷ xs ++ y ∷ ys))
  ≡ layout (D.aboveA al (vcatA al g (x ∷ xs)) (D.aboveA al (↕ g) (vcatA al g (y ∷ ys))))
vcat-++ al g x xs y ys = cut (aboveSG al) layout (λ _ _ → refl) (↕ g) x xs y ys

-- gaps add, as layouts
gap-∥ : ∀ a b → layout (↔ a ∥ ↔ b) ≡ layout (↔ (a + b))
gap-∥ a b = V.gap-beside middle a b

gap-═ : ∀ a b → layout (↕ a ═ ↕ b) ≡ layout (↕ (a + b))
gap-═ a b = V.gap-above centred a b

gap-⊙ : ∀ a b → layout (↔ a ⊙ ↔ b) ≡ layout (↔ (a ⊔ b))
gap-⊙ a b rewrite ⊔-≥ (≤-refl {0#}) = refl

-- zero margins vanish from a valid diagram
margin-zero : ∀ d → V.Valid d → layout (margin 0# 0# 0# 0# d) ≡ layout d
margin-zero d v =
  trans (cong (P.besideA middle E) (trans (cong (λ x → P.besideA middle x E) col) (V.besideA-unitʳ middle L h)))
        (V.besideA-unitˡ middle L h)
  where
    L = layout d
    E = V.empty
    w = proj₁ (V.valid-layout d v)
    h = proj₂ (V.valid-layout d v)
    col = trans (cong (P.aboveA centred E) (V.aboveA-unitʳ centred L w)) (V.aboveA-unitˡ centred L w)
