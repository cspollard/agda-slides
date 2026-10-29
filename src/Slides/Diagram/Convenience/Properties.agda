{-# OPTIONS --safe --without-K #-}

-- The laws of the convenience combinators, from the laws of the connectives
-- (`Slides.Diagram.Assoc`, `Slides.Diagram.Laws`): joining lists with a gap is compatible with
-- appending them, so a row (column) may be cut anywhere into two rows (columns) with a gap
-- between; and a gap has the size it says.

open import Data.Nat.Base using (ℕ)
open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Convenience.Properties {S : Set} (Sp : Space S) (fromℕ : ℕ → S) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open Space Sp
import Slides.Diagram.Syntax as D
import Slides.Diagram.Place Sp as P
open import Slides.Diagram.Layout Sp using (layout)
open import Slides.Diagram.Laws Sp using (size)
open import Slides.Diagram.Assoc Sp using (besideA-assoc; aboveA-assoc)
import Slides.Diagram.Convenience as C
open C.ConvenienceWith 0# fromℕ

-- a gap is as wide (high) as it says
size-↔ : ∀ n → size (↔ n) ≡ (n , 0#)
size-↔ n = refl

size-↕ : ∀ n → size (↕ n) ≡ (0# , n)
size-↕ n = refl

-- cutting a row anywhere: the layout is that of the two rows with a gap between them
hcat-++ : ∀ al g x xs y ys → layout (hcatA al g (x ∷ xs ++ y ∷ ys))
  ≡ layout (D.besideA al (hcatA al g (x ∷ xs)) (D.besideA al (↔ g) (hcatA al g (y ∷ ys))))
hcat-++ al g x []        y ys = refl
hcat-++ al g x (x′ ∷ xs) y ys =
  trans (cong (λ z → P.besideA al (layout x) (P.besideA al (layout (↔ g)) z)) (hcat-++ al g x′ xs y ys))
    (sym (trans (besideA-assoc al (layout x) (P.besideA al (layout (↔ g)) (layout (hcatA al g (x′ ∷ xs)))) _)
                (cong (P.besideA al (layout x))
                      (besideA-assoc al (layout (↔ g)) (layout (hcatA al g (x′ ∷ xs))) _))))

-- the same for a column
vcat-++ : ∀ al g x xs y ys → layout (vcatA al g (x ∷ xs ++ y ∷ ys))
  ≡ layout (D.aboveA al (vcatA al g (x ∷ xs)) (D.aboveA al (↕ g) (vcatA al g (y ∷ ys))))
vcat-++ al g x []        y ys = refl
vcat-++ al g x (x′ ∷ xs) y ys =
  trans (cong (λ z → P.aboveA al (layout x) (P.aboveA al (layout (↕ g)) z)) (vcat-++ al g x′ xs y ys))
    (sym (trans (aboveA-assoc al (layout x) (P.aboveA al (layout (↕ g)) (layout (vcatA al g (x′ ∷ xs)))) _)
                (cong (P.aboveA al (layout x))
                      (aboveA-assoc al (layout (↕ g)) (layout (vcatA al g (x′ ∷ xs))) _))))
