{-# OPTIONS --safe --without-K #-}

-- Decidable equality of styles and drawing commands (over a scalar with decidable equality).
-- Used to group the ticks of a parametric animation into phases by what they ship
-- (`Slides.Anim.Phases`).

module Slides.Diagram.DrawEq where

open import Data.Maybe using (Maybe)
import Data.Maybe.Properties as MP
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as ΣP
open import Data.String using (String)
import Data.String.Properties as StrP
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Slides.Diagram using (Style; mkStyle)
open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label)

private
  maybeℕ : DecidableEquality (Maybe ℕ)
  maybeℕ = MP.≡-dec ℕP._≟_

  maybeS : DecidableEquality (Maybe String)
  maybeS = MP.≡-dec StrP._≟_

  Tup : Set
  Tup = Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe ℕ × Maybe String

  to : Style → Tup
  to s = Style.stroke s , Style.fill s , Style.strokeWidth s , Style.cls s , Style.ident s , Style.rx s , Style.dash s , Style.opacity s , Style.anchor s

  from : Tup → Style
  from (a , b , c , d , e , f , g , h , i) = mkStyle a b c d e f g h i

  tupEq : DecidableEquality Tup
  tupEq = ΣP.≡-dec maybeS (ΣP.≡-dec maybeS (ΣP.≡-dec maybeℕ (ΣP.≡-dec maybeS (ΣP.≡-dec maybeS
          (ΣP.≡-dec maybeℕ (ΣP.≡-dec maybeS (ΣP.≡-dec maybeℕ maybeS)))))))

styleEq? : DecidableEquality Style
styleEq? a b = map′ (λ p → cong from p) (λ q → cong to q) (tupEq (to a) (to b))

module _ {S : Set} (_≟ˢ_ : DecidableEquality S) where
  private
    -- equality of a tuple of arguments, then of the command
    4eq : DecidableEquality (S × S × S × S × Style)
    4eq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ styleEq?)))
    3eq : DecidableEquality (S × S × S × Style)
    3eq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ styleEq?))
    leq : DecidableEquality (S × S × ℕ × String × Style)
    leq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec ℕP._≟_ (ΣP.≡-dec StrP._≟_ styleEq?)))

  drawEq? : DecidableEquality (Draw S)
  drawEq? (rect x₁ y₁ w₁ h₁ s₁) (rect x₂ y₂ w₂ h₂ s₂) = map′ (λ { refl → refl }) (λ { refl → refl }) (4eq (x₁ , y₁ , w₁ , h₁ , s₁) (x₂ , y₂ , w₂ , h₂ , s₂))
  drawEq? (rect _ _ _ _ _) (circle _ _ _ _) = no λ ()
  drawEq? (rect _ _ _ _ _) (line _ _ _ _ _) = no λ ()
  drawEq? (rect _ _ _ _ _) (arrow _ _ _ _ _) = no λ ()
  drawEq? (rect _ _ _ _ _) (label _ _ _ _ _) = no λ ()
  drawEq? (circle _ _ _ _) (rect _ _ _ _ _) = no λ ()
  drawEq? (circle x₁ y₁ r₁ s₁) (circle x₂ y₂ r₂ s₂) = map′ (λ { refl → refl }) (λ { refl → refl }) (3eq (x₁ , y₁ , r₁ , s₁) (x₂ , y₂ , r₂ , s₂))
  drawEq? (circle _ _ _ _) (line _ _ _ _ _) = no λ ()
  drawEq? (circle _ _ _ _) (arrow _ _ _ _ _) = no λ ()
  drawEq? (circle _ _ _ _) (label _ _ _ _ _) = no λ ()
  drawEq? (line _ _ _ _ _) (rect _ _ _ _ _) = no λ ()
  drawEq? (line _ _ _ _ _) (circle _ _ _ _) = no λ ()
  drawEq? (line a₁ b₁ c₁ d₁ s₁) (line a₂ b₂ c₂ d₂ s₂) = map′ (λ { refl → refl }) (λ { refl → refl }) (4eq (a₁ , b₁ , c₁ , d₁ , s₁) (a₂ , b₂ , c₂ , d₂ , s₂))
  drawEq? (line _ _ _ _ _) (arrow _ _ _ _ _) = no λ ()
  drawEq? (line _ _ _ _ _) (label _ _ _ _ _) = no λ ()
  drawEq? (arrow _ _ _ _ _) (rect _ _ _ _ _) = no λ ()
  drawEq? (arrow _ _ _ _ _) (circle _ _ _ _) = no λ ()
  drawEq? (arrow _ _ _ _ _) (line _ _ _ _ _) = no λ ()
  drawEq? (arrow a₁ b₁ c₁ d₁ s₁) (arrow a₂ b₂ c₂ d₂ s₂) = map′ (λ { refl → refl }) (λ { refl → refl }) (4eq (a₁ , b₁ , c₁ , d₁ , s₁) (a₂ , b₂ , c₂ , d₂ , s₂))
  drawEq? (arrow _ _ _ _ _) (label _ _ _ _ _) = no λ ()
  drawEq? (label _ _ _ _ _) (rect _ _ _ _ _) = no λ ()
  drawEq? (label _ _ _ _ _) (circle _ _ _ _) = no λ ()
  drawEq? (label _ _ _ _ _) (line _ _ _ _ _) = no λ ()
  drawEq? (label _ _ _ _ _) (arrow _ _ _ _ _) = no λ ()
  drawEq? (label x₁ y₁ n₁ t₁ s₁) (label x₂ y₂ n₂ t₂ s₂) = map′ (λ { refl → refl }) (λ { refl → refl }) (leq (x₁ , y₁ , n₁ , t₁ , s₁) (x₂ , y₂ , n₂ , t₂ , s₂))
