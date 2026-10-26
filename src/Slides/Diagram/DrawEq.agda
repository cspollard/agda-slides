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
import Data.Sum.Properties as SP
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
import Data.String.Properties as StrP
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using ()
open import Relation.Nullary.Decidable using (map′)

open import Slides.DecEq using (retract-dec)
open import Slides.Diagram using (Style; mkStyle)
open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label)

private
  maybeℕ : DecidableEquality (Maybe ℕ)
  maybeℕ = MP.≡-dec ℕP._≟_

  maybeS : DecidableEquality (Maybe String)
  maybeS = MP.≡-dec StrP._≟_

  Tup : Set
  Tup = Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe String × Maybe ℕ × Maybe String × Maybe ℕ × Maybe String

  styleTo : Style → Tup
  styleTo s = Style.stroke s , Style.fill s , Style.strokeWidth s , Style.cls s , Style.ident s , Style.rx s , Style.dash s , Style.opacity s , Style.anchor s

  styleFrom : Tup → Style
  styleFrom (a , b , c , d , e , f , g , h , i) = mkStyle a b c d e f g h i

  tupEq : DecidableEquality Tup
  tupEq = ΣP.≡-dec maybeS (ΣP.≡-dec maybeS (ΣP.≡-dec maybeℕ (ΣP.≡-dec maybeS (ΣP.≡-dec maybeS
          (ΣP.≡-dec maybeℕ (ΣP.≡-dec maybeS (ΣP.≡-dec maybeℕ maybeS)))))))

styleEq? : DecidableEquality Style
styleEq? a b = map′ (cong styleFrom) (cong styleTo) (tupEq (styleTo a) (styleTo b))

-- A drawing command is a sum of tuples (`Slides.DecEq`): no clause for a pair of different
-- constructors.
module _ {S : Set} (_≟ˢ_ : DecidableEquality S) where
  private
    4eq : DecidableEquality (S × S × S × S × Style)
    4eq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ styleEq?)))
    3eq : DecidableEquality (S × S × S × Style)
    3eq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ styleEq?))
    leq : DecidableEquality (S × S × ℕ × String × Style)
    leq = ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec _≟ˢ_ (ΣP.≡-dec ℕP._≟_ (ΣP.≡-dec StrP._≟_ styleEq?)))

    Code : Set
    Code = (S × S × S × S × Style) ⊎ (S × S × S × Style) ⊎ (S × S × S × S × Style) ⊎ (S × S × S × S × Style)
           ⊎ (S × S × ℕ × String × Style)

    to : Draw S → Code
    to (rect x y w h s)     = inj₁ (x , y , w , h , s)
    to (circle x y r s)     = inj₂ (inj₁ (x , y , r , s))
    to (line a b c d s)     = inj₂ (inj₂ (inj₁ (a , b , c , d , s)))
    to (arrow a b c d s)    = inj₂ (inj₂ (inj₂ (inj₁ (a , b , c , d , s))))
    to (label x y n t s)    = inj₂ (inj₂ (inj₂ (inj₂ (x , y , n , t , s))))

    from : Code → Draw S
    from (inj₁ (x , y , w , h , s))                       = rect x y w h s
    from (inj₂ (inj₁ (x , y , r , s)))                    = circle x y r s
    from (inj₂ (inj₂ (inj₁ (a , b , c , d , s))))         = line a b c d s
    from (inj₂ (inj₂ (inj₂ (inj₁ (a , b , c , d , s)))))  = arrow a b c d s
    from (inj₂ (inj₂ (inj₂ (inj₂ (x , y , n , t , s)))))  = label x y n t s

    from-to : ∀ d → from (to d) ≡ d
    from-to (rect _ _ _ _ _)  = refl
    from-to (circle _ _ _ _)  = refl
    from-to (line _ _ _ _ _)  = refl
    from-to (arrow _ _ _ _ _) = refl
    from-to (label _ _ _ _ _) = refl

  drawEq? : DecidableEquality (Draw S)
  drawEq? = retract-dec to from from-to (SP.≡-dec 4eq (SP.≡-dec 3eq (SP.≡-dec 4eq (SP.≡-dec 4eq leq))))
