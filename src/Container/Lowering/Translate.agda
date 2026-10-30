{-# OPTIONS --safe --without-K #-}

-- Container morphisms act on programs functorially.
--
--   translate-cong   translation respects equality of programs
--   translate-ext    morphisms equal on shapes and (transported) positions translate alike
--   translate-id     the identity translates to the identity
--   translate-∘      translating along a composite is translating in turn
--   embed-id, embed-∘   the same laws for `embed`, as laws of lowerings
--
-- Renaming a vocabulary or changing a language's scalar is such a translation.

module Container.Lowering.Translate where

open import Level using (Level; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
import Data.Container.Morphism as CM
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

open import Container.Lowering
open import Container.Lowering.Properties

private
  variable
    s p c : Level

module _ {C D : Container s p} {X : Set c} where

  -- Translation respects equality of programs.
  translate-cong : (m : C ⇒ D) {t u : C ⋆ X} → t ≈⋆ u → translate m t ≈⋆ translate m u
  translate-cong m {pure _}         {pure _}           e        = e
  translate-cong m {pure _}         {impure _}         ()
  translate-cong m {impure _}       {pure _}           ()
  translate-cong m {impure (a , k)} {impure (.a , k′)} (refl , e) =
    refl , λ q → translate-cong m (e (position m q))

  private
    -- Translating a continuation at equal positions.
    cont : (n : C ⇒ D) {a : Shape C} (k : Position C a → C ⋆ X) {q q′ : Position C a} → q ≡ q′ →
         translate n (k q) ≈⋆ translate n (k q′)
    cont n k refl = refl≈ _

  -- Morphisms that agree on shapes, and on positions up to that agreement, translate alike.
  translate-ext : (m n : C ⇒ D) (e : ∀ a → shape m a ≡ shape n a) →
                  (∀ a (q : Position D (shape m a)) →
                     position m q ≡ position n (subst (Position D) (e a) q)) →
                  ∀ t → translate m t ≈⋆ translate n t
  translate-ext m n e pe (pure _)         = lift refl
  translate-ext m n e pe (impure (a , k)) = e a , λ q →
    trans≈ (translate-ext m n e pe (k (position m q))) (cont n k (pe a q))

module _ {C : Container s p} {X : Set c} where

  -- The identity morphism translates to the identity.
  translate-id : (t : C ⋆ X) → translate (CM.id C) t ≈⋆ t
  translate-id (pure _)         = lift refl
  translate-id (impure (_ , k)) = refl , λ q → translate-id (k q)

module _ {C D E : Container s p} {X : Set c} where

  -- Map fusion: translating along a composite is translating along each in turn.
  translate-∘ : (m : D ⇒ E) (n : C ⇒ D) (t : C ⋆ X) →
                translate (m CM.∘ n) t ≈⋆ translate m (translate n t)
  translate-∘ m n (pure _)         = lift refl
  translate-∘ m n (impure (_ , k)) = refl , λ q → translate-∘ m n (k (position n (position m q)))

-- Container morphisms embed as lowerings functorially.
embed-id : ∀ {C : Container s p} → embed (CM.id C) ≈ˡ ret
embed-id a = refl , λ q → lift refl

embed-∘ : ∀ {C D E : Container s p} (m : D ⇒ E) (n : C ⇒ D) →
          embed (m CM.∘ n) ≈ˡ (embed n ⋙ embed m)
embed-∘ m n a = refl , λ q → lift refl
