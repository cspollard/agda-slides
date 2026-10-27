{-# OPTIONS --safe --without-K #-}

-- The bridge between the generic tree equality `Container.FreeMonad.Eq` and parsnip's bisimilarity `_≈ₓ_`.
module Slides.Backend.XML.Properties where

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)


open import Data.XML.AST using (XMLC; XMLDoc; XMLShape)
open import Slides.Backend.XML

------------------------------------------------------------------------
-- Bridge: the generic tree equality is parsnip's bisimilarity
--
-- On `XMLDoc = XMLC ⋆ ⊥`, `Container.FreeMonad.Eq` (equal shapes, pairwise
-- equal children) coincides with `_≈ₓ_`.  So generic results about
-- `Free₀ XMLC` (folds, fusion) can be stated for parsnip's equality.

open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥)
open import Data.Container.Pos using (Pos)
open import Data.Product.Base using (_,_; Σ; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; subst)

open import Data.XML.AST using (shape)
open import Data.XML.Equality using (_≈ₓ_; ≈element)
open import Container.FreeMonad using (Eq)

-- The empty setoid (on `⊥` itself, the leaves of `XMLDoc`).
⊥ˢ : Setoid 0ℓ 0ℓ
⊥ˢ = record
  { Carrier       = ⊥
  ; _≈_           = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  }

XMLEq : XMLDoc → XMLDoc → Set
XMLEq = Eq {C = XMLC} ⊥ˢ

≈ₓ-from-Eq : ∀ {t u} → XMLEq t u → t ≈ₓ u
≈ₓ-from-Eq {pure ()}
≈ₓ-from-Eq {impure _} {pure ()}
≈ₓ-from-Eq {impure (shape _ _ _ _ _ _ _ , f)} {impure (shape _ _ _ _ _ _ _ , g)}
           (refl , h) =
  ≈element refl refl (λ i → ≈ₓ-from-Eq (h i))

-- Validity evidence is proof-irrelevant (`T b` is `⊤` or `⊥`).
private
  T-irrel : ∀ {b} (x y : T b) → x ≡ y
  T-irrel {true}  _ _ = refl
  T-irrel {false} ()

  shape-eq : ∀ {tag attrs n ts pt pt′ pa pa′ px px′} →
             pt ≡ pt′ → pa ≡ pa′ → px ≡ px′ →
             Σ (shape tag attrs n ts pt pa px ≡ shape tag attrs n ts pt′ pa′ px′)
               (λ e → ∀ (q : Pos n) → subst (λ s → Pos (XMLShape.arity s)) e q ≡ q)
  shape-eq refl refl refl = refl , λ _ → refl

Eq-from-≈ₓ : ∀ {t u} → t ≈ₓ u → XMLEq t u
Eq-from-≈ₓ (≈element {tag} {attrs} {n} {_} {ts} {_} {pt} {pt′} {pa} {pa′} {px} {px′}
                     {f} {g} refl refl h) =
  proj₁ se , λ q →
    subst (λ z → XMLEq (f q) (g z)) (sym (proj₂ se q)) (Eq-from-≈ₓ (h q))
  where
    se = shape-eq {tag} {attrs} {n} {ts} (T-irrel pt pt′) (T-irrel pa pa′) (T-irrel px px′)
