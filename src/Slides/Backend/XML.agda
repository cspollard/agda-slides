{-# OPTIONS --safe --without-K #-}

-- Bridge between the generic container development and parsnip's XML.
--
-- parsnip's XML AST is the free monad over the container `XMLC`
-- (`XMLDoc = XMLC ⋆ ⊥`) with `Setoid 0ℓ 0ℓ` equality `XMLSetoid`, so the
-- `Container.*` machinery applies directly: `Poly XMLC` is an endofunctor on
-- `Setoids 0ℓ 0ℓ`, and XML-producing backends are algebras of slide
-- containers whose carrier is built from `XMLSetoid`.

module Slides.Backend.XML where

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Endofunctor)

open import Data.XML.AST using (XMLC; XMLDoc; XMLShape)
open import Data.XML.Equality using (XMLSetoid)
open import Data.XML.Print using (printXML)
open import Data.XML.RoundTrip using (xmlStage)

open import Container.Polynomial using (Poly)
open import Container.FreeMonad using (Free₀)

XMLEndo : Endofunctor (Setoids 0ℓ 0ℓ)
XMLEndo = Poly XMLC

-- Trees of XML nodes with leaves in `X`.
XMLTrees : Setoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ
XMLTrees = Free₀ XMLC

------------------------------------------------------------------------
-- Bridge: the generic tree equality is parsnip's bisimilarity
--
-- On `XMLDoc = XMLC ⋆ ⊥`, `Container.FreeMonad.Eq` (equal shapes, pairwise
-- equal children) coincides with `_≈ₓ_`.  So generic results about
-- `Free₀ XMLC` (folds, fusion) can be stated for parsnip's equality.

open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product.Base using (_,_; Σ; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; subst)

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
               (λ e → ∀ (q : Fin n) → subst (λ s → Fin (XMLShape.arity s)) e q ≡ q)
  shape-eq refl refl refl = refl , λ _ → refl

Eq-from-≈ₓ : ∀ {t u} → t ≈ₓ u → XMLEq t u
Eq-from-≈ₓ (≈element {tag} {attrs} {n} {_} {ts} {_} {pt} {pt′} {pa} {pa′} {px} {px′}
                     {f} {g} refl refl h) =
  proj₁ se , λ q →
    subst (λ z → XMLEq (f q) (g z)) (sym (proj₂ se q)) (Eq-from-≈ₓ (h q))
  where
    se = shape-eq {tag} {attrs} {n} {ts} (T-irrel pt pt′) (T-irrel pa pa′) (T-irrel px px′)
