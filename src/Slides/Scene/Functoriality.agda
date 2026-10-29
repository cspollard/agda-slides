{-# OPTIONS --safe --without-K #-}

-- Change of clock and drivers is a functor: `mapScene` preserves identities and composition,
-- as `mapDia` does (`Slides.Diagram.Functoriality`).  `mapScene h g = translate (mapSC h g)`.
--
--   mapScene id id ≈ id        mapScene h₂ g₂ ∘ mapScene h₁ g₁ ≈ mapScene (h₂ ∘ h₁) (g₂ ∘ g₁)
--
-- and folding a mapped scene is folding the original with the handler pulled back (`fold-mapScene`).

module Slides.Scene.Functoriality where

open import Level using (lift)
open import Function.Base using (id; _∘_)
open import Data.Product.Base using (_,_)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl)

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pull; pfold-translate)
open import Container.Lowering using (_≈⋆_)
open import Slides.Scene.Syntax

mapScene-id : ∀ {T D A} (s : Scene T D A) → mapScene id id s ≈⋆ s
mapScene-id (pure _)                = lift refl
mapScene-id (impure (Seq , k))      = refl , λ q → mapScene-id (k q)
mapScene-id (impure (Par , k))      = refl , λ q → mapScene-id (k q)
mapScene-id (impure (Hold _ , k))   = refl , λ q → mapScene-id (k q)
mapScene-id (impure (Delay _ , k))  = refl , λ q → mapScene-id (k q)
mapScene-id (impure (Repeat _ , k)) = refl , λ q → mapScene-id (k q)
mapScene-id (impure (Drive _ , k))  = refl , λ q → mapScene-id (k q)

mapScene-∘ : ∀ {T₁ T₂ T₃ D₁ D₂ D₃ A} (h₂ : T₂ → T₃) (h₁ : T₁ → T₂) (g₂ : D₂ → D₃) (g₁ : D₁ → D₂)
             (s : Scene T₁ D₁ A) → mapScene h₂ g₂ (mapScene h₁ g₁ s) ≈⋆ mapScene (h₂ ∘ h₁) (g₂ ∘ g₁) s
mapScene-∘ h₂ h₁ g₂ g₁ (pure _)                = lift refl
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Seq , k))      = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Par , k))      = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Hold _ , k))   = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Delay _ , k))  = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Repeat _ , k)) = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)
mapScene-∘ h₂ h₁ g₂ g₁ (impure (Drive _ , k))  = refl , λ q → mapScene-∘ h₂ h₁ g₂ g₁ (k q)

fold-mapScene : ∀ {T₁ T₂ D₁ D₂ A a ℓ} (h : T₁ → T₂) (g : D₁ → D₂) (R : Setoid a ℓ)
                {k : Handler (SceneC T₂ D₂) (Setoid.Carrier R)} (c : Congruent (SceneC T₂ D₂) R k)
                {f : A → Setoid.Carrier R} (s : Scene T₁ D₁ A) →
                Setoid._≈_ R (pfold (SceneC T₂ D₂) k f (mapScene h g s)) (pfold (SceneC T₁ D₁) (pull (mapSC h g) k) f s)
fold-mapScene h g R c = pfold-translate (mapSC h g) R c
