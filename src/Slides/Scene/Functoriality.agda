{-# OPTIONS --safe --without-K #-}

-- `mapScene` (change of clock and drivers) is a functor, as `mapDia` is.
--
--   mapScene id id ≈ id        mapScene h₂ g₂ ∘ mapScene h₁ g₁ ≈ mapScene (h₂ ∘ h₁) (g₂ ∘ g₁)
--   fold-mapScene              folding a mapped scene is folding the original with the handler
--                              pulled back

module Slides.Scene.Functoriality where

open import Level using (lift)
open import Function.Base using (id; _∘_)
open import Data.Product.Base using (_,_)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pull; pfold-translate)
open import Container.Lowering using (_≈⋆_)
open import Container.Tagged using (over-id; over-∘)
open import Slides.Scene.Syntax

mapP-id : ∀ {T D} t (p : Held t T D) → mapP id id t p ≡ p
mapP-id seqK    _ = refl
mapP-id parK    _ = refl
mapP-id holdK   _ = refl
mapP-id delayK  _ = refl
mapP-id repeatK _ = refl
mapP-id driveK  _ = refl

mapP-∘ : ∀ {T₁ T₂ T₃ D₁ D₂ D₃} (h₂ : T₂ → T₃) (h₁ : T₁ → T₂) (g₂ : D₂ → D₃) (g₁ : D₁ → D₂) t (p : Held t T₁ D₁) →
         mapP h₂ g₂ t (mapP h₁ g₁ t p) ≡ mapP (h₂ ∘ h₁) (g₂ ∘ g₁) t p
mapP-∘ h₂ h₁ g₂ g₁ seqK    _ = refl
mapP-∘ h₂ h₁ g₂ g₁ parK    _ = refl
mapP-∘ h₂ h₁ g₂ g₁ holdK   _ = refl
mapP-∘ h₂ h₁ g₂ g₁ delayK  _ = refl
mapP-∘ h₂ h₁ g₂ g₁ repeatK _ = refl
mapP-∘ h₂ h₁ g₂ g₁ driveK  _ = refl

mapScene-id : ∀ {T D A} (s : Scene T D A) → mapScene id id s ≈⋆ s
mapScene-id {T} {D} = over-id arity {P = λ t → Held t T D} (mapP id id) mapP-id

mapScene-∘ : ∀ {T₁ T₂ T₃ D₁ D₂ D₃ A} (h₂ : T₂ → T₃) (h₁ : T₁ → T₂) (g₂ : D₂ → D₃) (g₁ : D₁ → D₂)
             (s : Scene T₁ D₁ A) → mapScene h₂ g₂ (mapScene h₁ g₁ s) ≈⋆ mapScene (h₂ ∘ h₁) (g₂ ∘ g₁) s
mapScene-∘ {T₁} {T₂} {T₃} {D₁} {D₂} {D₃} h₂ h₁ g₂ g₁ =
  over-∘ arity {P = λ t → Held t T₁ D₁} {Q = λ t → Held t T₂ D₂} {R = λ t → Held t T₃ D₃}
    (mapP h₂ g₂) (mapP h₁ g₁) (mapP (h₂ ∘ h₁) (g₂ ∘ g₁)) (mapP-∘ h₂ h₁ g₂ g₁)

fold-mapScene : ∀ {T₁ T₂ D₁ D₂ A a ℓ} (h : T₁ → T₂) (g : D₁ → D₂) (R : Setoid a ℓ)
                {k : Handler (SceneC T₂ D₂) (Setoid.Carrier R)} (c : Congruent (SceneC T₂ D₂) R k)
                {f : A → Setoid.Carrier R} (s : Scene T₁ D₁ A) →
                Setoid._≈_ R (pfold (SceneC T₂ D₂) k f (mapScene h g s)) (pfold (SceneC T₁ D₁) (pull (mapSC h g) k) f s)
fold-mapScene h g R c = pfold-translate (mapSC h g) R c
