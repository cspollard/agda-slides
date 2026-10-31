{-# OPTIONS --safe --without-K #-}

-- A change of scalar is a functor: `mapDia` and `mapLayout` preserve identities and composition.
--
--   mapDia id ≈ id          mapDia (g ∘ f) ≈ mapDia g ∘ mapDia f          (equality of programs)
--   mapLayout id ≡ id       mapLayout (g ∘ f) ≡ mapLayout g ∘ mapLayout f
--
-- (`mapDia-id`, `mapDia-∘`, `mapLayout-id`, `mapLayout-∘`.)  Since `mapDia f = translate (mapC f)`,
-- these say `mapC` is a functor into container morphisms (`Container.Tagged`: the identity on
-- positions, so no clause per command).  Folding along a map is folding with the
-- handler pulled back along `mapC f` (`fold-mapDia`, an instance of `pfold-translate`).

module Slides.Diagram.Functoriality where

open import Function.Base using (id; _∘_)
open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Data.Container.Core using (position)
open import Data.Container.FreeMonad using (pure; impure)
import Data.List.Properties as ListP
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pull; pfold-translate)
open import Container.Lowering using (_≈⋆_; translate)
open import Container.Tagged using (over-id; over-∘)
open import Slides.Diagram.Draw
open import Slides.Diagram.Syntax

-- Diagrams: the laws of `fmap` on payloads, lifted by `over-id` and `over-∘`

mapDia-id : ∀ {S} (t : Dia S) → mapDia id t ≈⋆ t
mapDia-id {S} = over-id arity {P = λ t → Payload t S} (λ t → fmap id (fields t)) (λ t → fmap-id (fields t))

mapDia-∘ : ∀ {S T U} (g : T → U) (f : S → T) (t : Dia S) → mapDia g (mapDia f t) ≈⋆ mapDia (g ∘ f) t
mapDia-∘ {S} {T} {U} g f = over-∘ arity {P = λ t → Payload t S} {Q = λ t → Payload t T} {R = λ t → Payload t U} (λ t → fmap g (fields t)) (λ t → fmap f (fields t)) (λ t → fmap (g ∘ f) (fields t)) (λ t → fmap-∘ g f (fields t))

-- Folding after a change of scalar is folding the original with the handler pulled back along `mapC f`.
fold-mapDia : ∀ {S T a ℓ} (f : S → T) (A : Setoid a ℓ) {h : Handler (DiagramC T) (Setoid.Carrier A)}
              (c : Congruent (DiagramC T) A h) (t : Dia S) →
              Setoid._≈_ A (pfold (DiagramC T) h (λ ()) (mapDia f t)) (pfold (DiagramC S) (pull (mapC f) h) (λ ()) t)
fold-mapDia f A c t = pfold-translate (mapC f) A c {X = ⊥} {f = λ ()} t

-- Layouts

mapDraw-id : ∀ {S} (d : Draw S) → mapDraw id d ≡ d
mapDraw-id (rect _ _ _ _ _)  = refl
mapDraw-id (circle _ _ _ _)  = refl
mapDraw-id (ellipse _ _ _ _ _) = refl
mapDraw-id (poly c ps s)     = cong (λ qs → poly c qs s) (ListP.map-id ps)
mapDraw-id (line _ _ _ _ _)  = refl
mapDraw-id (arrow _ _ _ _ _) = refl
mapDraw-id (label _ _ _ _ _) = refl
mapDraw-id (path _ _ _ _)    = refl

mapDraw-∘ : ∀ {S T U} (g : T → U) (f : S → T) (d : Draw S) → mapDraw g (mapDraw f d) ≡ mapDraw (g ∘ f) d
mapDraw-∘ g f (rect _ _ _ _ _)  = refl
mapDraw-∘ g f (circle _ _ _ _)  = refl
mapDraw-∘ g f (ellipse _ _ _ _ _) = refl
mapDraw-∘ g f (poly c ps s)     = cong (λ qs → poly c qs s) (trans (sym (ListP.map-∘ ps)) (ListP.map-cong (λ _ → refl) ps))
mapDraw-∘ g f (line _ _ _ _ _)  = refl
mapDraw-∘ g f (arrow _ _ _ _ _) = refl
mapDraw-∘ g f (label _ _ _ _ _) = refl
mapDraw-∘ g f (path _ _ _ _)    = refl

-- both are `map` laws once the elements obey them
mapLayout-id : ∀ {S} (l : Layout S) → mapLayout id l ≡ l
mapLayout-id (mkLayout w h ds as) =
  cong₂ (mkLayout w h) (trans (ListP.map-cong mapDraw-id ds) (ListP.map-id ds)) (ListP.map-id as)

mapLayout-∘ : ∀ {S T U} (g : T → U) (f : S → T) (l : Layout S) →
              mapLayout g (mapLayout f l) ≡ mapLayout (g ∘ f) l
mapLayout-∘ g f (mkLayout w h ds as) =
  cong₂ (mkLayout _ _) (trans (sym (ListP.map-∘ ds)) (ListP.map-cong (mapDraw-∘ g f) ds))
        (trans (sym (ListP.map-∘ as)) (ListP.map-cong (λ _ → refl) as))
