{-# OPTIONS --safe --without-K #-}

-- A change of scalar is a functor: `mapDia` and `mapLayout` preserve identities and composition.
--
--   mapDia id ≈ id          mapDia (g ∘ f) ≈ mapDia g ∘ mapDia f          (equality of programs)
--   mapLayout id ≡ id       mapLayout (g ∘ f) ≡ mapLayout g ∘ mapLayout f
--
-- `mapDia f = translate (mapC f)`, so these say that `mapC` is a functor into the container
-- morphisms, one clause per command (`Container.Lowering.Translate` has the generic laws).  Folding
-- along a map is folding with the pulled-back handler (`fold-mapDia`, an instance of `pfold-translate`).
-- Not stated: congruence in the map (`f ≗ g` gives equal results) needs no more than these cases.

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
open import Slides.Diagram.Draw
open import Slides.Diagram.Syntax

------------------------------------------------------------------------
-- Diagrams

mapDia-id : ∀ {S} (t : Dia S) → mapDia id t ≈⋆ t
mapDia-id (pure ())
mapDia-id (impure (Rectangle _ _ _ , k))   = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Segment _ _ _ , k))     = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Disc _ _ , k))          = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Text _ _ _ _ _ , k))    = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Path _ _ _ _ , k))      = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Spacer _ _ , k))        = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Beside _ , k))          = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Above _ , k))           = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Atop , k))              = refl , λ q → mapDia-id (k q)
mapDia-id (impure (LabelAbove , k))        = refl , λ q → mapDia-id (k q)
mapDia-id (impure (LabelBelow , k))        = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Place _ _ _ _ , k))     = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Overlay _ _ , k))       = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Named _ , k))           = refl , λ q → mapDia-id (k q)
mapDia-id (impure (Connect _ _ _ _ _ , k)) = refl , λ q → mapDia-id (k q)

mapDia-∘ : ∀ {S T U} (g : T → U) (f : S → T) (t : Dia S) → mapDia g (mapDia f t) ≈⋆ mapDia (g ∘ f) t
mapDia-∘ g f (pure ())
mapDia-∘ g f (impure (Rectangle _ _ _ , k))   = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Segment _ _ _ , k))     = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Disc _ _ , k))          = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Text _ _ _ _ _ , k))    = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Path _ _ _ _ , k))      = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Spacer _ _ , k))        = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Beside _ , k))          = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Above _ , k))           = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Atop , k))              = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (LabelAbove , k))        = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (LabelBelow , k))        = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Place _ _ _ _ , k))     = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Overlay _ _ , k))       = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Named _ , k))           = refl , λ q → mapDia-∘ g f (k q)
mapDia-∘ g f (impure (Connect _ _ _ _ _ , k)) = refl , λ q → mapDia-∘ g f (k q)

-- Folding after a change of scalar is folding the original with the handler pulled back along `mapC f`.
fold-mapDia : ∀ {S T a ℓ} (f : S → T) (A : Setoid a ℓ) {h : Handler (DiagramC T) (Setoid.Carrier A)}
              (c : Congruent (DiagramC T) A h) (t : Dia S) →
              Setoid._≈_ A (pfold (DiagramC T) h (λ ()) (mapDia f t)) (pfold (DiagramC S) (pull (mapC f) h) (λ ()) t)
fold-mapDia f A c t = pfold-translate (mapC f) A c {X = ⊥} {f = λ ()} t

------------------------------------------------------------------------
-- Layouts

mutual
  mapDraw-id : ∀ {S} (d : Draw S) → mapDraw id d ≡ d
  mapDraw-id (rect _ _ _ _ _)  = refl
  mapDraw-id (circle _ _ _ _)  = refl
  mapDraw-id (line _ _ _ _ _)  = refl
  mapDraw-id (arrow _ _ _ _ _) = refl
  mapDraw-id (label _ _ _ _ _) = refl
  mapDraw-id (path _ _ _ _)    = refl
  mapDraw-id (group x y ds)    = cong (group x y) (mapDraws-id ds)

  mapDraws-id : ∀ {S} (ds : List (Draw S)) → mapDraws id ds ≡ ds
  mapDraws-id []       = refl
  mapDraws-id (d ∷ ds) = cong₂ _∷_ (mapDraw-id d) (mapDraws-id ds)

mapLayout-id : ∀ {S} (l : Layout S) → mapLayout id l ≡ l
mapLayout-id (mkLayout w h ds as) =
  cong₂ (mkLayout w h) (mapDraws-id ds) (ListP.map-id as)

mutual
  mapDraw-∘ : ∀ {S T U} (g : T → U) (f : S → T) (d : Draw S) → mapDraw g (mapDraw f d) ≡ mapDraw (g ∘ f) d
  mapDraw-∘ g f (rect _ _ _ _ _)  = refl
  mapDraw-∘ g f (circle _ _ _ _)  = refl
  mapDraw-∘ g f (line _ _ _ _ _)  = refl
  mapDraw-∘ g f (arrow _ _ _ _ _) = refl
  mapDraw-∘ g f (label _ _ _ _ _) = refl
  mapDraw-∘ g f (path _ _ _ _)    = refl
  mapDraw-∘ g f (group x y ds)    = cong (group _ _) (mapDraws-∘ g f ds)

  mapDraws-∘ : ∀ {S T U} (g : T → U) (f : S → T) (ds : List (Draw S)) →
               mapDraws g (mapDraws f ds) ≡ mapDraws (g ∘ f) ds
  mapDraws-∘ g f []       = refl
  mapDraws-∘ g f (d ∷ ds) = cong₂ _∷_ (mapDraw-∘ g f d) (mapDraws-∘ g f ds)

mapLayout-∘ : ∀ {S T U} (g : T → U) (f : S → T) (l : Layout S) →
              mapLayout g (mapLayout f l) ≡ mapLayout (g ∘ f) l
mapLayout-∘ g f (mkLayout w h ds as) =
  cong₂ (mkLayout _ _) (mapDraws-∘ g f ds)
        (trans (sym (ListP.map-∘ as)) (ListP.map-cong (λ _ → refl) as))
