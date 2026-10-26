{-# OPTIONS --safe --without-K #-}

-- The names a diagram declares do not depend on its sizes.  (That `dangling` is sound is
-- `Slides.Diagram.Names.Properties.Soundness`.)
module Slides.Diagram.Names.Properties where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Diagram.Syntax
open import Slides.Diagram.Names

-- the names a diagram uses do not depend on its sizes: changing the scalar leaves them alone
names-mapDia : ∀ {S T} (f : S → T) (d : Dia S) → fold namesAlgebra (mapDia f d) ≡ fold namesAlgebra d
names-mapDia f (pure ())
names-mapDia f (impure (Rectangle _ _ _ , k))  = refl
names-mapDia f (impure (Disc _ _ , k))         = refl
names-mapDia f (impure (Segment _ _ _ , k))    = refl
names-mapDia f (impure (Text _ _ _ _ , k))     = refl
names-mapDia f (impure (Spacer _ _ , k))       = refl
names-mapDia f (impure (Beside _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Above _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Atop , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (LabelAbove , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (LabelBelow , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Overlay _ _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Place _ _ _ _ , k))
  rewrite names-mapDia f (k tt) = refl
names-mapDia f (impure (Named n , k))
  rewrite names-mapDia f (k tt) = refl
names-mapDia f (impure (Connect a _ b _ _ , k))
  rewrite names-mapDia f (k tt) = refl
