{-# OPTIONS --safe --without-K #-}

-- Structural properties of the rendering shared by the HTML backends: rendering is a monoid
-- homomorphism from programs under sequencing to forests under concatenation.
module Slides.Backend.Common.Properties where

open import Data.List using (_++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Container.FreeMonad as FM
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)

open import Slides.Core
open import Slides.Backend.Common

------------------------------------------------------------------------
-- Structural properties

-- Rendering is a monoid homomorphism: sequencing programs concatenates the
-- markup.  (The fold of a program is the markup of its first command followed
-- by the fold of the rest, and the leaf contributes nothing.)
renderBody-bind : ∀ (b₁ b₂ : Body) →
                  renderBody (b₁ FM.>>= λ _ → b₂) ≡ renderBody b₁ ++ renderBody b₂
renderBody-bind (pure tt)             b₂ = refl
renderBody-bind (impure (inj₁ c , k)) b₂ =
  trans (cong (renderContent c ++_) (renderBody-bind (k tt) b₂))
        (sym (++-assoc (renderContent c) (renderBody (k tt)) (renderBody b₂)))
renderBody-bind (impure (inj₂ c , k)) b₂ =
  trans (cong (renderLayout c ++_) (renderBody-bind (k tt) b₂))
        (sym (++-assoc (renderLayout c) (renderBody (k tt)) (renderBody b₂)))
