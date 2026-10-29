{-# OPTIONS --safe --without-K #-}

-- Looking down the axis moves nothing: the view `flat` (the turns by tangent 0) is the identity.

module Slides.Three.Properties where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _≃_; _*_; _+_; _-_)
open import Data.Rational.Unnormalised.Properties

open import Slides.Three.Point
open import Slides.Three.View

-- the turn by 0 moves nothing
act-id : ∀ x y → (proj₁ (act (1ℚᵘ , 0ℚᵘ) (x , y)) ≃ x) × (proj₂ (act (1ℚᵘ , 0ℚᵘ) (x , y)) ≃ y)
act-id x y = ≃-trans (+-cong (*-identityˡ x) (-‿cong (*-zeroˡ y))) (+-identityʳ x)
           , ≃-trans (+-cong (*-zeroˡ x) (*-identityˡ y)) (+-identityˡ y)

rotate-id : ∀ x y z → let q = rotate (view (1ℚᵘ , 0ℚᵘ) (1ℚᵘ , 0ℚᵘ)) (point x y z) in (Point.x q ≃ x) × (Point.y q ≃ y) × (Point.z q ≃ z)
rotate-id x y z = ≃-trans (proj₁ (act-id x₁ y)) (proj₁ (act-id x z)) , proj₂ (act-id x₁ y) , proj₂ (act-id x z)
  where x₁ = proj₁ (act (1ℚᵘ , 0ℚᵘ) (x , z))

-- `flat` is that view, by computation: tangent 0 = (1 , 0)
rotate-flat : ∀ x y z → let q = rotate flat (point x y z) in (Point.x q ≃ x) × (Point.y q ≃ y) × (Point.z q ≃ z)
rotate-flat = rotate-id
