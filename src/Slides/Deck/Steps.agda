{-# OPTIONS --safe --without-K #-}

-- Steps: the fragments a slide's page steps through, counted on the syntax.
--
-- Both backends reveal a slide one `.fragment` at a time (`assets/plain.js`, reveal.js), in document
-- order.  The renderer (`Slides.Backend.Render`) emits one for
--   * each later chunk that has something to show (`wraps`),
--   * each `fragment` block, and each `classed` block whose class has the token `fragment`,
--   * each item of an incremental bullet tree, nested items included,
--   * each rest of an animation.
-- `flowSteps` counts the last three: a monoid homomorphism from flows under `++` to `(ℕ, +, 0)`.
-- A chunk after the first also contributes its wrapper, but only when it holds a block that is not
-- an aside (a note or script), so `wraps` is not additive: it is `⊔` (`wraps-++`).
--
--   `chunkSteps (c ∷ cs)`   steps of a slide: those of `c`, then `wraps d + flowSteps d` per later chunk `d`
--   `gap c d`               the step at which chunk `d` appears after chunk `c` has: `flowSteps c + wraps d`
-- A slide has `1 + chunkSteps` states (`Slides.Deck.Syntax.ticks`); the first is the first chunk with
-- nothing revealed.  `Slides.Backend.Render.Properties.render-fragments` proves the count against the page.

module Slides.Deck.Steps where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n)
open import Data.String using (String; words; _==_)
open import Algebra.Morphism.Structures using (module MagmaMorphisms; module MonoidMorphisms)
open import Algebra.Bundles using (Monoid)
import Data.List.Properties as ListP
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Deck.Content
open import Slides.Deck.Anim using (rests)

-- 1 when `fragment` is one of the class tokens
fragClass : String → ℕ
fragClass c = if any (_== "fragment") (words c) then 1 else 0

mutual
  bulletSteps : Bullet → ℕ
  bulletSteps (bullet _ cs) = suc (bulletsSteps cs)

  bulletsSteps : List Bullet → ℕ
  bulletsSteps []       = 0
  bulletsSteps (b ∷ bs) = bulletSteps b + bulletsSteps bs

mutual
  blockSteps : Block → ℕ
  blockSteps (bulletTree inc is)            = if inc then bulletsSteps is else 0
  blockSteps (animation _ _ _ as)           = length (rests as)
  blockSteps (animationBoth _ _ _ _ _ rs)   = length rs
  blockSteps (columns cs)                   = columnsSteps cs
  blockSteps (box _ f)                      = flowSteps f
  blockSteps (fragment _ f)                 = suc (flowSteps f)
  blockSteps (classed c f)                  = fragClass c + flowSteps f
  blockSteps (placed _ _ _ _ f)             = flowSteps f
  blockSteps (heading _ _)                  = 0
  blockSteps (paragraph _)                  = 0
  blockSteps (code _ _)                     = 0
  blockSteps (displayMath _)                = 0
  blockSteps (figure _ _ _)                 = 0
  blockSteps (notes _)                      = 0
  blockSteps (table _ _)                    = 0
  blockSteps (references _)                 = 0
  blockSteps (diagram _ _ _)                = 0
  blockSteps (animationLoop _ _ _ _)        = 0
  blockSteps (still _ _ _)                  = 0
  blockSteps (script _)                     = 0
  blockSteps (mount _)                      = 0

  flowSteps : Flow → ℕ
  flowSteps []       = 0
  flowSteps (b ∷ bs) = blockSteps b + flowSteps bs

  columnsSteps : List Flow → ℕ
  columnsSteps []       = 0
  columnsSteps (f ∷ fs) = flowSteps f + columnsSteps fs

flowSteps-++ : ∀ xs ys → flowSteps (xs ++ ys) ≡ flowSteps xs + flowSteps ys
flowSteps-++ []       ys = refl
flowSteps-++ (b ∷ xs) ys = trans (cong (blockSteps b +_) (flowSteps-++ xs ys)) (sym (ℕP.+-assoc (blockSteps b) _ _))

-- `flowSteps` is a monoid homomorphism
module _ where
  open MonoidMorphisms (Monoid.rawMonoid (ListP.++-monoid Block)) (Monoid.rawMonoid ℕP.+-0-monoid)
  open MagmaMorphisms (Monoid.rawMagma (ListP.++-monoid Block)) (Monoid.rawMagma ℕP.+-0-monoid)

  flowSteps-isMonoidHomomorphism : IsMonoidHomomorphism flowSteps
  flowSteps-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = cong flowSteps }
        ; homo = flowSteps-++ }
    ; ε-homo = refl }

-- notes and scripts are never inside a chunk's fragment
aside? : Block → Bool
aside? (notes _)  = true
aside? (script _) = true
aside? _          = false

-- 1 when a later chunk has a block to wrap in its fragment
wraps : Flow → ℕ
wraps []       = 0
wraps (b ∷ bs) = if aside? b then wraps bs else 1

wraps-≤1 : ∀ f → wraps f ≤ 1
wraps-≤1 []       = z≤n
wraps-≤1 (b ∷ xs) with aside? b
... | true  = wraps-≤1 xs
... | false = ℕP.≤-refl

wraps-++ : ∀ xs ys → wraps (xs ++ ys) ≡ wraps xs ⊔ wraps ys
wraps-++ []       ys = refl
wraps-++ (b ∷ xs) ys with aside? b
... | true  = wraps-++ xs ys
... | false = sym (ℕP.m≥n⇒m⊔n≡m (wraps-≤1 ys))

-- the step at which chunk `d` appears once chunk `c` has: after `c`'s own steps, `d`'s wrapper
gap : Flow → Flow → ℕ
gap c d = flowSteps c + wraps d

laterSteps : List Flow → ℕ
laterSteps []       = 0
laterSteps (d ∷ ds) = wraps d + flowSteps d + laterSteps ds

-- the steps of a slide, whose chunks are `c ∷ cs`
chunkSteps : List⁺ Flow → ℕ
chunkSteps (c ∷ cs) = flowSteps c + laterSteps cs

-- the gaps add up to the steps: chunk `d` appears at `gap c d`, then `d` and the rest follow
chunkSteps-gap : ∀ c d ds → chunkSteps (c ∷ d ∷ ds) ≡ gap c d + chunkSteps (d ∷ ds)
chunkSteps-gap c d ds =
  trans (cong (flowSteps c +_) (ℕP.+-assoc (wraps d) (flowSteps d) (laterSteps ds)))
        (sym (ℕP.+-assoc (flowSteps c) (wraps d) _))
