{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The static instance: the footprint of a scene (the names its frames declare, over all time) is a
-- plain `cata` into `Usage`, the third kind of reading next to `sample` (Timed) and the list
-- timeline.  Seq and Par take the union, the unary temporal operations pass the child through,
-- the diagram operations are `namesAlgebra`.  For the embedding it is the existing
-- `Slides.Anim.Footprint.footprint`.

module Slides.Spike.Stage2.Footprint where

open import Data.Fin using (zero; suc)
open import Data.List using (List; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Container.Core using (Shape; Position)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram.Expr using (Expr)
open import Slides.Diagram.Names using (Usage; namesAlgebra)
open import Slides.Diagram.Syntax using (Dia; fold)
import Slides.Anim.Syntax as A
import Slides.Anim.Footprint as F
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.Instances using (names-ext)
open import Data.Rational using (ℚ)
open import Data.Unit using (⊤)

private
  both : Usage → Usage → Usage
  both (d , r) (d′ , r′) = d ++ d′ , r ++ r′

timeNames : (s : Shape TimeC) → (Position TimeC s → Usage) → Usage
timeNames Seq        k = both (k zero) (k (suc zero))
timeNames Par        k = both (k zero) (k (suc zero))
timeNames (Hold _)   k = k tt
timeNames (Delay _)  k = k tt
timeNames (Repeat _) k = k tt
timeNames (Drive _)  k = k tt

usage : ∀ {S} → Scene S → Usage
usage = cata (copairAlg timeNames namesAlgebra)

-- a diagram folded as a scene is folded
usage-inj : ∀ {S} (d : Dia S) → usage (inj d) ≡ fold namesAlgebra d
usage-inj (pure ())
usage-inj (impure (o , k)) = names-ext o (λ i → usage-inj (k i))

-- the existing footprint is the declared names of the scene
footprint-embed : ∀ t → proj₁ (usage (embed t)) ≡ F.footprint (toAnim t)
footprint-embed (pure (tr , d))       = cong proj₁ (usage-inj d)
footprint-embed (impure (A.Seq , k))  = cong₂ _++_ (footprint-embed (k zero)) (footprint-embed (k (suc zero)))
footprint-embed (impure (A.Par , k))  = cong₂ _++_ (footprint-embed (k zero)) (footprint-embed (k (suc zero)))
