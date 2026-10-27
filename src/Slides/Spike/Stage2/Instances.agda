{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The lifting lemma (`Lift.lifting-lemma′`) instantiated at the diagram algebras of the library.
-- An instance costs its extensionality proof (`*-ext`: 14 clauses, `cong` on each operation;
-- without funext this is what the setoid `Func.cong` of `Container.Sum.copair` would also ask)
-- and one line.  Compile time of this module (generic lemma at layout and at names) is measured
-- in docs/Stage2.md.

module Slides.Spike.Stage2.Instances where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe)
import Data.Maybe as Maybe
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram.Syntax
open import Slides.Diagram.Names using (namesAlgebra; Usage)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Spike.Timed using (fin2)
open import Slides.Spike.Timed.Layout using (layout-ext)
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.Lift

open LayoutWith ratOps using (layoutAlgebra; layout)

-- LAYOUT: what a closed scene shows at τ, laid out, is the layout of the diagram it shows
layout-at′ : ∀ (t : Scene ℚ) τ →
  proj₂ (sample layoutAlgebra (λ _ x → x) t) τ
  ≡ Maybe.map layout (proj₂ (sample (λ o k → impure (o , k)) (λ _ d → d) t) τ)
layout-at′ t τ = at≡ (lifting-lemma′ layoutAlgebra (λ _ x → x) (λ _ d → d) (λ _ _ → refl) layout-ext t) τ

-- NAMES
names-ext : ∀ {S} o {x y : arity o → Usage} → (∀ i → x i ≡ y i) → namesAlgebra {S} o x ≡ namesAlgebra o y
names-ext {S} (Rectangle _ _ _)   p = refl
names-ext {S} (Disc _ _)          p = refl
names-ext {S} (Segment _ _ _)     p = refl
names-ext {S} (Text _ _ _ _)      p = refl
names-ext {S} (Spacer _ _)        p = refl
names-ext {S} (Beside al)         p = cong₂ (λ a b → namesAlgebra {S} (Beside al) (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} (Above al)          p = cong₂ (λ a b → namesAlgebra {S} (Above al) (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} Atop                p = cong₂ (λ a b → namesAlgebra {S} Atop (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} LabelAbove          p = cong₂ (λ a b → namesAlgebra {S} LabelAbove (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} LabelBelow          p = cong₂ (λ a b → namesAlgebra {S} LabelBelow (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} (Place w h x y)     p = cong (λ u → namesAlgebra {S} (Place w h x y) (λ _ → u)) (p tt)
names-ext {S} (Overlay w h)       p = cong₂ (λ a b → namesAlgebra {S} (Overlay w h) (fin2 a b)) (p zero) (p (suc zero))
names-ext {S} (Named n)           p = cong (λ u → namesAlgebra {S} (Named n) (λ _ → u)) (p tt)
names-ext {S} (Connect a pa b pb s) p = cong (λ u → namesAlgebra {S} (Connect a pa b pb s) (λ _ → u)) (p tt)

-- the names a scene declares at τ are the names of the diagram it shows at τ
names-at : ∀ {S} (t : Scene S) τ →
  proj₂ (sample namesAlgebra (λ _ u → u) t) τ
  ≡ Maybe.map (fold namesAlgebra) (proj₂ (sample (λ o k → impure (o , k)) (λ _ d → d) t) τ)
names-at t τ = at≡ (lifting-lemma′ namesAlgebra (λ _ u → u) (λ _ d → d) (λ _ _ → refl) names-ext t) τ
