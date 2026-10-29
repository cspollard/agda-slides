{-# OPTIONS --safe --without-K #-}

-- Plain folds: the curried form of a fold, and its laws, stated once.
--
-- A language over a container `C` is usually interpreted by one handler per command,
-- `(a : Shape C) → (Position C a → A) → A`, and a map from leaves.  `pfold` is that fold.
-- When the handler respects pointwise-equal children (`Congruent`) it is an
-- `⟦ C ⟧`-algebra and `pfold` is `Container.FreeMonad.Algebraic.fold` (`pfold-agrees`).  The
-- laws below are the ones every language re-proved for itself:
--
-- * congruence: pointwise-equal leaves, or equal programs, give equal folds;
-- * the bind law: folding a substitution is folding with the substituted programs folded
--   (`pfold-bind`); for a handler into a monoid this is the statement that the fold of a
--   bind is the fold with the continuation folded;
-- * homomorphisms of handlers, up to a lowering of the source (`pfold-hom`); fusion along a
--   lowering or a morphism is the case `φ = id` with the pulled-back handler;
-- * related handlers give related folds (`pfold-rel`, and along a morphism `pfold-rel-translate`).
--
-- Equality of programs is `_≈⋆_` (propositional equality of leaves).

module Container.Interpret.Plain where

open import Level using (Level; _⊔_; 0ℓ; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Container.Lowering

private
  variable
    s p x y : Level

module _ (C : Container s p) where

  -- One handler per command, given the results for its positions.
  Handler : ∀ {a} → Set a → Set (s ⊔ p ⊔ a)
  Handler A = (a : Shape C) → (Position C a → A) → A

  pfold : ∀ {a} {A : Set a} {X : Set x} → Handler A → (X → A) → C ⋆ X → A
  pfold h leaf (pure v)         = leaf v
  pfold h leaf (impure (a , k)) = h a (λ q → pfold h leaf (k q))

  -- Handlers that respect pointwise-equal children.
  Congruent : ∀ {a ℓ} (A : Setoid a ℓ) → Handler (Setoid.Carrier A) → Set (s ⊔ p ⊔ a ⊔ ℓ)
  Congruent A h = ∀ a {k k′} → (∀ q → k q ≈ k′ q) → h a k ≈ h a k′
    where open Setoid A using (_≈_)

module _ {C : Container s p} {a ℓ} (A : Setoid a ℓ) where
  private module A = Setoid A

  module _ {h : Handler C A.Carrier} (c : Congruent C A h) where

    -- Folds with pointwise-equal leaves agree.
    pfold-ext : ∀ {X : Set x} {f g : X → A.Carrier} → (∀ v → f v A.≈ g v) → ∀ t →
                pfold C h f t A.≈ pfold C h g t
    pfold-ext e (pure v)         = e v
    pfold-ext e (impure (_ , k)) = c _ (λ q → pfold-ext e (k q))

    -- Folds respect equality of programs.
    pfold-cong : ∀ {X : Set x} {f : X → A.Carrier} {t u : C ⋆ X} → t ≈⋆ u →
                 pfold C h f t A.≈ pfold C h f u
    pfold-cong {t = pure _}         {pure _}           (lift refl) = A.refl
    pfold-cong {t = pure _}         {impure _}         ()
    pfold-cong {t = impure _}       {pure _}           ()
    pfold-cong {t = impure (a , k)} {impure (.a , k′)} (refl , e)     =
      c a (λ q → pfold-cong (e q))

    -- The bind law.
    pfold-bind : ∀ {X : Set x} {Y : Set y} {f : X → A.Carrier} {f′ : Y → A.Carrier}
                 (g : Y → C ⋆ X) → (∀ y → pfold C h f (g y) A.≈ f′ y) →
                 ∀ t → pfold C h f (t >>= g) A.≈ pfold C h f′ t
    pfold-bind g e (pure y)         = e y
    pfold-bind g e (impure (_ , k)) = c _ (λ q → pfold-bind g e (k q))

    -- Homomorphisms of handlers: a function `φ` that commutes with each command, up to the
    -- lowering `l` of the source command into the target language, commutes with the fold.
    -- The fusion laws below, and digitisation, are instances.
    pfold-hom : ∀ {α} {A : Set α} {X : Set x} {D : Container s p} (φ : A → A.Carrier)
                (hA : Handler D A) (l : Lowering D C) →
                (∀ a k → φ (hA a k) A.≈ pfold C h (λ q → φ (k q)) (l a)) →
                ∀ (f : X → A) t → φ (pfold D hA f t) A.≈ pfold C h (λ v → φ (f v)) (lower l t)
    pfold-hom φ hA l hom f (pure _)         = A.refl
    pfold-hom φ hA l hom f (impure (a , k)) =
      A.trans (hom a _) (A.sym (pfold-bind (λ q → lower l (k q))
                                           (λ q → A.sym (pfold-hom φ hA l hom f (k q))) (l a)))

-- Folds preserve a relation: if two handlers send related children to related results then
-- they send related programs to related results (the fundamental lemma of logical relations).
-- A handler homomorphism `φ (hA c k) ≡ hB c (φ ∘ k)` is the case `R x y = φ x ≡ y`; "the names
-- of a layout are the names the usage fold declares" and "layout is natural in the scalar" are
-- this lemma once each.

module _ {C : Container s p} {a b r} {A : Set a} {B : Set b} (R : A → B → Set r)
         {hA : Handler C A} {hB : Handler C B}
         (hom : ∀ c k k′ → (∀ q → R (k q) (k′ q)) → R (hA c k) (hB c k′)) where

  pfold-rel : ∀ {X : Set x} {f : X → A} {g : X → B} → (∀ v → R (f v) (g v)) → ∀ t →
              R (pfold C hA f t) (pfold C hB g t)
  pfold-rel e (pure v)         = e v
  pfold-rel e (impure (c , k)) = hom c _ _ (λ q → pfold-rel e (k q))

-- The same along a container morphism `m`, the second program being the translation of the first.
-- The commutation is stated against the handler pulled back along `m`, so no congruence is needed.
-- (The identity morphism gives `pfold-rel` up to `translate-id`.)

module _ {C D : Container s p} (m : C ⇒ D) {a b r} {A : Set a} {B : Set b} (R : A → B → Set r)
         {hA : Handler C A} {hB : Handler D B}
         (hom : ∀ c (k : Position C c → A) (k′ : Position C c → B) → (∀ q → R (k q) (k′ q)) →
               R (hA c k) (hB (shape m c) (λ q → k′ (position m q)))) where

  pfold-rel-translate : ∀ {X : Set x} {f : X → A} {g : X → B} → (∀ v → R (f v) (g v)) → ∀ t →
                        R (pfold C hA f t) (pfold D hB g (translate m t))
  pfold-rel-translate e (pure v)         = e v
  pfold-rel-translate e (impure (c , k)) =
    hom c (λ q → pfold C hA _ (k q)) (λ q → pfold D hB _ (translate m (k q))) (λ q → pfold-rel-translate e (k q))

-- Fusion of a fold with a translation: folding the translation along `m` is folding the original with
-- the handler pulled back along `m`.  (Digitising, renaming and a change of scalar are instances.)

pull : ∀ {C D : Container s p} {a} {A : Set a} → C ⇒ D → Handler D A → Handler C A
pull m h c k = h (shape m c) (λ q → k (position m q))

module _ {C D : Container s p} (m : C ⇒ D) {a ℓ} (A : Setoid a ℓ) {h : Handler D (Setoid.Carrier A)}
         (c : Congruent D A h) {X : Set x} {f : X → Setoid.Carrier A} where

  pfold-translate : ∀ t → Setoid._≈_ A (pfold D h f (translate m t)) (pfold C (pull m h) f t)
  pfold-translate (pure v)         = Setoid.refl A
  pfold-translate (impure (a , k)) = c (shape m a) (λ q → pfold-translate (k (position m q)))

-- A congruent handler is an algebra of the polynomial functor, and `pfold` is its fold.

module _ (C : Container s p) (A : Setoid (s ⊔ p) (s ⊔ p)) where
  private
    module A = Setoid A
    module G = Alg 0ℓ 0ℓ C

  toAlgebra : (h : Handler C A.Carrier) → Congruent C A h → F-Algebra G.F
  toAlgebra h c = record
    { A = A
    ; α = record
        { to   = λ { (a , k) → h a k }
        ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → c _ k≈ } } }

  module _ (h : Handler C A.Carrier) (c : Congruent C A h) {X : Set (s ⊔ p)}
           (f : X → A.Carrier) where
    leafFunc : Func (≡P.setoid X) A
    leafFunc = record { to = f ; cong = λ e → A.reflexive (cong f e) }

    pfold-agrees : (t : C ⋆ X) → pfold C h f t A.≈ G.fold (toAlgebra h c) leafFunc t
    pfold-agrees (pure _)         = A.refl
    pfold-agrees (impure (a , k)) = c a (λ q → pfold-agrees (k q))
