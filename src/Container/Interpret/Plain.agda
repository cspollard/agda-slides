{-# OPTIONS --safe --without-K #-}

-- Plain folds: the curried form of a fold, with its laws stated once.
--
--   Handler A = (a : Shape C) → (Position C a → A) → A       one clause per command
--   pfold h leaf : C ⋆ X → A                                 the fold of a handler
--
-- `pfold` is the one fold: a `Congruent` handler is an `⟦ C ⟧`-algebra (`handler`, `handler-congruent`)
-- and `Container.FreeMonad.Algebraic.fold` is defined as `pfold` of it.  Laws, so no language
-- re-proves them:
--
-- * `pfold-ext`, `pfold-cong`: pointwise-equal leaves, or equal programs (`_≈⋆_`), give equal folds
--   (`pfold-cong′`: equal programs over any setoid of leaves);
-- * `pfold-bind`: folding a substitution is folding with the substituted programs folded;
-- * `pfold-hom`: a map commuting with each command, up to a lowering, commutes with the fold;
-- * `pfold-translate`: folding a translation is folding with the pulled-back handler (`pull`);
-- * `pfold-rel`, `pfold-rel-translate`: related handlers give related folds (logical relations).

module Container.Interpret.Plain where

open import Level using (Level; _⊔_; 0ℓ; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Polynomial using (Poly₀)
open import Container.FreeMonad using (Eq)
open import Container.Lowering

private
  variable
    s p x y r : Level

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

    -- Folds respect equality of programs, over any setoid of leaves on which `f` is congruent.
    pfold-cong′ : ∀ {X : Setoid x r} {f : Setoid.Carrier X → A.Carrier} →
                  (∀ {u v} → Setoid._≈_ X u v → f u A.≈ f v) →
                  ∀ {t u : C ⋆ Setoid.Carrier X} → Eq X t u → pfold C h f t A.≈ pfold C h f u
    pfold-cong′ fc {pure _}         {pure _}           (lift e)    = fc e
    pfold-cong′ fc {pure _}         {impure _}         ()
    pfold-cong′ fc {impure _}       {pure _}           ()
    pfold-cong′ fc {impure (a , k)} {impure (.a , k′)} (refl , e)  =
      c a (λ q → pfold-cong′ fc (e q))

    -- ... in particular over a set of leaves (propositional equality).
    pfold-cong : ∀ {X : Set x} {f : X → A.Carrier} {t u : C ⋆ X} → t ≈⋆ u →
                 pfold C h f t A.≈ pfold C h f u
    pfold-cong = pfold-cong′ {X = ≡P.setoid _} (λ { refl → A.refl })

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

-- A congruent handler is an algebra of the polynomial functor, and the other way round.

module _ {C : Container s p} {a ℓ} {A : Setoid a ℓ} where
  handler : Func (Poly₀ C A) A → Handler C (Setoid.Carrier A)
  handler α c k = α ⟨$⟩ (c , k)

  handler-congruent : (α : Func (Poly₀ C A) A) → Congruent C A (handler α)
  handler-congruent α c k≈ = Func.cong α (refl ,ₚ k≈)
