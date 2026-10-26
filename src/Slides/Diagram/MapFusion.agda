{-# OPTIONS --safe --without-K #-}

-- Changing the scalar of a diagram is translation along a container morphism.
--
-- `mapDia f` rebuilds every operation with its sizes sent through `f : S → T`
-- (`Slides.Diagram.Syntax.rescale`).  The operations change but their arities do
-- not, so `mapOp f : Op S → Op T` with the identity on positions is a container
-- morphism `scalarMor f : DiagramC S ⇒ DiagramC T`, and `mapDia f` is translation
-- along it (`mapDia-translate`, equality of programs, `_≈⋆_`).  The generic theory
-- (`Container.Lowering`) then gives what is true of `mapDia`:
--
--   * functoriality: `mapDia id d ≈⋆ d` and `mapDia g (mapDia f d) ≈⋆ mapDia (g ∘ f) d`
--     (equality of programs; `mapDia` is an action only up to the equality of
--     children as functions, since `pick2` is not `k` itself);
--   * fusion: folding a rescaled diagram is folding the original with the algebra
--     pulled back along the morphism (`pull`, `fold-translate`, `fold-mapDia`):
--       fold α (mapDia f d) ≈ fold (pull (scalarMor f) α) d
--     for any renderer `α` whose handlers respect pointwise-equal children
--     (`Congruent`, as in `Slides.Diagram.Generic`).  The pullback is the same
--     renderer applied to the operation with rescaled sizes; no function
--     extensionality is needed.
--
-- What does not follow is a pullback of `Layout` along `f` unless `f` is a ring
-- homomorphism that respects the layout's order, since `⊔` and centring are
-- computed in the target scalar (`Slides.Diagram.Laws`); that is outside this module.

module Slides.Diagram.MapFusion where

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Data.Container.Core using (_⇒_; _▷_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (refl)
open import Function using (id; _∘_)

open import Container.Lowering using (_≈⋆_; translate; lower; embed; lower-embed; sym≈; trans≈)
open import Slides.Diagram.Syntax

------------------------------------------------------------------------
-- The container morphism

mapOp : ∀ {S T} → (S → T) → Op S → Op T
mapOp f (Rectangle w h s)     = Rectangle (f w) (f h) s
mapOp f (Disc r s)            = Disc (f r) s
mapOp f (Segment w h s)       = Segment (f w) (f h) s
mapOp f (Text pct size t s)   = Text pct size t s
mapOp f (Spacer w h)          = Spacer (f w) (f h)
mapOp f (Beside al)           = Beside al
mapOp f (Above al)            = Above al
mapOp f Atop                  = Atop
mapOp f LabelAbove            = LabelAbove
mapOp f LabelBelow            = LabelBelow
mapOp f (Named n)             = Named n
mapOp f (Connect a pa b pb s) = Connect a pa b pb s

-- positions are unchanged (the arity of `mapOp f o` is that of `o`, by cases)
posOf : ∀ {S T} (f : S → T) (o : Op S) → arity (mapOp f o) → arity o
posOf f (Rectangle _ _ _)   x = x
posOf f (Disc _ _)          x = x
posOf f (Segment _ _ _)     x = x
posOf f (Text _ _ _ _)      x = x
posOf f (Spacer _ _)        x = x
posOf f (Beside _)          x = x
posOf f (Above _)           x = x
posOf f Atop                x = x
posOf f LabelAbove          x = x
posOf f LabelBelow          x = x
posOf f (Named _)           x = x
posOf f (Connect _ _ _ _ _) x = x

scalarMor : ∀ {S T} → (S → T) → DiagramC S ⇒ DiagramC T
scalarMor f = mapOp f ▷ λ {o} → posOf f o

------------------------------------------------------------------------
-- `mapDia` is translation along it

mapDia-translate : ∀ {S T} (f : S → T) (d : Dia S) → mapDia f d ≈⋆ translate (scalarMor f) d
mapDia-translate f (impure (Rectangle w h s , k))     = refl , λ ()
mapDia-translate f (impure (Disc r s , k))            = refl , λ ()
mapDia-translate f (impure (Segment w h s , k))       = refl , λ ()
mapDia-translate f (impure (Text pct size t s , k))   = refl , λ ()
mapDia-translate f (impure (Spacer w h , k))          = refl , λ ()
mapDia-translate f (impure (Beside al , k))           = refl , λ { zero → mapDia-translate f (k zero) ; (suc zero) → mapDia-translate f (k (suc zero)) }
mapDia-translate f (impure (Above al , k))            = refl , λ { zero → mapDia-translate f (k zero) ; (suc zero) → mapDia-translate f (k (suc zero)) }
mapDia-translate f (impure (Atop , k))                = refl , λ { zero → mapDia-translate f (k zero) ; (suc zero) → mapDia-translate f (k (suc zero)) }
mapDia-translate f (impure (LabelAbove , k))          = refl , λ { zero → mapDia-translate f (k zero) ; (suc zero) → mapDia-translate f (k (suc zero)) }
mapDia-translate f (impure (LabelBelow , k))          = refl , λ { zero → mapDia-translate f (k zero) ; (suc zero) → mapDia-translate f (k (suc zero)) }
mapDia-translate f (impure (Named n , k))             = refl , λ _ → mapDia-translate f (k tt)
mapDia-translate f (impure (Connect a pa b pb s , k)) = refl , λ _ → mapDia-translate f (k tt)

-- … so it is a lowering (`Container.Lowering`)
mapDia-lower : ∀ {S T} (f : S → T) (d : Dia S) → mapDia f d ≈⋆ lower (embed (scalarMor f)) d
mapDia-lower f d = trans≈ (mapDia-translate f d) (sym≈ (lower-embed (scalarMor f) d))

------------------------------------------------------------------------
-- Functoriality (equality of programs)

translate-id : ∀ {S} (d : Dia S) → translate (scalarMor (id {A = S})) d ≈⋆ d
translate-id (impure (Rectangle w h s , k))     = refl , λ ()
translate-id (impure (Disc r s , k))            = refl , λ ()
translate-id (impure (Segment w h s , k))       = refl , λ ()
translate-id (impure (Text pct size t s , k))   = refl , λ ()
translate-id (impure (Spacer w h , k))          = refl , λ ()
translate-id (impure (Beside al , k))           = refl , λ { zero → translate-id (k zero) ; (suc zero) → translate-id (k (suc zero)) }
translate-id (impure (Above al , k))            = refl , λ { zero → translate-id (k zero) ; (suc zero) → translate-id (k (suc zero)) }
translate-id (impure (Atop , k))                = refl , λ { zero → translate-id (k zero) ; (suc zero) → translate-id (k (suc zero)) }
translate-id (impure (LabelAbove , k))          = refl , λ { zero → translate-id (k zero) ; (suc zero) → translate-id (k (suc zero)) }
translate-id (impure (LabelBelow , k))          = refl , λ { zero → translate-id (k zero) ; (suc zero) → translate-id (k (suc zero)) }
translate-id (impure (Named n , k))             = refl , λ _ → translate-id (k tt)
translate-id (impure (Connect a pa b pb s , k)) = refl , λ _ → translate-id (k tt)

translate-∘ : ∀ {S T U} (f : S → T) (g : T → U) (d : Dia S) →
              translate (scalarMor g) (translate (scalarMor f) d) ≈⋆ translate (scalarMor (g ∘ f)) d
translate-∘ f g (impure (Rectangle w h s , k))     = refl , λ ()
translate-∘ f g (impure (Disc r s , k))            = refl , λ ()
translate-∘ f g (impure (Segment w h s , k))       = refl , λ ()
translate-∘ f g (impure (Text pct size t s , k))   = refl , λ ()
translate-∘ f g (impure (Spacer w h , k))          = refl , λ ()
translate-∘ f g (impure (Beside al , k))           = refl , λ { zero → translate-∘ f g (k zero) ; (suc zero) → translate-∘ f g (k (suc zero)) }
translate-∘ f g (impure (Above al , k))            = refl , λ { zero → translate-∘ f g (k zero) ; (suc zero) → translate-∘ f g (k (suc zero)) }
translate-∘ f g (impure (Atop , k))                = refl , λ { zero → translate-∘ f g (k zero) ; (suc zero) → translate-∘ f g (k (suc zero)) }
translate-∘ f g (impure (LabelAbove , k))          = refl , λ { zero → translate-∘ f g (k zero) ; (suc zero) → translate-∘ f g (k (suc zero)) }
translate-∘ f g (impure (LabelBelow , k))          = refl , λ { zero → translate-∘ f g (k zero) ; (suc zero) → translate-∘ f g (k (suc zero)) }
translate-∘ f g (impure (Named n , k))             = refl , λ _ → translate-∘ f g (k tt)
translate-∘ f g (impure (Connect a pa b pb s , k)) = refl , λ _ → translate-∘ f g (k tt)

mapDia-id : ∀ {S} (d : Dia S) → mapDia id d ≈⋆ d
mapDia-id d = trans≈ (mapDia-translate id d) (translate-id d)

-- `translate` respects equality of programs
translate-cong : ∀ {S T} (m : DiagramC S ⇒ DiagramC T) {d d′ : Dia S} → d ≈⋆ d′ →
                 translate m d ≈⋆ translate m d′
translate-cong m {impure (o , k)} {impure (.o , k′)} (refl , e) = refl , λ q → translate-cong m (e (position m q))

mapDia-∘ : ∀ {S T U} (f : S → T) (g : T → U) (d : Dia S) →
           mapDia g (mapDia f d) ≈⋆ mapDia (g ∘ f) d
mapDia-∘ f g d =
  trans≈ (mapDia-translate g (mapDia f d))
  (trans≈ (translate-cong (scalarMor g) (mapDia-translate f d))
  (trans≈ (translate-∘ f g d) (sym≈ (mapDia-translate (g ∘ f) d))))

------------------------------------------------------------------------
-- Fusion with folds

-- the algebra pulled back along a morphism
pull : ∀ {S T A} → DiagramC S ⇒ DiagramC T → Algebra T A → Algebra S A
pull m α o k = α (shape m o) (λ q → k (position m q))

-- handlers that respect pointwise-equal children
Congruent : ∀ {S} (A : Setoid 0ℓ 0ℓ) → Algebra S (Setoid.Carrier A) → Set
Congruent A α = ∀ o {k k′} → (∀ i → Setoid._≈_ A (k i) (k′ i)) → Setoid._≈_ A (α o k) (α o k′)

module _ {S T : Set} (A : Setoid 0ℓ 0ℓ) where
  private module A = Setoid A

  -- folding a translated diagram is folding the original with the pullback
  fold-translate : (m : DiagramC S ⇒ DiagramC T) (α : Algebra T A.Carrier) → Congruent A α →
                   ∀ d → fold α (translate m d) A.≈ fold (pull m α) d
  fold-translate m α c (impure (o , k)) = c (shape m o) (λ q → fold-translate m α c (k (position m q)))

  -- folding respects equality of programs
  fold-cong : (α : Algebra T A.Carrier) → Congruent A α → ∀ {d d′ : Dia T} → d ≈⋆ d′ →
              fold α d A.≈ fold α d′
  fold-cong α c {impure (o , k)} {impure (.o , k′)} (refl , e) = c o (λ i → fold-cong α c (e i))

  -- rendering after a change of scalar is rendering the original, pulled back
  fold-mapDia : (f : S → T) (α : Algebra T A.Carrier) → Congruent A α →
                ∀ d → fold α (mapDia f d) A.≈ fold (pull (scalarMor f) α) d
  fold-mapDia f α c d = A.trans (fold-cong α c (mapDia-translate f d)) (fold-translate (scalarMor f) α c d)
