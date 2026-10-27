{-# OPTIONS --safe --without-K #-}

-- Laws of the `pause` elaboration.
--
-- Mode threading (`Slides.Steps`):
--
--   bind-assoc, go-bind   sequencing is associative; elaborating a sequence elaborates the
--                         second part in the mode the first leaves behind
--
-- The same on bodies that await (`Slides.Steps.Input`), for any `step?`:
--
--   goBy-bind     elaborating a sequence elaborates the second part in the mode the first
--                 leaves behind
--
-- Bridge: `pause` is `await next`:
--
--   elab-bind                   `elab` preserves sequencing (it is a Kleisli lowering)
--   goBy-elab, afterBy-elab     the second pass after `elab` is `go`, and its mode is `after`
--   stepsBy-elab                `stepsBy isNext (elab b) ≡ steps b`
--   go-bind-elab                `go-bind` re-derived through the bridge, from `goBy-bind`

module Slides.Steps.Properties where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Core
open import Slides.Input.Deck
open import Slides.Steps
open import Slides.Steps.Input

------------------------------------------------------------------------
-- The mode flows through sequencing

-- Sequencing is associative (every command has a single continuation, so
-- `λ q → …` over `⊤` is a constant function).
bind-assoc : ∀ (b₁ b₂ b₃ : Body) →
             ((b₁ >>= λ _ → b₂) >>= λ _ → b₃) ≡ (b₁ >>= λ _ → (b₂ >>= λ _ → b₃))
bind-assoc (pure _)             b₂ b₃ = refl
bind-assoc (impure (inj₁ c , k)) b₂ b₃ =
  cong (λ x → impure (inj₁ c , λ _ → x)) (bind-assoc (k tt) b₂ b₃)
bind-assoc (impure (inj₂ l , k)) b₂ b₃ =
  cong (λ x → impure (inj₂ l , λ _ → x)) (bind-assoc (k tt) b₂ b₃)

-- Elaborating a sequence elaborates the second part in the mode the first
-- part leaves behind.
go-bind : ∀ m (b₁ b₂ : Body) →
          go m (b₁ >>= λ _ → b₂) ≡ (go m b₁ >>= λ _ → go (after m b₁) b₂)
go-bind m (pure _)              b₂ = refl
go-bind m (impure (inj₁ c , k)) b₂ =
  trans (cong (λ x → wrapC m c >>= λ _ → x) (go-bind m (k tt) b₂))
        (sym (bind-assoc (wrapC m c) (go m (k tt)) (go (after m (k tt)) b₂)))
go-bind m (impure (inj₂ l , k)) b₂ =
  trans (cong (λ x → proj₂ (stepL m l) >>= λ _ → x) (go-bind (proj₁ (stepL m l)) (k tt) b₂))
        (sym (bind-assoc (proj₂ (stepL m l)) (go (proj₁ (stepL m l)) (k tt))
                         (go (after (proj₁ (stepL m l)) (k tt)) b₂)))

------------------------------------------------------------------------
-- Bodies that await

module _ {X : Set} (step? : X → Bool) where

  -- Elaborating a sequence elaborates the second part in the mode the first leaves.
  goBy-bind : ∀ m (x y : Body⁺ X) →
              goBy step? m (x >>= λ _ → y)
              ≡ (goBy step? m x >>= λ _ → goBy step? (afterBy step? m x) y)
  goBy-bind m (pure _)                     y = refl
  goBy-bind m (impure (inj₁ (inj₁ c) , k)) y =
    trans (cong (λ w → wrapC m c >>= λ _ → w) (goBy-bind m (k tt) y))
          (sym (bind-assoc (wrapC m c) (goBy step? m (k tt))
                           (goBy step? (afterBy step? m (k tt)) y)))
  goBy-bind m (impure (inj₁ (inj₂ l) , k)) y =
    trans (cong (λ w → proj₂ (stepL m l) >>= λ _ → w) (goBy-bind (proj₁ (stepL m l)) (k tt) y))
          (sym (bind-assoc (proj₂ (stepL m l)) (goBy step? (proj₁ (stepL m l)) (k tt))
                           (goBy step? (afterBy step? (proj₁ (stepL m l)) (k tt)) y)))
  goBy-bind m (impure (inj₂ a , k))        y = goBy-bind (m ∨ step? a) (k tt) y

------------------------------------------------------------------------
-- Bridge: `pause` is `await next`

module _ {C : Set} where

  -- One elaborated layout command: the second pass sees exactly what `go` and `after` see.
  private
    goBy-elabS : ∀ m l (r : Body⁺ (Nav ⊎ C)) →
      goBy isNext m (impure (elabS {C} l , λ _ → r))
      ≡ (proj₂ (stepL m l) >>= λ _ → goBy isNext (proj₁ (stepL m l)) r)
    goBy-elabS m pause         r = refl
    goBy-elabS m (columns _)   r = refl
    goBy-elabS m (box _ _)     r = refl
    goBy-elabS m (fragment _ _) r = refl
    goBy-elabS m (classed _ _) r = refl
    goBy-elabS m (placed _ _ _ _ _) r = refl
    goBy-elabS m (stepped _ _) r = refl

    afterBy-elabS : ∀ m l (r : Body⁺ (Nav ⊎ C)) →
      afterBy isNext m (impure (elabS {C} l , λ _ → r)) ≡ afterBy isNext (proj₁ (stepL m l)) r
    afterBy-elabS m pause         r = refl
    afterBy-elabS m (columns _)   r = refl
    afterBy-elabS m (box _ _)     r = refl
    afterBy-elabS m (fragment _ _) r = refl
    afterBy-elabS m (classed _ _) r = refl
    afterBy-elabS m (placed _ _ _ _ _) r = refl
    afterBy-elabS m (stepped _ _) r = refl

  -- `elab` preserves sequencing.
  elab-bind : ∀ (b₁ b₂ : Body) →
              elab {C} (b₁ >>= λ _ → b₂) ≡ (elab b₁ >>= λ _ → elab b₂)
  elab-bind (pure _)              b₂ = refl
  elab-bind (impure (inj₁ c , k)) b₂ =
    cong (λ w → impure (inj₁ (inj₁ c) , λ _ → w)) (elab-bind (k tt) b₂)
  elab-bind (impure (inj₂ l , k)) b₂ =
    cong (λ w → impure (elabS l , λ _ → w)) (elab-bind (k tt) b₂)

  -- The second pass after `elab` is `go`, and its mode is `after`.
  goBy-elab : ∀ m (b : Body) → goBy (isNext {C}) m (elab b) ≡ go m b
  goBy-elab m (pure _)              = refl
  goBy-elab m (impure (inj₁ c , k)) = cong (λ w → wrapC m c >>= λ _ → w) (goBy-elab m (k tt))
  goBy-elab m (impure (inj₂ l , k)) =
    trans (goBy-elabS m l (elab (k tt)))
          (cong (λ w → proj₂ (stepL m l) >>= λ _ → w) (goBy-elab (proj₁ (stepL m l)) (k tt)))

  afterBy-elab : ∀ m (b : Body) → afterBy (isNext {C}) m (elab b) ≡ after m b
  afterBy-elab m (pure _)              = refl
  afterBy-elab m (impure (inj₁ c , k)) = afterBy-elab m (k tt)
  afterBy-elab m (impure (inj₂ l , k)) =
    trans (afterBy-elabS m l (elab (k tt))) (afterBy-elab (proj₁ (stepL m l)) (k tt))

  -- The bridge theorem: `steps` is `elab` followed by the second pass.
  stepsBy-elab : ∀ (b : Body) → stepsBy (isNext {C}) (elab b) ≡ steps b
  stepsBy-elab = goBy-elab false

  -- `go-bind` re-derived: `elab` is a monad morphism and the second pass obeys `goBy-bind`.
  go-bind-elab : ∀ m (b₁ b₂ : Body) →
                 go m (b₁ >>= λ _ → b₂) ≡ (go m b₁ >>= λ _ → go (after m b₁) b₂)
  go-bind-elab m b₁ b₂ =
    trans (sym (goBy-elab m (b₁ >>= λ _ → b₂)))
    (trans (cong (goBy (isNext {C}) m) (elab-bind b₁ b₂))
    (trans (goBy-bind isNext m (elab b₁) (elab b₂))
           (cong₂ (λ u v → u >>= λ _ → v) (goBy-elab m b₁)
             (trans (cong (λ n → goBy (isNext {C}) n (elab b₂)) (afterBy-elab m b₁))
                    (goBy-elab (after m b₁) b₂)))))
