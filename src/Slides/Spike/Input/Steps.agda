{-# OPTIONS --safe --without-K #-}

-- Spike: `pause` of `Slides.Steps` is `await next`.
--
-- `elab` lowers a `Body` (a program over `BlockC`, in which `pause` is a layout
-- command) to a program over `BlockC ⊎ AwaitC Nav` in which each `pause` is
-- `await next`.  It is a Kleisli lowering (`Container.Lowering.lower`).  The mode
-- that `Slides.Steps.go` threads through a body ("have we passed a pause?") is
-- exactly "does the elaborated program contain an `await`?":
--
--   after-elab    after m b ≡ m ∨ hasAwait (elab b)
--   after-bind    after (after m b₁) b₂ ≡ m ∨ hasAwait (elab (b₁ ⨾ b₂))
--
-- the second being the statement behind `go-bind` for sequencing.

module Slides.Spike.Input.Steps where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Container; Shape; Position)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎C_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ)

open import Slides.Core
open import Slides.Steps using (after; stepL)
open import Container.Lowering using (Lowering; lower)

-- `Nav` and `AwaitC` come from the scene-parametric module; only the command type matters here.
open import Slides.Spike.Input.Prog ⊤ using (Nav; next; AwaitC)

DeckBlockC : Container _ _
DeckBlockC = BlockC ⊎C AwaitC Nav

ElabBody : Set
ElabBody = DeckBlockC ⋆ ⊤

private
  lay : LayoutShape → ElabBody
  lay l = impure (inj₁ (inj₂ l) , λ _ → pure tt)

  isPause : LayoutShape → Bool
  isPause pause = true
  isPause _     = false

elabL : Lowering BlockC DeckBlockC
elabL (inj₁ c)     = impure (inj₁ (inj₁ c) , λ _ → pure tt)
elabL (inj₂ pause) = impure (inj₂ next , λ _ → pure tt)
elabL (inj₂ l)     = lay l

elab : Body → ElabBody
elab = lower elabL

hasAwait : ∀ {A : Set} → DeckBlockC ⋆ A → Bool
hasAwait (pure _)                 = false
hasAwait (impure (inj₁ (inj₁ _) , k)) = hasAwait (k tt)
hasAwait (impure (inj₁ (inj₂ _) , k)) = hasAwait (k tt)
hasAwait (impure (inj₂ _ , k))    = true

------------------------------------------------------------------------
-- The mode of `Slides.Steps` is "has an `await` been passed?"

other : ∀ m (X Y : Bool) → X ≡ (m ∨ false) ∨ Y → X ≡ m ∨ Y
other m X Y ih = trans ih (cong (λ z → z ∨ Y) (∨-identityʳ m))

after-elab : ∀ m (b : Body) → after m b ≡ m ∨ hasAwait (elab b)
after-elab m (pure _)                       = sym (∨-identityʳ m)
after-elab m (impure (inj₁ c , k))          = after-elab m (k tt)
after-elab m (impure (inj₂ pause , k))      =
  trans (after-elab (m ∨ true) (k tt)) (fin (∨-zeroʳ m))
  where fin : ∀ {x} → x ≡ true → x ∨ hasAwait (elab (k tt)) ≡ m ∨ true
        fin e = trans (cong (λ z → z ∨ hasAwait (elab (k tt))) e) (sym (∨-zeroʳ m))
after-elab m (impure (inj₂ (columns x) , k))     = other m _ _ (after-elab (m ∨ false) (k tt))
after-elab m (impure (inj₂ (box t x) , k))       = other m _ _ (after-elab (m ∨ false) (k tt))
after-elab m (impure (inj₂ (fragment s x) , k))  = other m _ _ (after-elab (m ∨ false) (k tt))
after-elab m (impure (inj₂ (classed s x) , k))   = other m _ _ (after-elab (m ∨ false) (k tt))
after-elab m (impure (inj₂ (placed a b c d x) , k)) = other m _ _ (after-elab (m ∨ false) (k tt))
after-elab m (impure (inj₂ (stepped s x) , k))   = other m _ _ (after-elab (m ∨ false) (k tt))

-- Sequencing: the mode after `b₁` is the mode in which `b₂` starts.
after-seq : ∀ m (b₁ b₂ : Body) → after m (b₁ >>= λ _ → b₂) ≡ after (after m b₁) b₂
after-seq m (pure _)              b₂ = refl
after-seq m (impure (inj₁ _ , k)) b₂ = after-seq m (k tt) b₂
after-seq m (impure (inj₂ l , k)) b₂ = after-seq (proj₁ (stepL m l)) (k tt) b₂

-- The `go-bind` fact in terms of the elaboration: a sequence awaits iff a part does.
hasAwait-bind : ∀ (b₁ b₂ : Body) →
  hasAwait (elab (b₁ >>= λ _ → b₂)) ≡ hasAwait (elab b₁) ∨ hasAwait (elab b₂)
hasAwait-bind b₁ b₂ =
  trans (sym (after-elab false (b₁ >>= λ _ → b₂)))
 (trans (after-seq false b₁ b₂)
 (trans (after-elab (after false b₁) b₂)
        (cong (λ z → z ∨ hasAwait (elab b₂)) (after-elab false b₁))))
