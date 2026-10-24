{-# OPTIONS --safe --without-K #-}

-- Beamer-style `pause`: everything after a `pause` appears step by step.
--
-- `pause` is an ordinary (layout) command that renders as nothing.  Its
-- meaning is given by this elaboration of a body into a pause-free body:
-- a pass with a mode (`false` until the first `pause`, `true` after) that
-- wraps every later command in a fragment.  Content commands become
-- `fragment` commands, other layout commands are `stepped`, and `notes` are
-- left alone (they are not shown on the slide).  The mode flows through
-- sequencing, so a `pause` in one component affects the commands that follow
-- it, including those of later components; `go-bind` states exactly how.
--
-- Backends apply `steps` to each slide body before rendering.

module Slides.Steps where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)

open import Slides.Core

private
  content : ContentShape → Body K
  content c = impure (inj₁ (inj₁ c) , λ _ → pure tt)

  layout : LayoutShape → Body K
  layout l = impure (inj₁ (inj₂ l) , λ _ → pure tt)

  capability : K → Body K
  capability s = impure (inj₂ s , λ _ → pure tt)

  -- Wrap a command for the current mode.
  wrapC : Bool → ContentShape → Body K
  wrapC false c         = content c
  wrapC true  (notes t) = content (notes t)
  wrapC true  c         = layout (fragment nothing (impure (c , λ _ → pure tt)))

  wrapL : Bool → LayoutShape → Body K
  wrapL false l = layout l
  wrapL true  l = layout (stepped nothing l)

  -- Commands of a capability decide for themselves how to appear later.
  wrapK : {{_ : Steppable K}} → Bool → K → Body K
  wrapK false s = capability s
  wrapK true  s = capability (later s)

-- What a layout command does in a mode: the mode afterwards, and its
-- replacement.  (A `pause` switches the mode on and disappears.)
isPause : LayoutShape → Bool
isPause pause = true
isPause _     = false

modeL : Bool → LayoutShape → Bool
modeL m l = m ∨ isPause l

replaceL : Bool → LayoutShape → Body K
replaceL m l = if isPause l then pure tt else wrapL m l

-- Elaborate a body, starting in the given mode.
go : {{_ : Steppable K}} → Bool → Body K → Body K
go m (pure x)                = pure x
go m (impure (inj₁ (inj₁ c) , k)) = wrapC m c >>= λ _ → go m (k tt)
go m (impure (inj₁ (inj₂ l) , k)) = replaceL m l >>= λ _ → go (modeL m l) (k tt)
go m (impure (inj₂ s , k))        = wrapK m s >>= λ _ → go m (k tt)

steps : {{_ : Steppable K}} → Body K → Body K
steps = go false

-- The mode after running a body from the given mode.
after : Bool → Body K → Bool
after m (pure _)              = m
after m (impure (inj₁ (inj₁ _) , k)) = after m (k tt)
after m (impure (inj₁ (inj₂ l) , k)) = after (modeL m l) (k tt)
after m (impure (inj₂ _ , k))        = after m (k tt)

------------------------------------------------------------------------
-- The mode flows through sequencing

module _ {K : Set} {{_ : Steppable K}} where

  -- Sequencing is associative (every command has a single continuation, so
  -- `λ q → …` over `⊤` is a constant function).
  bind-assoc : ∀ (b₁ b₂ b₃ : Body K) →
               ((b₁ >>= λ _ → b₂) >>= λ _ → b₃) ≡ (b₁ >>= λ _ → (b₂ >>= λ _ → b₃))
  bind-assoc (pure _)             b₂ b₃ = refl
  bind-assoc (impure (inj₁ (inj₁ c) , k)) b₂ b₃ =
    cong (λ x → impure (inj₁ (inj₁ c) , λ _ → x)) (bind-assoc (k tt) b₂ b₃)
  bind-assoc (impure (inj₁ (inj₂ l) , k)) b₂ b₃ =
    cong (λ x → impure (inj₁ (inj₂ l) , λ _ → x)) (bind-assoc (k tt) b₂ b₃)
  bind-assoc (impure (inj₂ s , k)) b₂ b₃ =
    cong (λ x → impure (inj₂ s , λ _ → x)) (bind-assoc (k tt) b₂ b₃)

  -- Elaborating a sequence elaborates the second part in the mode the first
  -- part leaves behind.
  go-bind : ∀ m (b₁ b₂ : Body K) →
            go m (b₁ >>= λ _ → b₂) ≡ (go m b₁ >>= λ _ → go (after m b₁) b₂)
  go-bind m (pure _)              b₂ = refl
  go-bind m (impure (inj₁ (inj₁ c) , k)) b₂ =
    trans (cong (λ x → wrapC m c >>= λ _ → x) (go-bind m (k tt) b₂))
          (sym (bind-assoc (wrapC m c) (go m (k tt)) (go (after m (k tt)) b₂)))
  go-bind m (impure (inj₂ s , k)) b₂ =
    trans (cong (λ x → wrapK m s >>= λ _ → x) (go-bind m (k tt) b₂))
          (sym (bind-assoc (wrapK m s) (go m (k tt)) (go (after m (k tt)) b₂)))
  go-bind m (impure (inj₁ (inj₂ l) , k)) b₂ =
    trans (cong (λ x → replaceL m l >>= λ _ → x) (go-bind (modeL m l) (k tt) b₂))
          (sym (bind-assoc (replaceL m l) (go (modeL m l) (k tt))
                           (go (after (modeL m l) (k tt)) b₂)))
