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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)

open import Slides.Core

private
  content : ContentShape → Body
  content c = impure (inj₁ c , λ _ → pure tt)

  layout : LayoutShape → Body
  layout l = impure (inj₂ l , λ _ → pure tt)

  -- Wrap a command for the current mode.
  wrapC : Bool → ContentShape → Body
  wrapC false c         = content c
  wrapC true  (notes t) = content (notes t)
  wrapC true  (script j) = content (script j)
  wrapC true  c         = layout (fragment nothing (impure (c , λ _ → pure tt)))

  wrapL : Bool → LayoutShape → Body
  wrapL false l = layout l
  wrapL true  l = layout (stepped nothing l)

-- What a layout command does in a mode: the mode afterwards, and its
-- replacement.  (A `pause` switches the mode on and disappears.)
stepL : Bool → LayoutShape → Bool × Body
stepL m l = (m ∨ isPause l) , (if isPause l then pure tt else wrapL m l)
  where
    isPause : LayoutShape → Bool
    isPause pause = true
    isPause _     = false

-- Elaborate a body, starting in the given mode.
go : Bool → Body → Body
go m (pure x)                = pure x
go m (impure (inj₁ c , k))   = wrapC m c >>= λ _ → go m (k tt)
go m (impure (inj₂ l , k))   = proj₂ (stepL m l) >>= λ _ → go (proj₁ (stepL m l)) (k tt)

steps : Body → Body
steps = go false

-- The mode after running a body from the given mode.
after : Bool → Body → Bool
after m (pure _)              = m
after m (impure (inj₁ _ , k)) = after m (k tt)
after m (impure (inj₂ l , k)) = after (proj₁ (stepL m l)) (k tt)

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
