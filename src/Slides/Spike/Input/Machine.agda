{-# OPTIONS --safe --without-K #-}

-- Spike: the semantics of a program as a Moore machine, by a fold.
--
-- `sem l` is the algebra for `ProgC V C` on the carrier `Machine V C`, extended
-- along a leaf interpretation `l : A → Machine V C` (the Kleisli extension).
-- `machine p = sem (λ _ → idle) p`.
--
--   show v ; k     the view gains `v`
--   await c ; k    waits; `c` moves to the start of `k`, anything else is ignored
--   par k₁ k₂      the synchronous product (both halves see every command)
--
-- Equality of machines is the isomorphism `MIso` of their state sets that
-- respects `init`, `step` and `view` pointwise (no funext needed).

module Slides.Spike.Input.Machine (V : Set) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Slides.Spike.Input.Prog V

record Machine (C : Set) : Set₁ where
  field
    State : Set
    init  : State
    step  : State → C → State
    view  : State → List V
open Machine

------------------------------------------------------------------------
-- Machine constructors (the algebra's operations)

idle : ∀ {C} → Machine C
idle = record { State = ⊤ ; init = tt ; step = λ q _ → q ; view = λ _ → [] }

showM : ∀ {C} → V → Machine C → Machine C
showM v M = record M { view = λ q → v ∷ view M q }

module _ {C : Set} (_≟_ : DecidableEquality C) where

  awaitM : C → Machine C → Machine C
  awaitM c M = record
    { State = ⊤ ⊎ State M
    ; init  = inj₁ tt
    ; step  = λ { (inj₁ _) c′ → if ⌊ c′ ≟ c ⌋ then inj₂ (init M) else inj₁ tt
                ; (inj₂ q) c′ → inj₂ (step M q c′) }
    ; view  = λ { (inj₁ _) → [] ; (inj₂ q) → view M q }
    }

parM : ∀ {C} → Machine C → Machine C → Machine C
parM M N = record
  { State = State M × State N
  ; init  = init M , init N
  ; step  = λ { (p , q) c → step M p c , step N q c }
  ; view  = λ { (p , q) → view M p ++ view N q }
  }

module Sem {C : Set} (_≟_ : DecidableEquality C) where

  sem : ∀ {A} → (A → Machine C) → Prog C A → Machine C
  sem l (pure a)                       = l a
  sem l (impure (inj₁ v , k))          = showM v (sem l (k tt))
  sem l (impure (inj₂ (inj₁ c) , k))   = awaitM _≟_ c (sem l (k tt))
  sem l (impure (inj₂ (inj₂ _) , k))   = parM (sem l (k true)) (sem l (k false))

  machine : ∀ {A} → Prog C A → Machine C
  machine = sem (λ _ → idle)

------------------------------------------------------------------------
-- Products on disjoint alphabets

-- Adapting the command vocabulary along a partial decoder `h : D → Maybe C`
-- (commands that do not decode are ignored).
liftE : ∀ {C D} → (D → Maybe C) → Machine C → Machine D
liftE h M = record
  { State = State M ; init = init M ; view = view M
  ; step = λ q d → maybe′ (step M q) q (h d) }

-- A machine for `C₁` as a machine for `C₁ ⊎ C₂` that ignores `C₂`, and dually.
decL : ∀ {C₁ C₂ : Set} → C₁ ⊎ C₂ → Maybe C₁
decL (inj₁ c) = just c
decL (inj₂ _) = nothing

decR : ∀ {C₁ C₂ : Set} → C₁ ⊎ C₂ → Maybe C₂
decR (inj₁ _) = nothing
decR (inj₂ c) = just c

liftL : ∀ {C₁ C₂} → Machine C₁ → Machine (C₁ ⊎ C₂)
liftL = liftE decL

liftR : ∀ {C₁ C₂} → Machine C₂ → Machine (C₁ ⊎ C₂)
liftR = liftE decR

-- The product: each half reacts only to its own summand.
infixr 2 _⊗_
_⊗_ : ∀ {C₁ C₂} → Machine C₁ → Machine C₂ → Machine (C₁ ⊎ C₂)
M ⊗ N = record
  { State = State M × State N
  ; init  = init M , init N
  ; step  = λ { (p , q) (inj₁ c) → step M p c , q ; (p , q) (inj₂ c) → p , step N q c }
  ; view  = λ { (p , q) → view M p ++ view N q }
  }
