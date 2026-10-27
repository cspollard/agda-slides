{-# OPTIONS --safe --without-K #-}

-- The semantics of a program as a Moore machine, by a Kleisli fold.
--
-- `sem l` is the algebra for `ProgC V C` on the carrier `Machine V C`, extended along a
-- leaf interpretation `l : A → Machine C`.  `machine p = sem (λ _ → idle) p`.
--
--   show v ; k     the view gains `v`
--   await c ; k    waits; `c` moves to the start of `k`, anything else is ignored
--   label l ; k    no effect (labels are read by `Slides.Input.Navigation`)
--
-- Laws (equality of machines is the isomorphism `MIso`) are in `Slides.Input.Machine.Properties`.

module Slides.Input.Machine (V : Set) where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; maybe′)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Slides.Input V

record Machine (C : Set) : Set₁ where
  field
    State : Set
    init  : State
    step  : State → C → State
    view  : State → List V
open Machine

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

  sem : ∀ {A} → (A → Machine C) → Prog C A → Machine C
  sem l (pure a)                       = l a
  sem l (impure (inj₁ v , k))          = showM v (sem l (k tt))
  sem l (impure (inj₂ (inj₁ c) , k))   = awaitM c (sem l (k tt))
  sem l (impure (inj₂ (inj₂ _) , k))   = sem l (k tt)

  machine : ∀ {A} → Prog C A → Machine C
  machine = sem (λ _ → idle)

-- Adapting the command vocabulary along a partial decoder `h : D → Maybe C`
-- (commands that do not decode are ignored).
liftE : ∀ {C D} → (D → Maybe C) → Machine C → Machine D
liftE h M = record
  { State = State M ; init = init M ; view = view M
  ; step = λ q d → maybe′ (step M q) q (h d) }
