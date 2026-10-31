{-# OPTIONS --safe --without-K #-}

-- Moore machines over a set of commands, up to bisimulation.
--
-- A machine has states, an initial state, a transition per command and an output per state.  Its
-- states with propositional equality are a coalgebra of `X ↦ O × (C → X)` (`coalg`), so the
-- finality of the behaviours `List C → O` is `Semantics.Behaviour.final`; here:
--
--   obs M q     the behaviour of a state: the unique coalgebra map into the behaviours
--               (`Semantics.Behaviour.obs`, unique by `obs-unique`); `obs-runs` is its reading
--   Bisim       a relation on states holding initially and preserved by every command and by the
--               output; bisimilar machines are exactly those with equal traces (`bisim⇔trace`)
--
-- The output has its own setoid `O`.

module Slides.Program.Machine where

open import Level using (0ℓ; suc)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func)
open import Data.Product.Base using (_,_)
open import Categories.Functor.Coalgebra using (F-Coalgebra)

import Semantics.Behaviour as B
import Relation.Binary.PropositionalEquality as Eq

record Machine (C Out : Set) : Set₁ where
  field
    State : Set
    init  : State
    step  : State → C → State
    out   : State → Out
open Machine public

-- feed a list of commands, first command first, and read the output
runs : ∀ {C Out} (M : Machine C Out) → State M → List C → State M
runs M q []       = q
runs M q (c ∷ cs) = runs M (step M q c) cs

module _ (O : Setoid 0ℓ 0ℓ) where
  private module O = Setoid O

  -- a machine is a coalgebra of the Moore functor
  coalg : ∀ {C} → Machine C O.Carrier → F-Coalgebra (B.Moore C O)
  coalg M = record
    { A = setoid (State M)
    ; α = record { to = λ q → out M q , step M q
                 ; cong = λ { Eq.refl → O.refl , λ c → Eq.refl } } }

  -- the behaviour of a state, and of the machine
  obs : ∀ {C} (M : Machine C O.Carrier) → State M → List C → O.Carrier
  obs M = B.obs _ O (coalg M)

  feed : ∀ {C} (M : Machine C O.Carrier) → List C → O.Carrier
  feed M = obs M (init M)

  -- the behaviour reads the output after running the commands
  obs-runs : ∀ {C} (M : Machine C O.Carrier) q cs → obs M q cs O.≈ out M (runs M q cs)
  obs-runs M q []       = O.refl
  obs-runs M q (c ∷ cs) = obs-runs M (step M q c) cs

  record Bisim {C} (M N : Machine C O.Carrier) : Set₁ where
    field
      R      : State M → State N → Set
      R-init : R (init M) (init N)
      R-out  : ∀ {p q} → R p q → out M p O.≈ out N q
      R-step : ∀ {p q} → R p q → ∀ c → R (step M p c) (step N q c)
  open Bisim public

  -- bisimilar machines have equal traces, and conversely: the trace relation is a bisimulation
  bisim⇒trace : ∀ {C} {M N : Machine C O.Carrier} → Bisim M N → ∀ cs → feed M cs O.≈ feed N cs
  bisim⇒trace {M = M} {N} b = go (init M) (init N) (R-init b)
    where go : ∀ p q → R b p q → ∀ cs → obs M p cs O.≈ obs N q cs
          go p q r []       = R-out b r
          go p q r (c ∷ cs) = go _ _ (R-step b r c) cs

  trace⇒bisim : ∀ {C} {M N : Machine C O.Carrier} → (∀ cs → feed M cs O.≈ feed N cs) → Bisim M N
  trace⇒bisim {M = M} {N} t = record
    { R = λ p q → ∀ cs → obs M p cs O.≈ obs N q cs ; R-init = t ; R-out = λ r → r []
    ; R-step = λ r c cs → r (c ∷ cs) }
