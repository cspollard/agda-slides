{-# OPTIONS --safe --without-K #-}

-- Moore machines over a set of commands, up to bisimulation.
--
-- A machine has states, an initial state, a transition per command and an output per state.
-- Machines are equal when bisimilar: a relation on states holding initially and preserved by
-- every command and by the output.  `MachineS` is a setoid, with no function extensionality (the
-- relation on product states is pointwise), as the generic lemmas of `Container.Interpret.Plain`
-- need.  The output has its own setoid `O`, so a `Congruent` scene algebra gives congruent machines.

module Slides.Program.Machine where

open import Level using (0ℓ; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_; Σ-syntax)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

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

feed : ∀ {C Out} (M : Machine C Out) → List C → Out
feed M cs = out M (runs M (init M) cs)

module _ (O : Setoid 0ℓ 0ℓ) where
  private module O = Setoid O

  record Bisim {C} (M N : Machine C O.Carrier) : Set₁ where
    field
      R      : State M → State N → Set
      R-init : R (init M) (init N)
      R-out  : ∀ {p q} → R p q → out M p O.≈ out N q
      R-step : ∀ {p q} → R p q → ∀ c → R (step M p c) (step N q c)
  open Bisim public

  bisim-refl : ∀ {C} {M : Machine C O.Carrier} → Bisim M M
  bisim-refl = record { R = λ p q → p ≡′ q ; R-init = refl′ ; R-out = λ { refl′ → O.refl }
                      ; R-step = λ { refl′ c → refl′ } }
    where open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≡′_; refl to refl′)

  bisim-sym : ∀ {C} {M N : Machine C O.Carrier} → Bisim M N → Bisim N M
  bisim-sym b = record { R = λ q p → R b p q ; R-init = R-init b ; R-out = λ r → O.sym (R-out b r)
                       ; R-step = λ r c → R-step b r c }

  bisim-trans : ∀ {C} {L M N : Machine C O.Carrier} → Bisim L M → Bisim M N → Bisim L N
  bisim-trans a b = record
    { R = λ p r → Σ[ q ∈ _ ] R a p q × R b q r
    ; R-init = _ , R-init a , R-init b
    ; R-out = λ { (_ , x , y) → O.trans (R-out a x) (R-out b y) }
    ; R-step = λ { (_ , x , y) c → _ , R-step a x c , R-step b y c } }
    where open import Data.Product.Base using (_×_)

  MachineS : Set → Setoid (suc 0ℓ) (suc 0ℓ)
  MachineS C = record
    { Carrier = Machine C O.Carrier ; _≈_ = Bisim
    ; isEquivalence = record { refl = bisim-refl ; sym = bisim-sym ; trans = bisim-trans } }
