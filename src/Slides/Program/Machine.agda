{-# OPTIONS --safe --without-K #-}

-- Moore machines over a set of commands, up to bisimulation.
--
-- A machine has states, an initial state, a transition per command and an output per state.
-- A machine is a pointed coalgebra of `X ↦ O × (C → X)`; the final one is the set of behaviours
-- `List C → O`, a map `hd f = f []` and `tl f c = f ∘ (c ∷_)`.
--
--   obs M q     the behaviour of a state: the unique coalgebra map into the behaviours (`unique`)
--   final f     a behaviour as a machine: its own state, `hd`, `tl`
--   BehS        behaviours up to pointwise equality, a setoid at level 0 with no function extensionality
--   Bisim       a relation on states holding initially and preserved by every command and by the
--               output; bisimilar machines are exactly those with equal traces (`bisim⇔trace`)
--
-- The output has its own setoid `O`.

module Slides.Program.Machine where

open import Level using (0ℓ; suc)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

-- the behaviour of a state, and of the machine
obs : ∀ {C Out} (M : Machine C Out) → State M → List C → Out
obs M q cs = out M (runs M q cs)

feed : ∀ {C Out} (M : Machine C Out) → List C → Out
feed M = obs M (init M)

-- a behaviour as a machine: the final coalgebra
final : ∀ {C Out} → (List C → Out) → Machine C Out
final f = record { State = _ ; init = f ; step = λ g c cs → g (c ∷ cs) ; out = λ g → g [] }

final-feed : ∀ {C Out} (f : List C → Out) cs → feed (final f) cs ≡ f cs
final-feed f cs = go f cs
  where go : ∀ g cs → obs (final f) g cs ≡ g cs
        go g []       = refl
        go g (c ∷ cs) = go (λ cs′ → g (c ∷ cs′)) cs

module _ (O : Setoid 0ℓ 0ℓ) where
  private module O = Setoid O

  BehS : Set → Setoid 0ℓ 0ℓ
  BehS C = record
    { Carrier = List C → O.Carrier ; _≈_ = λ f g → ∀ cs → f cs O.≈ g cs
    ; isEquivalence = record { refl = λ _ → O.refl ; sym = λ e cs → O.sym (e cs)
                             ; trans = λ e e′ cs → O.trans (e cs) (e′ cs) } }

  -- a coalgebra map from the states of `M` to the behaviours; `obs M` is one and the only one
  record CoHom {C} (M : Machine C O.Carrier) (h : State M → List C → O.Carrier) : Set where
    field
      hd-h : ∀ q → h q [] O.≈ out M q
      tl-h : ∀ q c cs → h (step M q c) cs O.≈ h q (c ∷ cs)

  obs-hom : ∀ {C} (M : Machine C O.Carrier) → CoHom M (obs M)
  obs-hom M = record { hd-h = λ _ → O.refl ; tl-h = λ _ _ _ → O.refl }

  unique : ∀ {C} (M : Machine C O.Carrier) {h} → CoHom M h → ∀ q cs → h q cs O.≈ obs M q cs
  unique M hh q []       = CoHom.hd-h hh q
  unique M hh q (c ∷ cs) = O.trans (O.sym (CoHom.tl-h hh q c cs)) (unique M hh (step M q c) cs)

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
