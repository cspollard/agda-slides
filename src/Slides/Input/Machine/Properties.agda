{-# OPTIONS --safe --without-K #-}

-- Laws of the machine semantics.
--
--   sem-bind      the fold is a monad morphism: grafting leaves commutes with it
--   seq-machine   machine (p ⨾ q) ≅ sem (λ _ → machine q) p
--   await-seq     the awaited command moves from p's final state to q's start
--   lift-lemma    the semantics of a program lifted along a command map is the lifted
--                 semantics (an adapter `h : D → Maybe C` that decodes `f`)
--
-- Equality of machines is `MIso`: a bijection of state sets that preserves `init`,
-- `step` and `view` pointwise (no funext).  The product lemma for the deferred
-- parallel composition `‖` is not here (no `ParC` yet); it is on branch spike-input.

module Slides.Input.Machine.Properties (V : Set) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (_∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans)

open import Slides.Input V
open import Slides.Input.Machine V
open Machine

record MIso {C : Set} (M N : Machine C) : Set where
  field
    to      : State M → State N
    from    : State N → State M
    from-to : ∀ q → from (to q) ≡ q
    to-from : ∀ q → to (from q) ≡ q
    to-init : to (init M) ≡ init N
    to-step : ∀ q c → to (step M q c) ≡ step N (to q) c
    to-view : ∀ q → view N (to q) ≡ view M q
open MIso

refl-iso : ∀ {C} {M : Machine C} → MIso M M
refl-iso = record { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
                  ; to-init = refl ; to-step = λ _ _ → refl ; to-view = λ _ → refl }

trans-iso : ∀ {C} {L M N : Machine C} → MIso L M → MIso M N → MIso L N
trans-iso I J = record
  { to = λ q → to J (to I q) ; from = λ q → from I (from J q)
  ; from-to = λ q → trans (cong (from I) (from-to J (to I q))) (from-to I q)
  ; to-from = λ q → trans (cong (to J) (to-from I (from J q))) (to-from J q)
  ; to-init = trans (cong (to J) (to-init I)) (to-init J)
  ; to-step = λ q c → trans (cong (to J) (to-step I q c)) (to-step J (to I q) c)
  ; to-view = λ q → trans (to-view J (to I q)) (to-view I q) }

showM-iso : ∀ {C} {M N : Machine C} v → MIso M N → MIso (showM v M) (showM v N)
showM-iso v I = record { to = to I ; from = from I ; from-to = from-to I ; to-from = to-from I
  ; to-init = to-init I ; to-step = to-step I ; to-view = λ q → cong (v ∷_) (to-view I q) }

module _ {C : Set} (_≟_ : DecidableEquality C) where

  awaitM-iso : ∀ {M N : Machine C} c → MIso M N → MIso (awaitM _≟_ c M) (awaitM _≟_ c N)
  awaitM-iso {M} {N} c I = record
    { to = tA
    ; from = λ { (inj₁ _) → inj₁ tt ; (inj₂ q) → inj₂ (from I q) }
    ; from-to = λ { (inj₁ _) → refl ; (inj₂ q) → cong inj₂ (from-to I q) }
    ; to-from = λ { (inj₁ _) → refl ; (inj₂ q) → cong inj₂ (to-from I q) }
    ; to-init = refl
    ; to-step = λ { (inj₁ _) c′ → by c′ ; (inj₂ q) c′ → cong inj₂ (to-step I q c′) }
    ; to-view = λ { (inj₁ _) → refl ; (inj₂ q) → to-view I q } }
    where tA : ⊤ ⊎ State M → ⊤ ⊎ State N
          tA = λ { (inj₁ _) → inj₁ tt ; (inj₂ q) → inj₂ (to I q) }
          by : ∀ c′ → tA (if ⌊ c′ ≟ c ⌋ then inj₂ (init M) else inj₁ tt)
                    ≡ (if ⌊ c′ ≟ c ⌋ then inj₂ (init N) else inj₁ tt)
          by c′ with ⌊ c′ ≟ c ⌋
          ... | true  = cong inj₂ (to-init I)
          ... | false = refl

------------------------------------------------------------------------
-- Sequencing: the fold commutes with grafting at the leaves

module _ {C : Set} (d : DecidableEquality C) where

  sem-bind : ∀ {A B} (l : B → Machine C) (f : A → Prog C B) (p : Prog C A) →
             MIso (sem d l (p >>= f)) (sem d (λ a → sem d l (f a)) p)
  sem-bind l f (pure a)                      = refl-iso
  sem-bind l f (impure (inj₁ v , k))         = showM-iso v (sem-bind l f (k tt))
  sem-bind l f (impure (inj₂ (inj₁ c) , k))  = awaitM-iso d c (sem-bind l f (k tt))
  sem-bind l f (impure (inj₂ (inj₂ _) , k))  = sem-bind l f (k tt)

  seq-machine : ∀ {A B} (p : Prog C A) (q : Prog C B) →
                MIso (machine d (p ⨾ q)) (sem d (λ _ → machine d q) p)
  seq-machine p q = sem-bind (λ _ → idle) (λ _ → q) p

  dec-refl : ∀ c → ⌊ d c c ⌋ ≡ true
  dec-refl c with d c c
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)

  -- After `await c`, the command `c` takes the machine from the final state of the
  -- first part to the initial state of the second.
  await-seq : ∀ {B} c (q : Prog C B) →
    step (machine d (await c ⨾ q)) (init (machine d (await c ⨾ q))) c ≡ inj₂ (init (machine d q))
  await-seq c q = cong (λ b → if b then inj₂ (init (machine d q)) else inj₁ tt) (dec-refl c)

------------------------------------------------------------------------
-- Lifting along a command map

liftE-iso : ∀ {C D} (h : D → Maybe C) {M N : Machine C} → MIso M N → MIso (liftE h M) (liftE h N)
liftE-iso h {M} {N} I = record
  { to = to I ; from = from I ; from-to = from-to I ; to-from = to-from I
  ; to-init = to-init I ; to-view = to-view I ; to-step = λ q x → s q x }
  where
    s : ∀ q x → to I (maybe′ (step M q) q (h x)) ≡ maybe′ (step N (to I q)) (to I q) (h x)
    s q x with h x
    ... | just y  = to-step I q y
    ... | nothing = refl

liftE-idle : ∀ {C D} (h : D → Maybe C) → MIso idle (liftE h idle)
liftE-idle h = record
  { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
  ; to-init = refl ; to-view = λ _ → refl ; to-step = λ q x → s q x }
  where
    s : ∀ q x → q ≡ maybe′ (λ _ → q) q (h x)
    s q x with h x
    ... | just y  = refl
    ... | nothing = refl

-- `await d` over the decoded machine is the decoded `await c`, when `d` is exactly the
-- command that decodes to `c` (`coh`).  This is the one fact about commands the
-- lifting and lowering theorems need.
liftE-await : ∀ {C D} (dC : DecidableEquality C) (dD : DecidableEquality D) (h : D → Maybe C)
              c d (coh : ∀ x → ⌊ dD x d ⌋ ≡ maybe′ (λ y → ⌊ dC y c ⌋) false (h x))
              (M : Machine C) → MIso (awaitM dD d (liftE h M)) (liftE h (awaitM dC c M))
liftE-await {C} dC dD h c d coh M = record
  { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
  ; to-init = refl ; to-view = λ { (inj₁ _) → refl ; (inj₂ _) → refl }
  ; to-step = λ { (inj₁ _) x → w x ; (inj₂ q) x → s q x } }
  where
    w : ∀ x → (if ⌊ dD x d ⌋ then inj₂ (init M) else inj₁ tt)
            ≡ maybe′ (step (awaitM dC c M) (inj₁ tt)) (inj₁ tt) (h x)
    w x with h x | coh x
    ... | just y  | e = cong (λ b → if b then inj₂ (init M) else inj₁ tt) e
    ... | nothing | e = cong (λ b → if b then inj₂ (init M) else inj₁ tt) e
    s : ∀ q x → inj₂ (maybe′ (step M q) q (h x)) ≡ maybe′ (step (awaitM dC c M) (inj₂ q)) (inj₂ q) (h x)
    s q x with h x
    ... | just y  = refl
    ... | nothing = refl

module _ {C D : Set} (dC : DecidableEquality C) (dD : DecidableEquality D)
         (f : C → D) (h : D → Maybe C)
         (coh : ∀ x c → ⌊ dD x (f c) ⌋ ≡ maybe′ (λ y → ⌊ dC y c ⌋) false (h x)) where

  -- The lifting lemma: `mapP f` is invisible to the semantics up to `liftE h`.
  lift-lemma : ∀ {A} (l : A → Machine C) (l′ : A → Machine D)
               (hl : ∀ a → MIso (l′ a) (liftE h (l a))) (p : Prog C A) →
               MIso (sem dD l′ (mapP f p)) (liftE h (sem dC l p))
  lift-lemma l l′ hl (pure a)                      = hl a
  lift-lemma l l′ hl (impure (inj₁ v , k))         = showM-iso v (lift-lemma l l′ hl (k tt))
  lift-lemma l l′ hl (impure (inj₂ (inj₁ c) , k))  =
    trans-iso (awaitM-iso dD (f c) (lift-lemma l l′ hl (k tt)))
              (liftE-await dC dD h c (f c) (λ x → coh x c) (sem dC l (k tt)))
  lift-lemma l l′ hl (impure (inj₂ (inj₂ _) , k))  = lift-lemma l l′ hl (k tt)
