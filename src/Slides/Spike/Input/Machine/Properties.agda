{-# OPTIONS --safe --without-K #-}

-- Spike: laws of the machine semantics.
--
--   lift-lemma    the semantics of a program lifted along a command map is the
--                 lifted semantics (an adapter `h : D → Maybe C` that decodes `f`)
--   product       machine (p ‖ q) ≅ machine p ⊗ machine q
--   sem-bind      the fold is a monad morphism: grafting leaves commutes with it
--   seq-machine   machine (p ⨾ q) ≅ sem (λ _ → machine q) p
--   await-seq     the awaited command moves from p's final state to q's start
--
-- Equality of machines is `MIso`: a bijection of state sets that preserves
-- `init`, `step` and `view` pointwise (no funext).

module Slides.Spike.Input.Machine.Properties (V : Set) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (≡-dec)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; ⌊⌋-map′)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂; trans)

open import Slides.Spike.Input.Prog V
open import Slides.Spike.Input.Machine V
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

-- The constructors of machines preserve isomorphism.
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

parM-iso : ∀ {C} {M M′ N N′ : Machine C} → MIso M M′ → MIso N N′ → MIso (parM M N) (parM M′ N′)
parM-iso I J = record
  { to = λ { (p , q) → to I p , to J q } ; from = λ { (p , q) → from I p , from J q }
  ; from-to = λ { (p , q) → cong₂ _,_ (from-to I p) (from-to J q) }
  ; to-from = λ { (p , q) → cong₂ _,_ (to-from I p) (to-from J q) }
  ; to-init = cong₂ _,_ (to-init I) (to-init J)
  ; to-step = λ { (p , q) c → cong₂ _,_ (to-step I p c) (to-step J q c) }
  ; to-view = λ { (p , q) → cong₂ _++_ (to-view I p) (to-view J q) } }

------------------------------------------------------------------------
-- Sequencing: the fold commutes with grafting at the leaves

module _ {C : Set} (d : DecidableEquality C) where
  open Sem d

  sem-bind : ∀ {A B} (l : B → Machine C) (f : A → Prog C B) (p : Prog C A) →
             MIso (sem l (p >>= f)) (sem (λ a → sem l (f a)) p)
  sem-bind l f (pure a)                      = refl-iso
  sem-bind l f (impure (inj₁ v , k))         = showM-iso v (sem-bind l f (k tt))
  sem-bind l f (impure (inj₂ (inj₁ c) , k))  = awaitM-iso d c (sem-bind l f (k tt))
  sem-bind l f (impure (inj₂ (inj₂ _) , k))  =
    parM-iso (sem-bind l f (k true)) (sem-bind l f (k false))

  seq-machine : ∀ {A B} (p : Prog C A) (q : Prog C B) →
                MIso (machine (p ⨾ q)) (sem (λ _ → machine q) p)
  seq-machine p q = sem-bind (λ _ → idle) (λ _ → q) p

  dec-refl : ∀ c → ⌊ d c c ⌋ ≡ true
  dec-refl c with d c c
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)

  -- After `await c`, the command `c` takes the machine from the final state of
  -- the first part to the initial state of the second.
  await-seq : ∀ {B} c (q : Prog C B) →
    step (machine (await c ⨾ q)) (init (machine (await c ⨾ q))) c ≡ inj₂ (init (machine q))
  await-seq c q = cong (λ b → if b then inj₂ (init (machine q)) else inj₁ tt) (dec-refl c)

------------------------------------------------------------------------
-- Lifting along a command map

module _ {C D : Set} (dC : DecidableEquality C) (dD : DecidableEquality D)
         (f : C → D) (h : D → Maybe C)
         (coh : ∀ x c → ⌊ dD x (f c) ⌋ ≡ maybe′ (λ y → ⌊ dC y c ⌋) false (h x)) where

  private
    module SC = Sem dC
    module SD = Sem dD

  liftE-await : ∀ c (M : Machine C) →
                MIso (awaitM dD (f c) (liftE h M)) (liftE h (awaitM dC c M))
  liftE-await c M = record
    { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
    ; to-init = refl ; to-view = λ { (inj₁ _) → refl ; (inj₂ _) → refl }
    ; to-step = λ { (inj₁ _) x → w x ; (inj₂ q) x → s q x } }
    where
      w : ∀ x → (if ⌊ dD x (f c) ⌋ then inj₂ (init M) else inj₁ tt)
              ≡ maybe′ (step (awaitM dC c M) (inj₁ tt)) (inj₁ tt) (h x)
      w x with h x | coh x c
      ... | just y  | e = cong (λ b → if b then inj₂ (init M) else inj₁ tt) e
      ... | nothing | e = cong (λ b → if b then inj₂ (init M) else inj₁ tt) e
      s : ∀ q x → inj₂ (maybe′ (step M q) q (h x)) ≡ maybe′ (step (awaitM dC c M) (inj₂ q)) (inj₂ q) (h x)
      s q x with h x
      ... | just y  = refl
      ... | nothing = refl

  liftE-par : ∀ (M N : Machine C) → MIso (parM (liftE h M) (liftE h N)) (liftE h (parM M N))
  liftE-par M N = record
    { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
    ; to-init = refl ; to-view = λ _ → refl
    ; to-step = λ { (p , q) x → s p q x } }
    where
      s : ∀ p q x → (maybe′ (step M p) p (h x) , maybe′ (step N q) q (h x))
                  ≡ maybe′ (λ c → step M p c , step N q c) (p , q) (h x)
      s p q x with h x
      ... | just y  = refl
      ... | nothing = refl

  liftE-idle : MIso idle (liftE h idle)
  liftE-idle = record
    { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
    ; to-init = refl ; to-view = λ _ → refl ; to-step = λ q x → s q x }
    where
      s : ∀ q x → q ≡ maybe′ (λ _ → q) q (h x)
      s q x with h x
      ... | just y  = refl
      ... | nothing = refl

  -- The lifting lemma: `mapP f` is invisible to the semantics up to `liftE h`.
  lift-lemma : ∀ {A} (l : A → Machine C) (l′ : A → Machine D)
               (hl : ∀ a → MIso (l′ a) (liftE h (l a))) (p : Prog C A) →
               MIso (SD.sem l′ (mapP f p)) (liftE h (SC.sem l p))
  lift-lemma l l′ hl (pure a)                      = hl a
  lift-lemma l l′ hl (impure (inj₁ v , k))         = showM-iso v (lift-lemma l l′ hl (k tt))
  lift-lemma l l′ hl (impure (inj₂ (inj₁ c) , k))  =
    trans-iso (awaitM-iso dD (f c) (lift-lemma l l′ hl (k tt))) (liftE-await c (SC.sem l (k tt)))
  lift-lemma l l′ hl (impure (inj₂ (inj₂ _) , k))  =
    trans-iso (parM-iso (lift-lemma l l′ hl (k true)) (lift-lemma l l′ hl (k false)))
              (liftE-par (SC.sem l (k true)) (SC.sem l (k false)))

------------------------------------------------------------------------
-- The product lemma

module _ {C₁ C₂ : Set} (d₁ : DecidableEquality C₁) (d₂ : DecidableEquality C₂) where

  private
    d : DecidableEquality (C₁ ⊎ C₂)
    d = ≡-dec d₁ d₂
    module S₁ = Sem d₁
    module S₂ = Sem d₂
    module S  = Sem d

  par-⊗ : ∀ (M : Machine C₁) (N : Machine C₂) → MIso (parM (liftL M) (liftR N)) (M ⊗ N)
  par-⊗ M N = record
    { to = λ q → q ; from = λ q → q ; from-to = λ _ → refl ; to-from = λ _ → refl
    ; to-init = refl ; to-view = λ _ → refl
    ; to-step = λ { (p , q) (inj₁ c) → refl ; (p , q) (inj₂ c) → refl } }

  -- Each side reacts only to its own summand, and the whole machine is the
  -- product of the two machines.
  product : ∀ {A} (p : Prog C₁ A) (q : Prog C₂ A) →
            MIso (S.machine (p ‖ q)) (S₁.machine p ⊗ S₂.machine q)
  product p q = trans-iso
    (parM-iso
      (lift-lemma d₁ d inj₁ decL codecL (λ _ → idle) (λ _ → idle) (λ _ → liftE-idle d₁ d inj₁ decL codecL) p)
      (lift-lemma d₂ d inj₂ decR codecR (λ _ → idle) (λ _ → idle) (λ _ → liftE-idle d₂ d inj₂ decR codecR) q))
    (par-⊗ _ _)
    where
      codecL : ∀ (x : C₁ ⊎ C₂) (c : C₁) → ⌊ d x (inj₁ c) ⌋ ≡ maybe′ (λ y → ⌊ d₁ y c ⌋) false (decL x)
      codecL (inj₁ x) c = ⌊⌋-map′ _ _ (d₁ x c)
      codecL (inj₂ x) c = refl
      codecR : ∀ (x : C₁ ⊎ C₂) (c : C₂) → ⌊ d x (inj₂ c) ⌋ ≡ maybe′ (λ y → ⌊ d₂ y c ⌋) false (decR x)
      codecR (inj₁ x) c = refl
      codecR (inj₂ x) c = ⌊⌋-map′ _ _ (d₂ x c)
