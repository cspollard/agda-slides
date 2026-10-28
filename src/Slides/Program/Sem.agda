{-# OPTIONS --safe --without-K #-}

-- The meaning of a program: a Moore machine, by a fold.
--
-- A scene algebra on the output (`hS`, congruent for the output setoid `O`) says what a scene
-- operation does to the outputs of its children; `blank` is the output of a machine that is
-- waiting for its first command.  The fold of the program signature into machines is
--
--   scene op o, children k   the product machine: every child sees every command, the output is
--                            `hS o` of the children's outputs (a synchronous product: `Par`
--                            of two programs that wait both wait for the same commands)
--   await c ; k              waits in a blank state; `c` moves to the start of `k`, any other
--                            command is ignored
--   pure a                   the leaf machine given by `l a`
--
-- Laws (machine equality is bisimilarity, `Slides.Program.Machine`):
--
--   sem-bind       the fold is a monad morphism: grafting leaves commutes with it
--   inject-const   a program that never waits is a constant machine, with the scene's meaning
--   await-step, await-ignore   the transitions of a wait
--
-- Both are instances of the generic lemmas of `Container.Interpret.Plain`.

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Container.Interpret.Plain using (Handler; Congruent)
open import Slides.Scene.Syntax using (SceneC)

module Slides.Program.Sem {T D C : Set} (dC : DecidableEquality C) (O : Setoid 0ℓ 0ℓ)
       (hS : Handler (SceneC T D) (Setoid.Carrier O)) (hS-c : Congruent (SceneC T D) O hS)
       (blank : Setoid.Carrier O) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Container.Interpret.Plain using (pfold; pfold-bind; pfold-cong; pfold-ext; pfold-rel-translate)
open import Container.Lowering.Properties using (_≈⋆_)
open import Container.Sum using (inl)
open import Slides.Scene.Syntax using (Scene; Op; arity)
open import Slides.Program.Syntax
open import Slides.Program.Machine
private module O = Setoid O
open Machine

------------------------------------------------------------------------
-- The machine algebra

Mach : Set₁
Mach = Machine C O.Carrier

constM : O.Carrier → Mach
constM x = record { State = ⊤ ; init = tt ; step = λ q _ → q ; out = λ _ → x }

prodM : (o : Op T D) → (arity o → Mach) → Mach
prodM o k = record
  { State = ∀ q → State (k q) ; init = λ q → init (k q)
  ; step = λ s c q → step (k q) (s q) c ; out = λ s → hS o (λ q → out (k q) (s q)) }

awaitM : C → Mach → Mach
awaitM c M = record
  { State = ⊤ ⊎ State M ; init = inj₁ tt
  ; step = λ { (inj₁ _) c′ → if ⌊ dC c′ c ⌋ then inj₂ (init M) else inj₁ tt
             ; (inj₂ q) c′ → inj₂ (step M q c′) }
  ; out = λ { (inj₁ _) → blank ; (inj₂ q) → out M q } }

hP : Handler (ProgC T D C) Mach
hP (inj₁ o) k = prodM o k
hP (inj₂ c) k = awaitM c (k tt)

-- the relation of a wait: blank with blank, or related states
RA : ∀ {M N : Mach} → Bisim O M N → ⊤ ⊎ State M → ⊤ ⊎ State N → Set
RA b (inj₁ _) (inj₁ _) = ⊤
RA b (inj₂ p) (inj₂ q) = R b p q
RA b _        _        = ⊥

hP-cong : Congruent (ProgC T D C) (MachineS O C) hP
hP-cong (inj₁ o) {k} {k′} e = record
  { R = λ s t → ∀ q → R (e q) (s q) (t q)
  ; R-init = λ q → R-init (e q)
  ; R-out = λ r → hS-c o (λ q → R-out (e q) (r q))
  ; R-step = λ r c q → R-step (e q) (r q) c }
hP-cong (inj₂ c) {k} {k′} e = record
  { R = RA b ; R-init = tt
  ; R-out = λ { {inj₁ _} {inj₁ _} _ → O.refl ; {inj₂ _} {inj₂ _} r → R-out b r }
  ; R-step = λ { {inj₁ _} {inj₁ _} _ c′ → cond (⌊ dC c′ c ⌋)
               ; {inj₂ _} {inj₂ _} r c′ → R-step b r c′ } }
  where
    b = e tt
    cond : ∀ x → RA b (if x then inj₂ (init (k tt)) else inj₁ tt) (if x then inj₂ (init (k′ tt)) else inj₁ tt)
    cond true  = R-init b
    cond false = tt

-- the meaning of a program whose leaves mean `l a`
sem : ∀ {A : Set} → (A → Mach) → Program T D C A → Mach
sem = pfold (ProgC T D C) hP

sem-cong : ∀ {A} {l : A → Mach} {p q : Program T D C A} → p ≈⋆ q → Bisim O (sem l p) (sem l q)
sem-cong = pfold-cong (MachineS O C) hP-cong

sem-ext : ∀ {A} {l l′ : A → Mach} → (∀ a → Bisim O (l a) (l′ a)) → ∀ p → Bisim O (sem l p) (sem l′ p)
sem-ext = pfold-ext (MachineS O C) hP-cong

-- The bind law: the fold of a substitution is the fold with the substituted programs folded.
sem-bind : ∀ {A B} (l : B → Mach) (f : A → Program T D C B) (p : Program T D C A) →
           Bisim O (sem l (p >>= f)) (sem (λ a → sem l (f a)) p)
sem-bind l f = pfold-bind (MachineS O C) hP-cong f (λ a → bisim-refl O)

------------------------------------------------------------------------
-- Waiting

sem-await : ∀ {A} (l : A → Mach) (k : Program T D C A) (c : C) →
            sem l (await c >>= λ _ → k) ≡ awaitM c (sem l k)
sem-await l k c = refl

private
  ⌊⌋-refl : ∀ c → ⌊ dC c c ⌋ ≡ true
  ⌊⌋-refl c with dC c c
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  ⌊⌋-no : ∀ {c c′} → (c′ ≡ c → ⊥) → ⌊ dC c′ c ⌋ ≡ false
  ⌊⌋-no {c} {c′} n with dC c′ c
  ... | yes e = ⊥-elim (n e)
  ... | no _  = refl

-- the awaited command moves a waiting machine to the start of the rest; others are ignored
await-step : ∀ M c → step (awaitM c M) (init (awaitM c M)) c ≡ inj₂ (init M)
await-step M c rewrite ⌊⌋-refl c = refl

await-ignore : ∀ M {c c′} → (c′ ≡ c → ⊥) → step (awaitM c M) (init (awaitM c M)) c′ ≡ inj₁ tt
await-ignore M n rewrite ⌊⌋-no n = refl

------------------------------------------------------------------------
-- A scene is a program that never waits

-- the algebra of constant machines is the scene algebra
inject-const : ∀ {A : Set} (f : A → O.Carrier) (s : Scene T D A) →
               Bisim O (sem (λ a → constM (f a)) (inject s)) (constM (pfold (SceneC T D) hS f s))
inject-const f s = pfold-rel-translate inl (λ x M → Bisim O M (constM x)) hom (λ a → bisim-refl O) s
  where
    hom : ∀ o (k′ : arity o → O.Carrier) k → (∀ q → Bisim O (k q) (constM (k′ q))) →
          Bisim O (prodM o k) (constM (hS o k′))
    hom o k′ k e = record
      { R = λ s _ → ∀ q → R (e q) (s q) tt ; R-init = λ q → R-init (e q)
      ; R-out = λ r → hS-c o (λ q → R-out (e q) (r q)) ; R-step = λ r c q → R-step (e q) (r q) c }
