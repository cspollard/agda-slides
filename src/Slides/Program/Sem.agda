{-# OPTIONS --safe --without-K #-}

-- The meaning of a program: its behaviour, by a fold.
--
--   commands so far --> scene reading
--
-- Behaviours `List C → O` are the final Moore machine (`Slides.Program.Machine`), and with a scene
-- algebra `hS` on `O` (congruent), a leaf behaviour `l a`, they are an algebra of the program
-- signature: the fold is `sem`, the unique map out of the free monad.
--
--   scene op o, children k   the synchronous product (`prodB`): every child sees every command; the
--                            output is `hS o` of theirs (`Par` of two waiting programs waits for both)
--   await c ; k              blank until `c` arrives, then `k` on the rest (`awaitB`); other commands
--                            are ignored
--   pure a                   `l a`
--
-- The product is the product of the machines' lenses along the diagonal `C → C × C`; the fold is
-- a distributive law of the scene algebra over the machine coalgebra, so a congruent `hS` gives a
-- congruent fold.
--
--   sem-bind               the fold is a monad morphism: grafting leaves commutes with it
--   inject-const           a program that never waits is a constant behaviour, the scene's meaning
--   await-hit, await-miss  the awaited command starts the rest; others change nothing
--
-- Equality of behaviours is pointwise (`BehS`), which is trace equality of machines.

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
open import Data.List.Base using (List; []; _∷_)
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
open import Slides.Program.Machine using (BehS)
private module O = Setoid O

-- The behaviour algebra

Beh : Set
Beh = List C → O.Carrier

constB : O.Carrier → Beh
constB x _ = x

prodB : (o : Op T D) → (arity o → Beh) → Beh
prodB o k cs = hS o (λ q → k q cs)

awaitB : C → Beh → Beh
awaitB c k []        = blank
awaitB c k (c′ ∷ cs) = if ⌊ dC c′ c ⌋ then k cs else awaitB c k cs

hP : Handler (ProgC T D C) Beh
hP (inj₁ o) k = prodB o k
hP (inj₂ c) k = awaitB c (k tt)

awaitB-cong : ∀ c {k k′ : Beh} → (∀ cs → k cs O.≈ k′ cs) → ∀ cs → awaitB c k cs O.≈ awaitB c k′ cs
awaitB-cong c e []        = O.refl
awaitB-cong c e (c′ ∷ cs) with ⌊ dC c′ c ⌋
... | true  = e cs
... | false = awaitB-cong c e cs

hP-cong : Congruent (ProgC T D C) (BehS O C) hP
hP-cong (inj₁ o) e cs = hS-c o (λ q → e q cs)
hP-cong (inj₂ c) e    = awaitB-cong c (e tt)

-- the meaning of a program whose leaves mean `l a`
sem : ∀ {A : Set} → (A → Beh) → Program T D C A → Beh
sem = pfold (ProgC T D C) hP

sem-cong : ∀ {A} {l : A → Beh} {p q : Program T D C A} → p ≈⋆ q → ∀ cs → sem l p cs O.≈ sem l q cs
sem-cong = pfold-cong (BehS O C) hP-cong

sem-ext : ∀ {A} {l l′ : A → Beh} → (∀ a cs → l a cs O.≈ l′ a cs) → ∀ p cs → sem l p cs O.≈ sem l′ p cs
sem-ext = pfold-ext (BehS O C) hP-cong

-- The bind law: the fold of a substitution is the fold with the substituted programs folded.
sem-bind : ∀ {A B} (l : B → Beh) (f : A → Program T D C B) (p : Program T D C A) →
           ∀ cs → sem l (p >>= f) cs O.≈ sem (λ a → sem l (f a)) p cs
sem-bind l f = pfold-bind (BehS O C) hP-cong f (λ a cs → O.refl)

-- Waiting

sem-await : ∀ {A} (l : A → Beh) (k : Program T D C A) (c : C) →
            sem l (await c >>= λ _ → k) ≡ awaitB c (sem l k)
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

-- the awaited command starts the rest on what follows; others are ignored
await-hit : ∀ k c cs → awaitB c k (c ∷ cs) ≡ k cs
await-hit k c cs rewrite ⌊⌋-refl c = refl

await-miss : ∀ k {c c′} cs → (c′ ≡ c → ⊥) → awaitB c k (c′ ∷ cs) ≡ awaitB c k cs
await-miss k cs n rewrite ⌊⌋-no n = refl

-- A scene is a program that never waits

-- the algebra of constant behaviours is the scene algebra
inject-const : ∀ {A : Set} (f : A → O.Carrier) (s : Scene T D A) →
               ∀ cs → sem (λ a → constB (f a)) (inject s) cs O.≈ pfold (SceneC T D) hS f s
inject-const f s = pfold-rel-translate inl (λ x b → ∀ cs → b cs O.≈ x) hom (λ a cs → O.refl) s
  where
    hom : ∀ o (k′ : arity o → O.Carrier) k → (∀ q cs → k q cs O.≈ k′ q) →
          ∀ cs → prodB o k cs O.≈ hS o k′
    hom o k′ k e cs = hS-c o (λ q → e q cs)
