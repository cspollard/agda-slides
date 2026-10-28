{-# OPTIONS --safe --without-K #-}

-- What a backend supports: a binding of a subset of the commands.
--
-- A backend has its own set of commands `S` (decidable), a partial embedding `inj` of the
-- program's commands into it and the decoder `dec` back, inverse to each other where defined, so
-- two commands never share a backend command.  Like the scalar theories it is an explicit
-- record of operations and laws; there is no instance search.
--
--   lowerP b     a program over `C` as a program over `S`: a supported `await c` becomes
--                `await (inj c)`, an unsupported one is skipped (the documented default);
--                scenes are kept.  It is `Container.Lowering.lower`, so a monad morphism.
--   skipU b      the same default inside `C`: unsupported waits removed.
--
--   lower-sound      the backend's machine for `lowerP b p`, with its commands decoded by `dec`
--                    (`Via`: an undecodable command does nothing), is the machine of `skipU b p`
--   lower-supported  if every wait of `p` is supported, `skipU b p` is `p`
--
-- Same statements as the legacy `Slides.Input.Supports.Properties`, for the new fold.

module Slides.Program.Supports where

open import Level using (0ℓ; lift)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product.Base using (_×_; _,_; Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Maybe.Properties using (just-injective)

open import Container.Interpret.Plain using (Handler; Congruent)
open import Container.Lowering using (Lowering; lower)
open import Container.Lowering.Properties using (_≈⋆_)
open import Slides.Scene.Syntax using (SceneC; arity)
open import Slides.Program.Syntax
open import Slides.Program.Machine

record Supports (C : Set) : Set₁ where
  field
    S       : Set
    _≟S_    : DecidableEquality S
    inj     : C → Maybe S
    dec     : S → Maybe C
    dec-inj : ∀ {c s} → inj c ≡ just s → dec s ≡ just c
    inj-dec : ∀ {c s} → dec s ≡ just c → inj c ≡ just s
open Supports

-- a backend that supports every command, unchanged
idSupports : ∀ {C} → DecidableEquality C → Supports C
idSupports d = record { S = _ ; _≟S_ = d ; inj = just ; dec = just
                      ; dec-inj = λ { refl → refl } ; inj-dec = λ { refl → refl } }

-- a backend with no commands (a print backend): everything is skipped
noSupports : ∀ {C} → Supports C
noSupports = record { S = ⊥ ; _≟S_ = λ () ; inj = λ _ → nothing ; dec = λ () ; dec-inj = λ ()
                    ; inj-dec = λ { {s = ()} } }

module _ {T D C : Set} (b : Supports C) where

  lowerOp : Lowering (ProgC T D C) (ProgC T D (S b))
  lowerOp (inj₁ o) = impure (inj₁ o , pure)
  lowerOp (inj₂ c) = maybe′ (λ s → await s) (pure tt) (inj b c)

  lowerP : ∀ {A} → Program T D C A → Program T D (S b) A
  lowerP = lower lowerOp

  skipUOp : Lowering (ProgC T D C) (ProgC T D C)
  skipUOp (inj₁ o) = impure (inj₁ o , pure)
  skipUOp (inj₂ c) = maybe′ (λ _ → await c) (pure tt) (inj b c)

  skipU : ∀ {A} → Program T D C A → Program T D C A
  skipU = lower skipUOp

  -- every wait of the program is supported
  AllSup : ∀ {A} → Program T D C A → Set
  AllSup (pure _)              = ⊤
  AllSup (impure (inj₁ _ , k)) = ∀ q → AllSup (k q)
  AllSup (impure (inj₂ c , k)) = (inj b c ≡ nothing → ⊥) × AllSup (k tt)

  lowerP-just : ∀ {A} {s} c (k : ⊤ → Program T D C A) → inj b c ≡ just s →
                lowerP (impure (inj₂ c , k)) ≡ impure (inj₂ s , λ _ → lowerP (k tt))
  lowerP-just c k e rewrite e = refl

  lowerP-nothing : ∀ {A} c (k : ⊤ → Program T D C A) → inj b c ≡ nothing →
                   lowerP (impure (inj₂ c , k)) ≡ lowerP (k tt)
  lowerP-nothing c k e rewrite e = refl

  skipU-just : ∀ {A} {s} c (k : ⊤ → Program T D C A) → inj b c ≡ just s →
               skipU (impure (inj₂ c , k)) ≡ impure (inj₂ c , λ _ → skipU (k tt))
  skipU-just c k e rewrite e = refl

  skipU-nothing : ∀ {A} c (k : ⊤ → Program T D C A) → inj b c ≡ nothing →
                  skipU (impure (inj₂ c , k)) ≡ skipU (k tt)
  skipU-nothing c k e rewrite e = refl

  -- nothing to skip when everything is supported
  lower-supported : ∀ {A} (p : Program T D C A) → AllSup p → skipU p ≈⋆ p
  lower-supported (pure _) _ = lift refl
  lower-supported (impure (inj₁ o , k)) a = refl , λ q → lower-supported (k q) (a q)
  lower-supported (impure (inj₂ c , k)) (n , a) with inj b c in e
  ... | nothing = ⊥-elim (n refl)
  ... | just s rewrite skipU-just {s = s} c k e = refl , λ _ → lower-supported (k tt) a

------------------------------------------------------------------------
-- Soundness of the lowering

-- A machine over the backend's commands behaves as one over the program's commands once each
-- backend command is decoded; one that does not decode does nothing.
module _ {S C : Set} (O : Setoid 0ℓ 0ℓ) (d : S → Maybe C) where
  private module O = Setoid O

  record Via (M : Machine S O.Carrier) (N : Machine C O.Carrier) : Set₁ where
    field
      R      : State M → State N → Set
      R-init : R (init M) (init N)
      R-out  : ∀ {p q} → R p q → out M p O.≈ out N q
      R-just : ∀ {p q s c} → R p q → d s ≡ just c → R (step M p s) (step N q c)
      R-none : ∀ {p q s} → R p q → d s ≡ nothing → R (step M p s) q
  open Via public

  -- a `Via` simulation can be followed by a bisimulation
  via-bisim : ∀ {M N N′} → Via M N → Bisim O N N′ → Via M N′
  via-bisim v b = record
    { R = λ p q′ → Σ[ q ∈ _ ] R v p q × R b q q′
    ; R-init = _ , R-init v , R-init b
    ; R-out = λ { (_ , x , y) → O.trans (R-out v x) (R-out b y) }
    ; R-just = λ { (_ , x , y) e → _ , R-just v x e , R-step b y _ }
    ; R-none = λ { (_ , x , y) e → _ , R-none v x e , y } }

module _ {T D C : Set} (b : Supports C) (dC : DecidableEquality C) (O : Setoid 0ℓ 0ℓ)
         (hS : Handler (SceneC T D) (Setoid.Carrier O)) (hS-c : Congruent (SceneC T D) O hS)
         (blank : Setoid.Carrier O) where
  private module O = Setoid O
  import Slides.Program.Sem {T} {D} {C} dC O hS hS-c blank as SC
  import Slides.Program.Sem {T} {D} {S b} (_≟S_ b) O hS hS-c blank as SS

  private
    RV : ∀ {M N : Machine (S b) O.Carrier} → ⊤ ⊎ State M → ⊤ ⊎ State N → Set
    RV (inj₁ _) (inj₁ _) = ⊤
    RV _ _ = ⊥

  -- the backend command and the program command agree on what a wait waits for
  coh-just : ∀ {c s s′ c′} → inj b c ≡ just s → dec b s′ ≡ just c′ → ⌊ _≟S_ b s′ s ⌋ ≡ ⌊ dC c′ c ⌋
  coh-just {c} {s} {s′} {c′} e e′ with _≟S_ b s′ s | dC c′ c
  ... | yes _ | yes _ = refl
  ... | no _  | no _  = refl
  ... | yes refl | no n = ⊥-elim (n (just-injective (trans (sym e′) (dec-inj b e))))
  ... | no n | yes refl = ⊥-elim (n (just-injective (trans (sym (inj-dec b e′)) e)))

  coh-none : ∀ {c s s′} → inj b c ≡ just s → dec b s′ ≡ nothing → ⌊ _≟S_ b s′ s ⌋ ≡ false
  coh-none {c} {s} {s′} e e′ with _≟S_ b s′ s
  ... | no _     = refl
  ... | yes refl = ⊥-elim (absurd (trans (sym e′) (dec-inj b e)))
    where absurd : nothing ≡ just c → ⊥
          absurd ()

  lower-sound : ∀ {A} (ls : A → SS.Mach) (lc : A → SC.Mach) → (∀ a → Via O (dec b) (ls a) (lc a)) →
                ∀ p → Via O (dec b) (SS.sem ls (lowerP b p)) (SC.sem lc (skipU b p))
  lower-sound ls lc l (pure a) = l a
  lower-sound ls lc l (impure (inj₁ o , k)) = record
    { R = λ s t → ∀ q → R (ih q) (s q) (t q)
    ; R-init = λ q → R-init (ih q)
    ; R-out = λ r → hS-c o (λ q → R-out (ih q) (r q))
    ; R-just = λ r e q → R-just (ih q) (r q) e
    ; R-none = λ r e q → R-none (ih q) (r q) e }
    where ih = λ q → lower-sound ls lc l (k q)
  lower-sound ls lc l (impure (inj₂ c , k)) with inj b c in e
  ... | nothing rewrite lowerP-nothing b c k e | skipU-nothing b c k e = lower-sound ls lc l (k tt)
  ... | just s rewrite lowerP-just b {s = s} c k e | skipU-just b {s = s} c k e = record
    { R = RW ; R-init = tt
    ; R-out = λ { {inj₁ _} {inj₁ _} _ → O.refl ; {inj₂ _} {inj₂ _} r → R-out ih r }
    ; R-just = λ { {inj₁ _} {inj₁ _} _ e′ → wj e′ ; {inj₂ _} {inj₂ _} r e′ → R-just ih r e′ }
    ; R-none = λ { {inj₁ _} {inj₁ _} _ e′ → wn e′ ; {inj₂ _} {inj₂ _} r e′ → R-none ih r e′ } }
    where
      ih = lower-sound ls lc l (k tt)
      RW : ⊤ ⊎ _ → ⊤ ⊎ _ → Set
      RW (inj₁ _) (inj₁ _) = ⊤
      RW (inj₂ p) (inj₂ q) = R ih p q
      RW _ _ = ⊥
      cond : ∀ x → RW (if x then inj₂ (init (SS.sem ls (lowerP b (k tt)))) else inj₁ tt)
                      (if x then inj₂ (init (SC.sem lc (skipU b (k tt)))) else inj₁ tt)
      cond true  = R-init ih
      cond false = tt
      wj : ∀ {s′ c′} → dec b s′ ≡ just c′ →
           RW (if ⌊ _≟S_ b s′ s ⌋ then inj₂ (init (SS.sem ls (lowerP b (k tt)))) else inj₁ tt)
              (if ⌊ dC c′ c ⌋ then inj₂ (init (SC.sem lc (skipU b (k tt)))) else inj₁ tt)
      wj {c′ = c′} e′ rewrite coh-just e e′ = cond ⌊ dC c′ c ⌋
      wn : ∀ {s′} → dec b s′ ≡ nothing →
           RW (if ⌊ _≟S_ b s′ s ⌋ then inj₂ (init (SS.sem ls (lowerP b (k tt)))) else inj₁ tt) (inj₁ tt)
      wn e′ rewrite coh-none e e′ = tt

  -- with every wait supported the backend machine is the program's machine, decoded
  lower-supported-sound : ∀ {A} (ls : A → SS.Mach) (lc : A → SC.Mach) → (∀ a → Via O (dec b) (ls a) (lc a)) →
                          ∀ p → AllSup b p → Via O (dec b) (SS.sem ls (lowerP b p)) (SC.sem lc p)
  lower-supported-sound ls lc l p a =
    via-bisim O (dec b) (lower-sound ls lc l p) (SC.sem-cong (lower-supported b p a))
