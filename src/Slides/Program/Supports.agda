{-# OPTIONS --safe --without-K #-}

-- What a backend supports: a binding of a subset of the commands.
--
-- A backend has decidable commands `S`, a partial embedding `inj` of the program's commands and a
-- decoder `dec`, inverse where defined.  An explicit record of operations and laws.
--
--   lowerP b   a program over `C` as one over `S`: a supported `await c` becomes `await (inj c)`,
--              an unsupported one is skipped; scenes are kept (`Container.Lowering.lower`)
--   skipU b    the same default inside `C`
--
--   lower-sound      the backend's behaviour for `lowerP b p` on commands `cs` is the behaviour of
--                    `skipU b p` on `mapMaybe dec cs` (an undecodable command does nothing)
--   lower-supported  if every wait of `p` is supported, `skipU b p` is `p`

module Slides.Program.Supports where

open import Level using (0ℓ; lift)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.List.Base using (mapMaybe; []; _∷_)
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

-- Soundness of the lowering

-- A behaviour over the backend's commands behaves as one over the program's commands once each
-- backend command is decoded; one that does not decode does nothing.
module _ {T D C : Set} (b : Supports C) (dC : DecidableEquality C) (O : Setoid 0ℓ 0ℓ)
         (hS : Handler (SceneC T D) (Setoid.Carrier O)) (hS-c : Congruent (SceneC T D) O hS)
         (blank : Setoid.Carrier O) where
  private module O = Setoid O
  import Slides.Program.Sem {T} {D} {C} dC O hS hS-c blank as SC
  import Slides.Program.Sem {T} {D} {S b} (_≟S_ b) O hS hS-c blank as SS

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

  -- a supported wait, on decoded commands: the same wait on the same rest
  wait-sound : ∀ {c s} → inj b c ≡ just s → (kS : SS.Beh) (kC : SC.Beh) →
               (∀ cs → kS cs O.≈ kC (mapMaybe (dec b) cs)) →
               ∀ cs → SS.awaitB s kS cs O.≈ SC.awaitB c kC (mapMaybe (dec b) cs)
  wait-sound e kS kC h [] = O.refl
  wait-sound {c} {s} e kS kC h (s′ ∷ cs) with dec b s′ in e′
  ... | nothing rewrite coh-none e e′ = wait-sound e kS kC h cs
  ... | just c′ rewrite coh-just e e′ with ⌊ dC c′ c ⌋
  ...   | true  = h cs
  ...   | false = wait-sound e kS kC h cs

  lower-sound : ∀ {A} (ls : A → SS.Beh) (lc : A → SC.Beh) →
                (∀ a cs → ls a cs O.≈ lc a (mapMaybe (dec b) cs)) →
                ∀ p cs → SS.sem ls (lowerP b p) cs O.≈ SC.sem lc (skipU b p) (mapMaybe (dec b) cs)
  lower-sound ls lc l (pure a) = l a
  lower-sound ls lc l (impure (inj₁ o , k)) cs = hS-c o (λ q → lower-sound ls lc l (k q) cs)
  lower-sound ls lc l (impure (inj₂ c , k)) with inj b c in e
  ... | nothing rewrite lowerP-nothing b c k e | skipU-nothing b c k e = lower-sound ls lc l (k tt)
  ... | just s rewrite lowerP-just b {s = s} c k e | skipU-just b {s = s} c k e =
    wait-sound e _ _ (lower-sound ls lc l (k tt))

  -- with every wait supported the backend behaviour is the program's, decoded
  lower-supported-sound : ∀ {A} (ls : A → SS.Beh) (lc : A → SC.Beh) →
                          (∀ a cs → ls a cs O.≈ lc a (mapMaybe (dec b) cs)) →
                          ∀ p → AllSup b p → ∀ cs → SS.sem ls (lowerP b p) cs O.≈ SC.sem lc p (mapMaybe (dec b) cs)
  lower-supported-sound ls lc l p a cs =
    O.trans (lower-sound ls lc l p cs) (SC.sem-cong (lower-supported b p a) _)
