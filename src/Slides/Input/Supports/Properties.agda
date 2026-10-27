{-# OPTIONS --safe --without-K #-}

-- Whole-program lowering soundness.
--
--   lower-sound     for every deck, the machine of its lowering to the backend is the
--                   machine of `skipDeck p` (unsupported awaits removed), seen through the
--                   decoder `dec` (backend commands that do not decode are ignored)
--   lower-supported if every `await` of `p` is supported, `skipDeck p` behaves as `p`, so
--                   the backend runs exactly the generic machine
--   unsupported-skipped, supported-kept    the per-operation statements
--
-- Both are up to `MIso` (`Slides.Input.Machine.Properties`).  Lowering a deck with only
-- supported commands is therefore the identity on behaviour; an unsupported `await` is
-- skipped, and navigation is never unsupported on a backend that is `NavTotal`.

module Slides.Input.Supports.Properties (V : Set) where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base using (_,_; _×_; Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; sym; trans)

open import Slides.Input V
open import Slides.Input.Machine V
open Machine
open import Slides.Input.Machine.Properties V
open import Slides.Input.Supports V
open Supports

module _ {C : Set} (b : Supports C) where

  supported-kept : ∀ k s {A} (r : ⊤ → Deck C A) → inj b k ≡ just s →
    lowerDeck b (impure (inj₂ (inj₁ k) , r)) ≡ impure (inj₂ (inj₁ s) , λ q → lowerDeck b (r q))
  supported-kept k s r e rewrite e = refl

  unsupported-skipped : ∀ k {A} (r : ⊤ → Deck C A) → inj b k ≡ nothing →
    lowerDeck b (impure (inj₂ (inj₁ k) , r)) ≡ lowerDeck b (r tt)
  unsupported-skipped k r e rewrite e = refl

  skip-supported : ∀ k s {A} (r : ⊤ → Deck C A) → inj b k ≡ just s →
    skipDeck b (impure (inj₂ (inj₁ k) , r)) ≡ impure (inj₂ (inj₁ k) , λ q → skipDeck b (r q))
  skip-supported k s r e rewrite e = refl

  skip-unsupported : ∀ k {A} (r : ⊤ → Deck C A) → inj b k ≡ nothing →
    skipDeck b (impure (inj₂ (inj₁ k) , r)) ≡ skipDeck b (r tt)
  skip-unsupported k r e rewrite e = refl

  -- Every `await` of a deck is supported.
  Supported : ∀ {A} → Deck C A → Set
  Supported (pure _)                       = ⊤
  Supported (impure (inj₁ _ , k))          = Supported (k tt)
  Supported (impure (inj₂ (inj₁ c) , k))   = (Σ[ s ∈ S b ] inj b c ≡ just s) × Supported (k tt)
  Supported (impure (inj₂ (inj₂ _) , k))   = Supported (k tt)

  module _ (dK : DecidableEquality (Nav ⊎ C)) where
    private dS = _≟S_ b

    -- `x` is the backend command of `k` exactly when `x` decodes to `k`.
    coh : ∀ k s → inj b k ≡ just s →
          ∀ x → ⌊ dS x s ⌋ ≡ maybe′ (λ y → ⌊ dK y k ⌋) false (dec b x)
    coh k s e x with dec b x in eq | dS x s
    ... | just y  | yes refl with just-injective (trans (sym eq) (dec-inj b e))
    ...   | refl with dK y y
    ...     | yes _ = refl
    ...     | no ¬p = ⊥-elim (¬p refl)
    coh k s e x | just y  | no ¬x with dK y k
    ... | no _      = refl
    ... | yes refl  = ⊥-elim (¬x (just-injective (trans (sym (inj-dec b eq)) e)))
    coh k s e x | nothing | yes refl with trans (sym eq) (dec-inj b e)
    ... | ()
    coh k s e x | nothing | no _ = refl

    lower-sound : ∀ {A} (l : A → Machine (Nav ⊎ C)) (l′ : A → Machine (S b))
                  (hl : ∀ a → MIso (l′ a) (liftE (dec b) (l a))) (p : Deck C A) →
                  MIso (sem dS l′ (lowerDeck b p)) (liftE (dec b) (sem dK l (skipDeck b p)))
    lower-sound l l′ hl (pure a) = hl a
    lower-sound l l′ hl (impure (inj₁ v , k)) = showM-iso v (lower-sound l l′ hl (k tt))
    lower-sound l l′ hl (impure (inj₂ (inj₂ _) , k)) = lower-sound l l′ hl (k tt)
    lower-sound l l′ hl (impure (inj₂ (inj₁ c) , k)) with inj b c in e
    ... | just s rewrite supported-kept c s k e | skip-supported c s k e =
      trans-iso (awaitM-iso dS s (lower-sound l l′ hl (k tt)))
                (liftE-await dK dS (dec b) c s (coh c s e) (sem dK l (skipDeck b (k tt))))
    ... | nothing rewrite unsupported-skipped c k e | skip-unsupported c k e =
      lower-sound l l′ hl (k tt)

    -- Skipping changes nothing when every `await` is supported.
    skip-sem : ∀ {A} (l : A → Machine (Nav ⊎ C)) (p : Deck C A) → Supported p →
               MIso (sem dK l (skipDeck b p)) (sem dK l p)
    skip-sem l (pure a) _ = refl-iso
    skip-sem l (impure (inj₁ v , k)) sp = showM-iso v (skip-sem l (k tt) sp)
    skip-sem l (impure (inj₂ (inj₂ _) , k)) sp = skip-sem l (k tt) sp
    skip-sem l (impure (inj₂ (inj₁ c) , k)) ((s , e) , sp)
      rewrite skip-supported c s k e = awaitM-iso dK c (skip-sem l (k tt) sp)

    lower-supported : ∀ {A} (p : Deck C A) → Supported p →
      MIso (machine dS (lowerDeck b p)) (liftE (dec b) (machine dK p))
    lower-supported p sp =
      trans-iso (lower-sound (λ _ → idle) (λ _ → idle) (λ _ → liftE-idle (dec b)) p)
        (liftE-iso (dec b) (skip-sem (λ _ → idle) p sp))
