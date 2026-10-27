{-# OPTIONS --safe --without-K #-}

-- Laws of navigation and of the label table.
--
--   labelTable-label   `label l` resolves to the position where it stands
--   labelTable-next    an `await next` shifts every label of the rest by one
--   gotoLabel-goto     resolving a label then moving is `goto` its index
--   gotoLabel-view     ... and shows the deck replayed by that many `next`s
--   view-next, prev-next   `next` is replay one more step; `prev` undoes `next`

module Slides.Input.Navigation.Properties (V : Set) where

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Base as Maybe using ()
open import Data.Nat.Base using (ℕ; suc; _⊓_; _≤_)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans)
import Data.String.Properties as Str

open import Slides.Input V
open import Slides.Input.Machine V
open Machine
open import Slides.Input.Navigation V

private
  ≟-refl : ∀ l → ⌊ l Str.≟ l ⌋ ≡ true
  ≟-refl l with l Str.≟ l
  ... | yes _ = refl
  ... | no ¬p = Data.Empty.⊥-elim (¬p refl)
    where import Data.Empty

module _ {C : Set} where

  labelFrom-label : ∀ n l {A} (p : Deck C A) →
    labelFrom n (impure (inj₂ (inj₂ l) , λ _ → p)) l ≡ just n
  labelFrom-label n l p rewrite ≟-refl l = refl

  labelTable-label : ∀ l {A} (p : Deck C A) → labelTable (label l ⨾ p) l ≡ just 0
  labelTable-label l p = labelFrom-label 0 l p

  -- Shifting the preceding count shifts the table.
  labelFrom-shift : ∀ n {A} (p : Deck C A) l →
    labelFrom (suc n) p l ≡ Maybe.map suc (labelFrom n p l)
  labelFrom-shift n (pure _) l = refl
  labelFrom-shift n (impure (inj₁ _ , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ next)) , k)) l = labelFrom-shift (suc n) (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ prev)) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ first)) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ last)) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ (goto _))) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₁ (gotoLabel _))) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₁ (inj₂ _)) , k)) l = labelFrom-shift n (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₂ l′) , k)) l with ⌊ l′ Str.≟ l ⌋
  ... | true  = refl
  ... | false = labelFrom-shift n (k tt) l

  labelTable-next : ∀ {A} (p : Deck C A) l →
    labelTable (pause ⨾ p) l ≡ Maybe.map suc (labelTable p l)
  labelTable-next p l = labelFrom-shift 0 p l

module _ {C : Set} (M : Machine (Nav ⊎ C)) (len : ℕ) (tbl : String → Maybe ℕ) where

  gotoLabel-goto : ∀ n l i → tbl l ≡ just i →
    navStep M len tbl n (gotoLabel l) ≡ navStep M len tbl n (goto i)
  gotoLabel-goto n l i e rewrite e = refl

  gotoLabel-view : ∀ n l i → tbl l ≡ just i →
    view (navM M len tbl) (navStep M len tbl n (gotoLabel l)) ≡ view M (replay M (i ⊓ len))
  gotoLabel-view n l i e rewrite e = refl

  view-next : ∀ n → suc n ≤ len →
    view (navM M len tbl) (navStep M len tbl n next) ≡ view M (step M (replay M n) (inj₁ next))
  view-next n le = cong (λ k → view M (replay M k)) (m≤n⇒m⊓n≡m le)

  prev-next : ∀ n → suc n ≤ len → navStep M len tbl (navStep M len tbl n next) prev ≡ n
  prev-next n le rewrite m≤n⇒m⊓n≡m le = refl
