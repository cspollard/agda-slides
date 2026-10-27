{-# OPTIONS --safe --without-K #-}

-- Laws of navigation and of the label table.
--
--   labelTable-label   `label l` resolves to the position where it stands
--   labelTable-next    an `await next` shifts every label of the rest by one
--   nextCount-bind, labelFrom-bind   the count of a sequence is the sum; its table is the first
--                      program's, then the second's shifted by the nexts before it
--   gotoLabel-goto     resolving a label then moving is `goto` its index
--   view-next, prev-next   `next` is replay one more step; `prev` undoes `next`

module Slides.Input.Navigation.Properties (V : Set) where

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _<∣>_)
open import Data.Maybe.Base as Maybe using ()
open import Data.Nat.Base using (ℕ; suc; _+_; _⊓_; _≤_)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m; +-assoc; +-identityʳ)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)
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
  labelFrom-shift n (impure (inj₂ (inj₁ c) , k)) l = labelFrom-shift (n + δ c) (k tt) l
  labelFrom-shift n (impure (inj₂ (inj₂ l′) , k)) l with ⌊ l′ Str.≟ l ⌋
  ... | true  = refl
  ... | false = labelFrom-shift n (k tt) l

  labelTable-next : ∀ {A} (p : Deck C A) l →
    labelTable (pause ⨾ p) l ≡ Maybe.map suc (labelTable p l)
  labelTable-next p l = labelFrom-shift 0 p l

  -- Sequencing: the counts add, and the table of `x ; f` is that of `x`, else that of `f`
  -- shifted by the nexts of `x`.
  nextCount-bind : ∀ {A} (x : Deck C ⊤) (f : ⊤ → Deck C A) →
    nextCount (x >>= f) ≡ nextCount x + nextCount (f tt)
  nextCount-bind (pure _) f = refl
  nextCount-bind (impure (inj₁ _ , k)) f = nextCount-bind (k tt) f
  nextCount-bind (impure (inj₂ (inj₁ c) , k)) f =
    trans (cong (δ c +_) (nextCount-bind (k tt) f)) (sym (+-assoc (δ c) _ _))
  nextCount-bind (impure (inj₂ (inj₂ _) , k)) f = nextCount-bind (k tt) f

  labelFrom-bind : ∀ n {A} (x : Deck C ⊤) (f : ⊤ → Deck C A) l →
    labelFrom n (x >>= f) l ≡ (labelFrom n x l <∣> labelFrom (n + nextCount x) (f tt) l)
  labelFrom-bind n (pure _) f l rewrite +-identityʳ n = refl
  labelFrom-bind n (impure (inj₁ _ , k)) f l = labelFrom-bind n (k tt) f l
  labelFrom-bind n (impure (inj₂ (inj₁ c) , k)) f l =
    trans (labelFrom-bind (n + δ c) (k tt) f l)
          (cong (λ m → labelFrom (n + δ c) (k tt) l <∣> labelFrom m (f tt) l) (+-assoc n (δ c) _))
  labelFrom-bind n (impure (inj₂ (inj₂ l′) , k)) f l with ⌊ l′ Str.≟ l ⌋
  ... | true  = refl
  ... | false = labelFrom-bind n (k tt) f l

module _ {C : Set} (M : Machine (Nav ⊎ C)) (len : ℕ) (tbl : String → Maybe ℕ) where

  gotoLabel-goto : ∀ n l i → tbl l ≡ just i →
    navStep M len tbl n (gotoLabel l) ≡ navStep M len tbl n (goto i)
  gotoLabel-goto n l i e rewrite e = refl

  view-next : ∀ n → suc n ≤ len →
    view (navM M len tbl) (navStep M len tbl n next) ≡ view M (step M (replay M n) (inj₁ next))
  view-next n le = cong (λ k → view M (replay M k)) (m≤n⇒m⊓n≡m le)

  prev-next : ∀ n → suc n ≤ len → navStep M len tbl (navStep M len tbl n next) prev ≡ n
  prev-next n le rewrite m≤n⇒m⊓n≡m le = refl
