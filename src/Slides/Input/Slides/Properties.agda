{-# OPTIONS --safe --without-K #-}

-- The slide-start table (`Slides.Input.Slides`).
--
-- The specification is independent of the program: slide `i` starts after the pauses and the
-- `next`s between the earlier slides (`entries`, `startOf`).
--
--   slide-table   `labelTable (deckProg d)` is the first match in `entries`: a label resolves to the
--                 start of the first slide that carries it
--   auto-start    the label of slide `i` resolves to the position where slide `i` starts, when no user
--                 label is a numeral (`Fresh`)
--
-- `Slides.Input.Navigation.Properties` supplies the sequencing laws (`labelFrom-bind`,
-- `nextCount-bind`); `gotoLabel-goto` there then makes `gotoLabel (autoLabel i)` the `goto` of the start.

module Slides.Input.Slides.Properties where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; _<∣>_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; z<s; s<s)
open import Data.Nat.Properties using (+-assoc; +-suc; suc-injective; +-identityʳ; m≢1+m+n)
open import Data.Nat.Show using (showInBase)
open import Data.Nat.Show.Properties using (charsInBase-injective)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.String.Base using (String; fromList)
import Data.String.Properties as Str
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; True)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; trans; sym; subst)

open import Data.Container.Core using (Shape)
open import Slides.Core
open import Slides.Input.Deck
open import Slides.Input.Slides
open import Slides.Steps.Input using (elab; elabS)
open import Slides.Input (Shape BlockC) using (Prog)
open import Slides.Input.Navigation (Shape BlockC)
open import Slides.Input.Navigation.Properties (Shape BlockC)

------------------------------------------------------------------------
-- The specification

pauses : Body → ℕ
pauses (pure _)               = 0
pauses (impure (inj₁ _ , k))  = pauses (k tt)
pauses (impure (inj₂ pause , k)) = suc (pauses (k tt))
pauses (impure (inj₂ _ , k))  = pauses (k tt)

-- the labels of a slide that starts at `st`
slideEs : ℕ → ℕ → Maybe String → List (String × ℕ)
slideEs i st nothing  = (autoLabel i , st) ∷ []
slideEs i st (just l) = (autoLabel i , st) ∷ (l , st) ∷ []

-- every label with the start of its slide; slide `i` starts at `st`
entries : ℕ → ℕ → List Slide → List (String × ℕ)
entries i st []             = []
entries i st ((o , b) ∷ ss) = slideEs i st o ++ entries (suc i) (st + pauses b + 1) ss

lookupE : String → List (String × ℕ) → Maybe ℕ
lookupE l []              = nothing
lookupE l ((l′ , n) ∷ es) = if ⌊ l′ Str.≟ l ⌋ then just n else lookupE l es

lookupE-++ : ∀ l es fs → lookupE l (es ++ fs) ≡ (lookupE l es <∣> lookupE l fs)
lookupE-++ l [] fs = refl
lookupE-++ l ((l′ , n) ∷ es) fs with ⌊ l′ Str.≟ l ⌋
... | true  = refl
... | false = lookupE-++ l es fs

-- the start of slide `i` (from `st`)
startOf : ℕ → List Slide → ℕ → ℕ
startOf st []             _       = st
startOf st (_ ∷ _)        zero    = st
startOf st ((_ , b) ∷ ss) (suc i) = startOf (st + pauses b + 1) ss i

------------------------------------------------------------------------
-- Elaborated slides: their awaits and no labels

private
  <∣>-nothing : ∀ {A : Set} (m : Maybe A) → (nothing <∣> m) ≡ m
  <∣>-nothing _ = refl

module _ {C : Set} where

  toProg-bind : ∀ (x : Body⁺ (Nav ⊎ C)) (f : ⊤ → Body⁺ (Nav ⊎ C)) →
    toProg (x >>= f) ≡ (toProg x >>= λ q → toProg (f q))
  toProg-bind (pure _) f = refl
  toProg-bind (impure (inj₁ (inj₁ c) , k)) f = cong (λ w → impure (inj₁ (inj₁ c) , λ _ → w)) (toProg-bind (k tt) f)
  toProg-bind (impure (inj₁ (inj₂ l) , k)) f = cong (λ w → impure (inj₁ (inj₂ l) , λ _ → w)) (toProg-bind (k tt) f)
  toProg-bind (impure (inj₂ (inj₁ a) , k)) f = cong (λ w → impure (inj₂ (inj₁ a) , λ _ → w)) (toProg-bind (k tt) f)
  toProg-bind (impure (inj₂ (inj₂ l) , k)) f = cong (λ w → impure (inj₂ (inj₂ l) , λ _ → w)) (toProg-bind (k tt) f)

  -- The elaborated slide awaits as many `next`s as it has pauses, and carries no label.
  elab-count : ∀ b → nextCount (toProg (elab {C} b)) ≡ pauses b
  elab-count (pure _)                      = refl
  elab-count (impure (inj₁ _ , k))         = elab-count (k tt)
  elab-count (impure (inj₂ pause , k))     = cong suc (elab-count (k tt))
  elab-count (impure (inj₂ (columns _) , k))   = elab-count (k tt)
  elab-count (impure (inj₂ (box _ _) , k))     = elab-count (k tt)
  elab-count (impure (inj₂ (fragment _ _) , k)) = elab-count (k tt)
  elab-count (impure (inj₂ (classed _ _) , k)) = elab-count (k tt)
  elab-count (impure (inj₂ (placed _ _ _ _ _) , k)) = elab-count (k tt)
  elab-count (impure (inj₂ (stepped _ _) , k)) = elab-count (k tt)

  elab-no-label : ∀ n b l → labelFrom n (toProg (elab {C} b)) l ≡ nothing
  elab-no-label n (pure _)                      l = refl
  elab-no-label n (impure (inj₁ _ , k))         l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ pause , k))     l = elab-no-label (n + 1) (k tt) l
  elab-no-label n (impure (inj₂ (columns _) , k))   l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ (box _ _) , k))     l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ (fragment _ _) , k)) l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ (classed _ _) , k)) l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ (placed _ _ _ _ _) , k)) l = elab-no-label n (k tt) l
  elab-no-label n (impure (inj₂ (stepped _ _) , k)) l = elab-no-label n (k tt) l

------------------------------------------------------------------------
-- The table of a deck

private
  ≟-refl : ∀ l → ⌊ l Str.≟ l ⌋ ≡ true
  ≟-refl l with l Str.≟ l
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

module _ {C : Set} where

  private
    after-elab : ∀ n b (k : Body⁺ (Nav ⊎ C)) l →
      labelFrom n (toProg (elab b >>= λ _ → k)) l ≡ labelFrom (n + pauses b) (toProg k) l
    after-elab n b k l =
      trans (cong (λ p → labelFrom n p l) (toProg-bind (elab b) (λ _ → k)))
     (trans (labelFrom-bind n (toProg (elab b)) (λ _ → toProg k) l)
     (trans (cong (λ r → r <∣> labelFrom (n + nextCount (toProg (elab b))) (toProg k) l) (elab-no-label n b l))
            (cong (λ m → labelFrom (n + m) (toProg k) l) (elab-count b))))

  -- One slide, then `k`: its labels first, then `k` after the slide's pauses.
  slideK-from : ∀ n i o b (k : Body⁺ (Nav ⊎ C)) l →
    labelFrom n (toProg (slideK i (o , b) k)) l
    ≡ (lookupE l (slideEs i n o) <∣> labelFrom (n + pauses b) (toProg k) l)
  slideK-from n i nothing b k l with ⌊ autoLabel i Str.≟ l ⌋
  ... | true  = refl
  ... | false = after-elab n b k l
  slideK-from n i (just u) b k l with ⌊ autoLabel i Str.≟ l ⌋
  ... | true  = refl
  ... | false with ⌊ u Str.≟ l ⌋
  ...   | true  = refl
  ...   | false = after-elab n b k l

  rest-from : ∀ n i ss l →
    labelFrom n (toProg (rest {C} i ss)) l ≡ lookupE l (entries i (n + 1) ss)
  rest-from n i []             l = refl
  rest-from n i ((o , b) ∷ ss) l =
    trans (slideK-from (n + 1) i o b (rest (suc i) ss) l)
    (trans (cong (lookupE l (slideEs i (n + 1) o) <∣>_) (rest-from (n + 1 + pauses b) (suc i) ss l))
           (sym (lookupE-++ l (slideEs i (n + 1) o) _)))

  deckBody-from : ∀ ss l →
    labelTable (toProg (deckBody {C} ss)) l ≡ lookupE l (entries 0 0 ss)
  deckBody-from []             l = refl
  deckBody-from ((o , b) ∷ ss) l =
    trans (slideK-from 0 0 o b (rest 1 ss) l)
    (trans (cong (lookupE l (slideEs 0 0 o) <∣>_) (rest-from (pauses b) 1 ss l))
           (sym (lookupE-++ l (slideEs 0 0 o) _)))

  -- `labelTable` of a deck is the slide-start table.
  slide-table : ∀ (d : Deck) l → labelTable (deckProg {C} d) l ≡ lookupE l (entries 0 0 (slides d))
  slide-table d = deckBody-from (slides d)

------------------------------------------------------------------------
-- The label of slide `i` resolves to its start

opaque
  unfolding autoLabel
  autoLabel-inj : ∀ {i j} → autoLabel i ≡ autoLabel j → i ≡ j
  autoLabel-inj e = suc-injective (charsInBase-injective 10 _ _ (Str.primStringFromListInjective _ _ e))

-- No user label is the label of a slide.
Fresh : List Slide → Set
Fresh = All λ s → ∀ {u} → proj₁ s ≡ just u → ∀ k → u ≢ autoLabel k

private
  ≟-miss : ∀ a b → a ≢ b → ⌊ a Str.≟ b ⌋ ≡ false
  ≟-miss a b ne with a Str.≟ b
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

  slideEs-miss : ∀ i st o l → autoLabel i ≢ l → (∀ {u} → o ≡ just u → u ≢ l) →
    lookupE l (slideEs i st o) ≡ nothing
  slideEs-miss i st nothing l na nu rewrite ≟-miss _ _ na = refl
  slideEs-miss i st (just u) l na nu rewrite ≟-miss _ _ na | ≟-miss u l (nu refl) = refl

-- the label of slide `j + i` resolves to the start of slide `i` among slides numbered from `j`
lookup-auto : ∀ j st ss i → Fresh ss → i < length ss →
  lookupE (autoLabel (j + i)) (entries j st ss) ≡ just (startOf st ss i)
lookup-auto j st [] i fr ()
lookup-auto j st ((nothing , b) ∷ ss) zero fr lt rewrite +-identityʳ j | ≟-refl (autoLabel j) = refl
lookup-auto j st ((just _ , b) ∷ ss) zero fr lt rewrite +-identityʳ j | ≟-refl (autoLabel j) = refl
lookup-auto j st ((o , b) ∷ ss) (suc i) (f ∷ fr) (s<s lt)
  rewrite +-suc j i | lookupE-++ (autoLabel (suc (j + i))) (slideEs j st o) (entries (suc j) (st + pauses b + 1) ss)
        | slideEs-miss j st o (autoLabel (suc (j + i)))
            (λ e → m≢1+m+n j {i} (autoLabel-inj e))
            (λ {u} eo e → f eo (suc (j + i)) e)
  = lookup-auto (suc j) (st + pauses b + 1) ss i fr lt

-- `labelTable (deckProg d)` resolves the label of slide `i` to its start.
auto-start : ∀ {C : Set} (d : Deck) i → Fresh (slides d) → i < length (slides d) →
  labelTable (deckProg {C} d) (autoLabel i) ≡ just (startOf 0 (slides d) i)
auto-start d i fr lt = trans (slide-table d (autoLabel i)) (lookup-auto 0 0 (slides d) i fr lt)
