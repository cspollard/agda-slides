{-# OPTIONS --safe --without-K #-}

-- Navigation: moving through a presentation as machine state.
--
-- The commands a navigating backend sends are `next`, `prev`, `first`, `last`, `goto n` (by
-- tick) and `gotoLabel l` (by name).  The machine `navM len labels view` keeps a position
-- `n ∈ [0, len]` as its state and shows `view n`.  Because the view is a function of the
-- position (a deck is read at a tick, `Slides.Deck.Read`), going back needs no replay of the
-- program: `prev` is the predecessor.  The label table is a partial map from names to
-- positions, built from a deck's events (`Slides.Deck.Read`).
--
-- Laws (the legacy `Slides.Input.Navigation.Properties`, restated for ticks):
--
--   nav-bounded      the position never leaves [0, len]
--   prev-next        prev undoes next (below the end)
--   view-next        next shows the view of the next tick (below the end)
--   gotoLabel-goto   resolving a label then moving is `goto` its position
--   next-steps       k nexts from position n is position n + k (below the end): history by counting
--
-- `Nav` has decidable equality, so programs can wait for `next`.

module Slides.Program.Navigation where

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _⊓_; z≤n; s≤s)
open import Data.Nat.Properties as ℕP using (m≤n⇒m⊓n≡m; m⊓n≤n; _≟_)
open import Data.String.Base using (String)
import Data.String.Properties as Str
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)

open import Slides.Program.Machine

data Nav : Set where
  next prev first last : Nav
  goto      : ℕ → Nav
  gotoLabel : String → Nav

private
  enc : Nav → ℕ ⊎ (ℕ ⊎ String)
  enc next          = inj₁ 0
  enc prev          = inj₁ 1
  enc first         = inj₁ 2
  enc last          = inj₁ 3
  enc (goto n)      = inj₂ (inj₁ n)
  enc (gotoLabel s) = inj₂ (inj₂ s)

  unenc : ℕ ⊎ (ℕ ⊎ String) → Nav
  unenc (inj₁ 0)        = next
  unenc (inj₁ 1)        = prev
  unenc (inj₁ 2)        = first
  unenc (inj₁ _)        = last
  unenc (inj₂ (inj₁ n)) = goto n
  unenc (inj₂ (inj₂ s)) = gotoLabel s

  unenc-enc : ∀ n → unenc (enc n) ≡ n
  unenc-enc next          = refl
  unenc-enc prev          = refl
  unenc-enc first         = refl
  unenc-enc last          = refl
  unenc-enc (goto _)      = refl
  unenc-enc (gotoLabel _) = refl

-- decidable equality as a retract of `ℕ ⊎ ℕ ⊎ String`: one clause per constructor
_≟N_ : DecidableEquality Nav
a ≟N b = map′ (λ e → trans (sym (unenc-enc a)) (trans (cong unenc e) (unenc-enc b))) (cong enc)
              (⊎-dec _≟_ (⊎-dec _≟_ Str._≟_) (enc a) (enc b))

module _ {V : Set} (len : ℕ) (labels : String → Maybe ℕ) (view : ℕ → V) where

  navStep : ℕ → Nav → ℕ
  navStep n next          = suc n ⊓ len
  navStep zero    prev    = zero
  navStep (suc n) prev    = n
  navStep n first         = zero
  navStep n last          = len
  navStep n (goto k)      = k ⊓ len
  navStep n (gotoLabel l) = maybe′ (_⊓ len) n (labels l)

  navM : Machine Nav V
  navM = record { State = ℕ ; init = zero ; step = navStep ; out = view }

  nav-bounded : ∀ {n} → n ≤ len → ∀ c → navStep n c ≤ len
  nav-bounded le next          = ℕP.m⊓n≤n _ len
  nav-bounded {zero}  le prev  = z≤n
  nav-bounded {suc n} le prev  = ℕP.≤-trans (ℕP.n≤1+n n) le
  nav-bounded le first         = z≤n
  nav-bounded le last          = ℕP.≤-refl
  nav-bounded le (goto k)      = ℕP.m⊓n≤n k len
  nav-bounded {n} le (gotoLabel l) with labels l
  ... | nothing = le
  ... | just k  = ℕP.m⊓n≤n k len

  prev-next : ∀ n → suc n ≤ len → navStep (navStep n next) prev ≡ n
  prev-next n le rewrite m≤n⇒m⊓n≡m le = refl

  view-next : ∀ n → suc n ≤ len → out navM (navStep n next) ≡ view (suc n)
  view-next n le = cong view (m≤n⇒m⊓n≡m le)

  gotoLabel-goto : ∀ n l i → labels l ≡ just i → navStep n (gotoLabel l) ≡ navStep n (goto i)
  gotoLabel-goto n l i e rewrite e = refl

  -- k nexts from position n, below the end: position n + k (history by counting)
  next-steps : ∀ k n → n + k ≤ len → runs navM n (replicate k next) ≡ n + k
  next-steps zero    n le = sym (ℕP.+-identityʳ n)
  next-steps (suc k) n le with ℕP.≤-trans (s≤s (ℕP.m≤m+n n k)) (subst (_≤ len) (ℕP.+-suc n k) le)
  ... | le₁ rewrite m≤n⇒m⊓n≡m le₁ =
    trans (next-steps k (suc n) (subst (_≤ len) (ℕP.+-suc n k) le))
          (sym (ℕP.+-suc n k))
