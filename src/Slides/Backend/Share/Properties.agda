{-# OPTIONS --safe --without-K #-}

-- Sharing loses nothing: `readBack (shareTop ts emptyTab) ≡ ts`, that is
-- `sharing : List Tree ↪ _` (a right inverse).  `unshare` folds the table into
-- trees, each entry unfolded over the entries below it; the table only grows at its new end,
-- and every entry refers only to entries below it.

module Slides.Backend.Share.Properties where

open import Data.List.Base using (List; []; _∷_; _++_; map; length; reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary.Decidable using (yes; no)
open import Function.Bundles using (_↪_; mk↪)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Listₚ
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there)
import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties as Sfx
import Data.List.Relation.Binary.Pointwise as Pointwise

open import Slides.Backend.Share
import Data.Tree.AVL.Map entryOrder as Index

-- Reading back: `unshare` is a fold of the table

nth : List Tree → ℕ → Tree
nth []       _       = node [] []
nth (t ∷ _)  zero    = t
nth (_ ∷ ts) (suc i) = nth ts i

-- the tree at a position of a table of trees (newest first), counted from the oldest
at : List Tree → ℕ → Tree
at u i = nth (reverse u) i

-- the trees of the entries of a table, newest first
unshare : Dag → List Tree
unshare []             = []
unshare ((h , rs) ∷ d) = node h (map (at (unshare d)) rs) ∷ unshare d

-- an entry over the trees of a table
readEntry : Dag → Entry → Tree
readEntry d (h , rs) = node h (map (at (unshare d)) rs)

-- The statement: the roots read back over the table are the trees shared.
readBack : List Entry × Tab → List Tree
readBack (es , d , _) = map (readEntry d) es

-- Sharing loses nothing: `readBack (shareTop ts emptyTab) ≡ ts`

-- the table only grows at the new end
_⊑_ : Dag → Dag → Set
_⊑_ = Suffix _≡_

⊑-refl : ∀ {d} → d ⊑ d
⊑-refl = here (Pointwise.refl refl)

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans = Sfx.trans trans

⊑-length : ∀ {d d′} → d ⊑ d′ → length d ≤ length d′
⊑-length = Sfx.length-mono

length-unshare : ∀ d → length (unshare d) ≡ length d
length-unshare []            = refl
length-unshare (_ ∷ d)       = cong suc (length-unshare d)

-- positions already used keep their trees when the table grows
nth-snoc : ∀ ys x i → i < length ys → nth (ys ++ x ∷ []) i ≡ nth ys i
nth-snoc (y ∷ ys) x zero    _       = refl
nth-snoc (y ∷ ys) x (suc i) (s≤s p) = nth-snoc ys x i p

nth-top : ∀ ys x → nth (ys ++ x ∷ []) (length ys) ≡ x
nth-top []       x = refl
nth-top (y ∷ ys) x = nth-top ys x

at-cons : ∀ u x i → i < length u → at (x ∷ u) i ≡ at u i
at-cons u x i p rewrite Listₚ.unfold-reverse x u = nth-snoc (reverse u) x i (subst (i <_) (sym (Listₚ.length-reverse u)) p)

at-top : ∀ u x {n} → n ≡ length u → at (x ∷ u) n ≡ x
at-top u x refl rewrite Listₚ.unfold-reverse x u = subst (λ n → nth (reverse u ++ x ∷ []) n ≡ x) (Listₚ.length-reverse u) (nth-top (reverse u) x)

stable : ∀ {d d′ i} → d ⊑ d′ → i < length d → at (unshare d′) i ≡ at (unshare d) i
stable (here rs) p rewrite Pointwise.Pointwise-≡⇒≡ rs = refl
stable {d} {e ∷ d′} {i} (there q) p =
  trans (at-cons (unshare d′) _ i (subst (i <_) (sym (length-unshare d′)) (ℕₚ.<-≤-trans p (⊑-length q)))) (stable q p)

map-stable : ∀ {d d′ rs} → d ⊑ d′ → All (_< length d) rs → map (at (unshare d′)) rs ≡ map (at (unshare d)) rs
map-stable q []         = refl
map-stable q (p ∷ ps) = cong₂ _∷_ (stable q p) (map-stable q ps)

-- every entry refers only to the entries below it
WF : Dag → Set
WF []             = ⊤
WF ((h , rs) ∷ d) = All (_< length d) rs × WF d

⊑-WF : ∀ {d d′} → d ⊑ d′ → WF d′ → WF d
⊑-WF (here rs) w       rewrite Pointwise.Pointwise-≡⇒≡ rs = w
⊑-WF (there q) (_ , w) = ⊑-WF q w

-- a found entry sits at the position `length t` above a table `t`
find-sound : ∀ e i d {n j} → n ≡ length d → find e i d n ≡ just j → ∃ λ t → (e ∷ t) ⊑ d × j ≡ length t
find-sound e i []       refl ()
find-sound e i (x ∷ xs) {suc n} refl eq with n ℕₚ.≟ i
... | no _ = let t , q , r = find-sound e i xs refl eq in t , there q , r
... | yes _ with x ≟ᵉ e
...   | yes refl = xs , ⊑-refl , sym (just-injective eq)

known-sound : ∀ e t {j} → known e t ≡ just j → ∃ λ u → (e ∷ u) ⊑ proj₁ t × j ≡ length u
known-sound e (d , x) eq with Index.lookup x e
... | just i = find-sound e i d refl eq

-- what `share₁` and `share` establish, of the table (the index is any)
Ok₁ : Dag → Tree → ℕ × Tab → Set
Ok₁ d t (r , d′ , _) = WF d′ × d ⊑ d′ × r < length d′ × at (unshare d′) r ≡ t

Ok : Dag → List Tree → List ℕ × Tab → Set
Ok d ts (rs , d′ , _) = WF d′ × d ⊑ d′ × All (_< length d′) rs × map (at (unshare d′)) rs ≡ ts

intern-ok : ∀ h rs ts d x → WF d → All (_< length d) rs → map (at (unshare d)) rs ≡ ts
          → Ok₁ d (node h ts) (intern (h , rs) (d , x))
intern-ok h rs ts d x w ps eq with known (h , rs) (d , x) in f
... | nothing = (ps , w) , there ⊑-refl , ℕₚ.n<1+n _ , trans (at-top (unshare d) _ (sym (length-unshare d))) (cong (node h) eq)
... | just i with known-sound (h , rs) (d , x) f
...   | t , q , refl with ⊑-WF q w
...     | ps′ , _ = w , ⊑-refl , ℕₚ.<-≤-trans (ℕₚ.n<1+n _) (⊑-length q)
                  , trans (stable q (ℕₚ.n<1+n _)) (trans (at-top (unshare t) _ (sym (length-unshare t)))
                          (cong (node h) (trans (sym (map-stable (⊑-trans (there ⊑-refl) q) ps′)) eq)))

mutual
  share₁-ok : ∀ t d x → WF d → Ok₁ d t (share₁ t (d , x))
  share₁-ok (node h ts) d x w with share ts (d , x) | share-ok ts d x w
  ... | rs , d₁ , x₁ | w₁ , q , ps , eq with intern-ok h rs ts d₁ x₁ w₁ ps eq
  ...   | w₂ , q₂ , r , e = w₂ , ⊑-trans q q₂ , r , e

  share-ok : ∀ ts d x → WF d → Ok d ts (share ts (d , x))
  share-ok []       d x w = w , ⊑-refl , [] , refl
  share-ok (t ∷ ts) d x w with share₁ t (d , x) | share₁-ok t d x w
  ... | r , d₁ , x₁ | w₁ , q₁ , p₁ , e₁ with share ts (d₁ , x₁) | share-ok ts d₁ x₁ w₁
  ...   | rs , d₂ , x₂ | w₂ , q₂ , ps , eq =
    w₂ , ⊑-trans q₁ q₂ , ℕₚ.<-≤-trans p₁ (⊑-length q₂) ∷ ps
       , cong₂ _∷_ (trans (stable q₂ p₁) e₁) eq

-- the roots of `shareTop` read back, over its table, are the trees shared
shareTop-ok : ∀ ts d x → WF d → WF (proj₁ (proj₂ (shareTop ts (d , x)))) × d ⊑ proj₁ (proj₂ (shareTop ts (d , x)))
                              × readBack (shareTop ts (d , x)) ≡ ts
shareTop-ok []              d x w = w , ⊑-refl , refl
shareTop-ok (node h ts ∷ r) d x w with share ts (d , x) | share-ok ts d x w
... | rs , d₁ , x₁ | w₁ , q₁ , ps , eq with shareTop r (d₁ , x₁) | shareTop-ok r d₁ x₁ w₁
...   | es , d₂ , x₂ | w₂ , q₂ , eq₂ =
  w₂ , ⊑-trans q₁ q₂ , cong₂ _∷_ (cong (node h) (trans (map-stable q₂ ps) eq)) eq₂

-- Sharing is a section of reading back: the trees are a retract of the shared form
sharing : List Tree ↪ (List Entry × Tab)
sharing = mk↪ {to = λ ts → shareTop ts emptyTab} {from = readBack} λ { refl → proj₂ (proj₂ (shareTop-ok _ [] _ tt)) }
