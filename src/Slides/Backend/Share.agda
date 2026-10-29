{-# OPTIONS --safe --without-K #-}

-- Sharing repeated subtrees: the finite DAG of a tree.
--
-- A tree is a node (its text, already printed, around its children) over a list of trees.  The shared form is a
-- table of entries, each a node whose children are *references* to earlier entries: a DAG, in which
-- equal subtrees are one entry (hash-consing; the key is the entry itself).  The table is a list,
-- newest entry first; a reference is the position of its entry counted from the oldest.
--
--   shareTop : List Tree → Dag → List Entry × Dag   roots (kept as entries) over a table
--   unshare  : Dag → List Tree                       the table read back: a fold, each entry
--                                                    unfolded over the trees of the entries below it
--
-- `unshare-share : readBack (shareTop ts []) ≡ ts`: sharing loses nothing.  (The page does the
-- same read-back lazily: a reference is looked up when it is reached.)

module Slides.Backend.Share where

open import Data.List.Base using (List; []; _∷_; _++_; map; length; reverse; concat; filterᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _≤ᵇ_; _≡ᵇ_)
open import Data.Bool.Base using (if_then_else_)
import Data.String.Base
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Show using (show)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Maybe.Properties using (just-injective)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Listₚ
import Data.Product.Properties as Prodₚ

-- a node: the text around its children (`k + 1` pieces for `k` children), and the children
data Tree : Set where
  node : List String → List Tree → Tree

-- an entry: a node over references
Entry : Set
Entry = List String × List ℕ

Dag : Set
Dag = List Entry


private
  _≟ᵉ_ = Prodₚ.≡-dec (Listₚ.≡-dec _≟ˢ_) (Listₚ.≡-dec ℕₚ._≟_)

-- the position (from the oldest) of an entry, given the length of the table
find : Entry → Dag → ℕ → Maybe ℕ
find e []       n       = nothing
find e (x ∷ xs) zero    = nothing
find e (x ∷ xs) (suc n) with x ≟ᵉ e
... | yes _ = just n
... | no  _ = find e xs n

-- the position of an entry, adding it if it is new
intern : Entry → Dag → ℕ × Dag
intern e d with find e d (length d)
... | just i  = i , d
... | nothing = length d , e ∷ d

mutual
  share₁ : Tree → Dag → ℕ × Dag
  share₁ (node h ts) d with share ts d
  ... | rs , d₁ = intern (h , rs) d₁

  share : List Tree → Dag → List ℕ × Dag
  share []       d = [] , d
  share (t ∷ ts) d with share₁ t d
  ... | r , d₁ with share ts d₁
  ...   | rs , d₂ = r ∷ rs , d₂

-- roots are not entered in the table: their children are, the roots stay entries
shareTop : List Tree → Dag → List Entry × Dag
shareTop []              d = [] , d
shareTop (node h ts ∷ r) d with share ts d
... | rs , d₁ with shareTop r d₁
...   | es , d₂ = (h , rs) ∷ es , d₂

------------------------------------------------------------------------
-- Writing trees and printing entries

-- a tree from text and subtrees, in order
tree : List (String ⊎ Tree) → Tree
tree = go ""
  where
    go : String → List (String ⊎ Tree) → Tree
    go acc []            = node (acc ∷ []) []
    go acc (inj₁ s ∷ r)  = go (acc ++ˢ s) r
    go acc (inj₂ t ∷ r)  with go "" r
    ... | node ps ks     = node (acc ∷ ps) (t ∷ ks)

-- an entry as text, each reference written by `ref`
render : (ℕ → String) → Entry → String
render ref (p ∷ ps , r ∷ rs) = p ++ˢ ref r ++ˢ render ref (ps , rs)
render ref (ps , _)          = Data.String.Base.concat ps

-- The text to ship for roots over a table: the table and the roots.  A reference is the string of
-- the entry's position (`"7"`), except that an entry referred to once is written where it is
-- used, so only the shared entries are in the table (and renumbered).
ship : List Entry → Dag → List String × List String
ship roots d = go 0 0 [] [] (reverse d)
  where
    refs : List ℕ
    refs = concat (map proj₂ (roots ++ d))
    uses : ℕ → ℕ
    uses i = length (filterᵇ (_≡ᵇ i) refs)
    nth′ : List String → ℕ → String
    nth′ []       _       = ""
    nth′ (x ∷ _)  zero    = x
    nth′ (_ ∷ xs) (suc i) = nth′ xs i
    go : ℕ → ℕ → List String → List String → List Entry → List String × List String
    go pos kept env tbl []       = reverse tbl , map (render (nth′ env)) roots
    go pos kept env tbl (e ∷ es) with render (nth′ env) e
    ... | t = if uses pos ≤ᵇ 1 then go (suc pos) kept (env ++ t ∷ []) tbl es
              else go (suc pos) (suc kept) (env ++ ("\"" ++ˢ show kept ++ˢ "\"") ∷ []) (t ∷ tbl) es

------------------------------------------------------------------------
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
readBack : List Entry × Dag → List Tree
readBack (es , d) = map (readEntry d) es

------------------------------------------------------------------------
-- Sharing loses nothing: `readBack (shareTop ts []) ≡ ts`

-- the table only grows at the new end
data _⊑_ : Dag → Dag → Set where
  ⊑-refl : ∀ {d} → d ⊑ d
  ⊑-cons : ∀ {d d′ e} → d ⊑ d′ → d ⊑ (e ∷ d′)

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p ⊑-refl     = p
⊑-trans p (⊑-cons q) = ⊑-cons (⊑-trans p q)

⊑-length : ∀ {d d′} → d ⊑ d′ → length d ≤ length d′
⊑-length ⊑-refl     = ℕₚ.≤-refl
⊑-length (⊑-cons p) = ℕₚ.m≤n⇒m≤1+n (⊑-length p)

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
stable ⊑-refl     p = refl
stable {d} {e ∷ d′} {i} (⊑-cons q) p =
  trans (at-cons (unshare d′) _ i (subst (i <_) (sym (length-unshare d′)) (ℕₚ.<-≤-trans p (⊑-length q)))) (stable q p)

map-stable : ∀ {d d′ rs} → d ⊑ d′ → All (_< length d) rs → map (at (unshare d′)) rs ≡ map (at (unshare d)) rs
map-stable q []         = refl
map-stable q (p ∷ ps) = cong₂ _∷_ (stable q p) (map-stable q ps)

-- every entry refers only to the entries below it
WF : Dag → Set
WF []             = ⊤
WF ((h , rs) ∷ d) = All (_< length d) rs × WF d

⊑-WF : ∀ {d d′} → d ⊑ d′ → WF d′ → WF d
⊑-WF ⊑-refl     w       = w
⊑-WF (⊑-cons q) (_ , w) = ⊑-WF q w

-- a found entry sits at the position `length t` above a table `t`
find-sound : ∀ e d {n i} → n ≡ length d → find e d n ≡ just i → ∃ λ t → (e ∷ t) ⊑ d × i ≡ length t
find-sound e []       refl ()
find-sound e (x ∷ xs) {suc n} refl eq with x ≟ᵉ e
... | yes refl = xs , ⊑-refl , sym (just-injective eq)
... | no _ with find-sound e xs refl eq
...   | t , q , r = t , ⊑-cons q , r

-- what `share₁` and `share` establish
Ok₁ : Dag → Tree → ℕ × Dag → Set
Ok₁ d t (r , d′) = WF d′ × d ⊑ d′ × r < length d′ × at (unshare d′) r ≡ t

Ok : Dag → List Tree → List ℕ × Dag → Set
Ok d ts (rs , d′) = WF d′ × d ⊑ d′ × All (_< length d′) rs × map (at (unshare d′)) rs ≡ ts

intern-ok : ∀ h rs ts d → WF d → All (_< length d) rs → map (at (unshare d)) rs ≡ ts
          → Ok₁ d (node h ts) (intern (h , rs) d)
intern-ok h rs ts d w ps eq with find (h , rs) d (length d) in f
... | nothing = (ps , w) , ⊑-cons ⊑-refl , ℕₚ.n<1+n _ , trans (at-top (unshare d) _ (sym (length-unshare d))) (cong (node h) eq)
... | just i with find-sound (h , rs) d refl f
...   | t , q , refl with ⊑-WF q w
...     | ps′ , _ = w , ⊑-refl , ℕₚ.<-≤-trans (ℕₚ.n<1+n _) (⊑-length q)
                  , trans (stable q (ℕₚ.n<1+n _)) (trans (at-top (unshare t) _ (sym (length-unshare t)))
                          (cong (node h) (trans (sym (map-stable (⊑-trans (⊑-cons ⊑-refl) q) ps′)) eq)))

mutual
  share₁-ok : ∀ t d → WF d → Ok₁ d t (share₁ t d)
  share₁-ok (node h ts) d w with share ts d | share-ok ts d w
  ... | rs , d₁ | w₁ , q , ps , eq with intern-ok h rs ts d₁ w₁ ps eq
  ...   | w₂ , q₂ , r , e = w₂ , ⊑-trans q q₂ , r , e

  share-ok : ∀ ts d → WF d → Ok d ts (share ts d)
  share-ok []       d w = w , ⊑-refl , [] , refl
  share-ok (t ∷ ts) d w with share₁ t d | share₁-ok t d w
  ... | r , d₁ | w₁ , q₁ , p₁ , e₁ with share ts d₁ | share-ok ts d₁ w₁
  ...   | rs , d₂ | w₂ , q₂ , ps , eq =
    w₂ , ⊑-trans q₁ q₂ , ℕₚ.<-≤-trans p₁ (⊑-length q₂) ∷ ps
       , cong₂ _∷_ (trans (stable q₂ p₁) e₁) eq

-- the roots of `shareTop` read back, over its table, are the trees shared
shareTop-ok : ∀ ts d → WF d → WF (proj₂ (shareTop ts d)) × d ⊑ proj₂ (shareTop ts d)
                              × readBack (shareTop ts d) ≡ ts
shareTop-ok []              d w = w , ⊑-refl , refl
shareTop-ok (node h ts ∷ r) d w with share ts d | share-ok ts d w
... | rs , d₁ | w₁ , q₁ , ps , eq with shareTop r d₁ | shareTop-ok r d₁ w₁
...   | es , d₂ | w₂ , q₂ , eq₂ =
  w₂ , ⊑-trans q₁ q₂ , cong₂ _∷_ (cong (node h) (trans (map-stable q₂ ps) eq)) eq₂

unshare-share : ∀ ts → readBack (shareTop ts []) ≡ ts
unshare-share ts = proj₂ (proj₂ (shareTop-ok ts [] tt))
