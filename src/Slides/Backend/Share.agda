{-# OPTIONS --safe --without-K #-}

-- Sharing repeated subtrees: the finite DAG of a tree.
--
-- A tree is a node (printed text around its children) over a list of trees.  The shared form is
-- a table of entries, each a node whose children are references (positions, counted from the
-- oldest) to earlier entries, so equal subtrees are one entry (hash-consing).
--
--   shareTop : List Tree → Tab → List Entry × Tab   roots over a table
--   unshare  : Dag → List Tree                      the fold reading the table back
--
-- `readBack (shareTop ts emptyTab) ≡ ts` (`Slides.Backend.Share.Properties`): sharing loses nothing.
-- The page reads back lazily, resolving a reference when it is reached.

module Slides.Backend.Share where

open import Data.List.Base using (List; []; _∷_; _++_; map; length; reverse; concat; filterᵇ)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤ᵇ_; _≡ᵇ_)
open import Data.Bool.Base using (if_then_else_)
import Data.String.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Show using (show)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Listₚ
import Data.Product.Properties as Prodₚ
import Data.String.Properties as Strₚ
import Data.List.Relation.Binary.Lex.Strict as Lex
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)

-- a node: the text around its children (`k + 1` pieces for `k` children), and the children
data Tree : Set where
  node : List String → List Tree → Tree

-- an entry: a node over references
Entry : Set
Entry = List String × List ℕ

Dag : Set
Dag = List Entry


_≟ᵉ_ = Prodₚ.≡-dec (Listₚ.≡-dec _≟ˢ_) (Listₚ.≡-dec ℕₚ._≟_)

-- An index from entries to positions finds a candidate in logarithmic time.  It is only a hint:
-- the table is checked at the position, so the proofs never rely on the index.
entryOrder : StrictTotalOrder _ _ _
entryOrder = ×-strictTotalOrder (Lex.<-strictTotalOrder Strₚ.<-strictTotalOrder-≈) (Lex.<-strictTotalOrder ℕₚ.<-strictTotalOrder)

open import Data.Tree.AVL.Map entryOrder as Index using (Map)

Tab : Set
Tab = Dag × Map ℕ

emptyTab : Tab
emptyTab = [] , Index.empty

-- the entry at position `i` of a table of length `n` is `e`: its position
find : Entry → ℕ → Dag → ℕ → Maybe ℕ
find e i []       n       = nothing
find e i (x ∷ xs) zero    = nothing
find e i (x ∷ xs) (suc n) with n ℕₚ.≟ i
... | no  _    = find e i xs n
... | yes _ with x ≟ᵉ e
...   | yes _ = just n
...   | no  _ = nothing

-- the position of an entry in the table, if it is there
known : Entry → Tab → Maybe ℕ
known e (d , x) with Index.lookup x e
... | nothing = nothing
... | just i  = find e i d (length d)

-- the position of an entry, adding it if it is new
intern : Entry → Tab → ℕ × Tab
intern e t@(d , x) with known e t
... | just i  = i , t
... | nothing = length d , e ∷ d , Index.insert e (length d) x

mutual
  share₁ : Tree → Tab → ℕ × Tab
  share₁ (node h ts) d with share ts d
  ... | rs , d₁ = intern (h , rs) d₁

  share : List Tree → Tab → List ℕ × Tab
  share []       d = [] , d
  share (t ∷ ts) d with share₁ t d
  ... | r , d₁ with share ts d₁
  ...   | rs , d₂ = r ∷ rs , d₂

-- roots are not entered in the table: their children are, the roots stay entries
shareTop : List Tree → Tab → List Entry × Tab
shareTop []              d = [] , d
shareTop (node h ts ∷ r) d with share ts d
... | rs , d₁ with shareTop r d₁
...   | es , d₂ = (h , rs) ∷ es , d₂

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
