{-# OPTIONS --safe --without-K #-}

-- What a backend binds: physical browser input and the program commands it sends.
--
-- A key is a DOM key code and a modifier; `#n`, `#/h/v`, `#/id` are the hashes a page reads.
-- A binding is a list of `Kind`s (keys sending one command), read first match; `clash-free`
-- decides that no key is in two kinds (the tables below are checked by `refl`).
--   `revealSupports`  all of `Nav` plus reveal's own commands (`Aux`, grid moves, overview)
--   `plainSupports`   all of `Nav`
-- Both are total, so a deck's program is presented unchanged (`reveal-total`, `plain-total`,
-- `Slides.Backend.Input.Properties`).  The tables describe reveal.js and `assets/plain.js`;
-- the browser tests check them.

module Slides.Backend.Input where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Bool.ListAction using (any; all)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base using (_×_; _,_; Σ-syntax; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)
open import Data.Empty using (⊥)
open import Relation.Nullary.Decidable using (⌊_⌋; map′)
open import Relation.Nullary using (yes; no)
open import Data.Unit.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Container.FreeMonad using (pure; impure)

open import Slides.Deck.Talk using (Mode; linear; stacked)
open import Slides.Program.Navigation using (Nav; next; prev; first; last; goto; gotoLabel; _≟N_)

-- Keys and hashes

KeyCode : Set
KeyCode = ℕ

arrowLeft arrowUp arrowRight arrowDown space pageUp pageDown end home escape keyH keyJ keyK keyL keyN keyO keyP keyQ : KeyCode
arrowLeft = 37; arrowUp = 38; arrowRight = 39; arrowDown = 40
space = 32; pageUp = 33; pageDown = 34; end = 35; home = 36; escape = 27
keyH = 72; keyJ = 74; keyK = 75; keyL = 76; keyN = 78; keyO = 79; keyP = 80; keyQ = 81

data Mods : Set where
  bare shift ctrl : Mods   -- ctrl: any of ctrl and meta (alt is not modelled)

_≟M_ : DecidableEquality Mods
bare  ≟M bare  = yes refl
bare  ≟M shift = no (λ ())
bare  ≟M ctrl  = no (λ ())
shift ≟M bare  = no (λ ())
shift ≟M shift = yes refl
shift ≟M ctrl  = no (λ ())
ctrl  ≟M bare  = no (λ ())
ctrl  ≟M shift = no (λ ())
ctrl  ≟M ctrl  = yes refl

Key : Set
Key = KeyCode × Mods

_≟Key_ : DecidableEquality Key
_≟Key_ = ≡-dec _≟_ _≟M_

⟨_⟩ ⇧_ : KeyCode → Key
⟨ n ⟩ = n , bare
⇧ n = n , shift

-- `#n` is `flat n`; `#/h/v` is `grid h v` (`#/h` is `grid h 0`); `#/id` is `named id`
data Hash : Set where
  flat  : ℕ → Hash
  grid  : ℕ → ℕ → Hash
  named : String → Hash

-- the URL fragment of a hash (how the page names it): `#n`, `#/h/v`, `#/id`
showHash : Hash → String
showHash (flat n)   = "#" ++ˢ showℕ n
showHash (grid h v) = "#/" ++ˢ showℕ h ++ˢ "/" ++ˢ showℕ v
showHash (named l)  = "#/" ++ˢ l

-- Bindings

-- the keys of a kind send its command
Kind : Set → Set
Kind S = List Key × S

private
  memberᵇ : Key → List Key → Bool
  memberᵇ k ks = any (λ k′ → ⌊ k ≟Key k′ ⌋) ks

  keysOf : ∀ {S} → List (Kind S) → List Key
  keysOf []             = []
  keysOf ((ks , _) ∷ r) = ks ++ keysOf r

decode : ∀ {S} → List (Kind S) → Key → Maybe S
decode []             k = nothing
decode ((ks , c) ∷ r) k with memberᵇ k ks
... | true  = just c
... | false = decode r k

-- no key is in two kinds, so the order of the kinds does not matter
clash-free : ∀ {S} → List (Kind S) → Bool
clash-free []             = true
clash-free ((ks , _) ∷ r) = all (λ k → not (memberᵇ k (keysOf r))) ks ∧ clash-free r

-- reveal.js (`js/controllers/keyboard.js`: this describes what it does, not configuration)

data Aux : Set where
  right left down up overview : Aux

private
  ix : Aux → ℕ
  ix right = 0; ix left = 1; ix down = 2; ix up = 3; ix overview = 4
  un : ℕ → Aux
  un 0 = right; un 1 = left; un 2 = down; un 3 = up; un _ = overview
  un-ix : ∀ a → un (ix a) ≡ a
  un-ix right = refl; un-ix left = refl; un-ix down = refl; un-ix up = refl; un-ix overview = refl

_≟A_ : DecidableEquality Aux
a ≟A b = map′ (λ e → trans (sym (un-ix a)) (trans (cong un e) (un-ix b))) (cong ix) (ix a ≟ ix b)

-- reveal's command vocabulary: all of `Nav` and its own
RCmd : Set
RCmd = Nav ⊎ Aux

_≟R_ : DecidableEquality RCmd
_≟R_ = ⊎-dec _≟N_ _≟A_

pattern nav n = inj₁ n
pattern aux a = inj₂ a

-- Space, n, PageDown are `next` and Shift+Space, p, PageUp `prev` in both modes; a linear deck
-- moves with the arrows and h j k l, a stacked one on the grid
commonKinds : List (Kind RCmd)
commonKinds =
    (⟨ space ⟩ ∷ ⟨ pageDown ⟩ ∷ ⟨ keyN ⟩ ∷ ⇧ keyN ∷ [] , nav next)
  ∷ (⇧ space ∷ ⟨ pageUp ⟩ ∷ ⟨ keyP ⟩ ∷ ⇧ keyP ∷ [] , nav prev)
  ∷ (⟨ home ⟩ ∷ ⇧ arrowLeft ∷ [] , nav first)
  ∷ (⟨ end ⟩ ∷ ⇧ arrowRight ∷ [] , nav last)
  ∷ (⟨ keyO ⟩ ∷ ⟨ escape ⟩ ∷ [] , aux overview)
  ∷ []

revealKinds : Mode → List (Kind RCmd)
revealKinds linear =
    (⟨ arrowRight ⟩ ∷ ⟨ keyL ⟩ ∷ ⟨ arrowDown ⟩ ∷ ⟨ keyJ ⟩ ∷ [] , nav next)
  ∷ (⟨ arrowLeft ⟩ ∷ ⟨ keyH ⟩ ∷ ⟨ arrowUp ⟩ ∷ ⟨ keyK ⟩ ∷ [] , nav prev)
  ∷ commonKinds
revealKinds stacked =
    (⟨ arrowRight ⟩ ∷ ⟨ keyL ⟩ ∷ [] , aux right)
  ∷ (⟨ arrowLeft ⟩ ∷ ⟨ keyH ⟩ ∷ [] , aux left)
  ∷ (⟨ arrowDown ⟩ ∷ ⟨ keyJ ⟩ ∷ [] , aux down)
  ∷ (⟨ arrowUp ⟩ ∷ ⟨ keyK ⟩ ∷ [] , aux up)
  ∷ commonKinds

revealKeys : Mode → Key → Maybe RCmd
revealKeys m = decode (revealKinds m)

-- `#n` and `#/h` are slide numbers (zero-based), `#/h/v` a vertical slide, `#/id` a label
revealHash : Hash → Maybe Nav
revealHash (flat n)         = just (goto n)
revealHash (grid h _)       = just (goto h)
revealHash (named l)        = just (gotoLabel l)

-- The standalone backend (`assets/plain.js`)

plainKinds : List (Kind Nav)
plainKinds =
    (⟨ arrowRight ⟩ ∷ ⟨ arrowDown ⟩ ∷ ⟨ space ⟩ ∷ ⟨ pageDown ⟩ ∷ [] , next)
  ∷ (⟨ arrowLeft ⟩ ∷ ⟨ arrowUp ⟩ ∷ ⟨ pageUp ⟩ ∷ [] , prev)
  ∷ (⟨ home ⟩ ∷ [] , first)
  ∷ (⟨ end ⟩ ∷ [] , last)
  ∷ []

-- `#n` is one-based and flat, read once on load (`#0` is the first slide)
plainHash : Hash → Maybe Nav
plainHash (flat zero)    = just (goto zero)
plainHash (flat (suc n)) = just (goto n)
plainHash _              = nothing
