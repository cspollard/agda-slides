{-# OPTIONS --safe --without-K #-}

-- What a backend binds: the physical inputs of the browser and the commands they send.
--
-- A key is its DOM key code (a number: decidable equality for free, no enumeration of names) and a
-- modifier; `#n`, `#/h/v` and `#/id` are the hashes a page reads on load or on `hashchange`.  A
-- backend binds a subset of the program commands (`Slides.Program.Supports`) and decodes
-- physical input into them:
--
--   Kind         keys that send one command; a binding is a list of kinds, read first match
--   clash-free   no key is in two kinds (decided by computation: the tables below are `refl`)
--   revealSupports   reveal.js binds all of `Nav` and, besides, the grid moves and the overview
--                (commands of its own, `Aux`, that no program awaits): `Supports Nav`
--   plainSupports    the standalone backend binds all of `Nav`: `idSupports`
--
-- Both are total (`AllSup` of every program: nothing is skipped), so `lower-supported`
-- of `Slides.Program.Supports` says a deck's program is presented unchanged by either backend
-- (`reveal-presents`, `plain-presents`).  The tables describe what reveal.js and
-- `assets/plain.js` do; the browser tests check them.

module Slides.Backend.Input where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Bool.ListAction using (any; all)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base using (_×_; _,_; Σ-syntax; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)
open import Data.Empty using (⊥)
open import Container.Lowering.Properties using (_≈⋆_)
open import Relation.Nullary.Decidable using (⌊_⌋; map′)
open import Relation.Nullary using (yes; no)
open import Data.Unit.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Container.FreeMonad using (pure; impure)

open import Slides.Deck.Talk using (Mode; linear; stacked)
open import Slides.Program.Navigation using (Nav; next; prev; first; last; goto; gotoLabel; _≟N_)
open import Slides.Program.Supports using (Supports; idSupports)
open import Slides.Program.Syntax using (Program)
import Slides.Program.Supports as Sup

------------------------------------------------------------------------
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

------------------------------------------------------------------------
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

------------------------------------------------------------------------
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

linear-clash-free : clash-free (revealKinds linear) ≡ true
linear-clash-free = refl

stacked-clash-free : clash-free (revealKinds stacked) ≡ true
stacked-clash-free = refl

-- `#n` and `#/h` are slide numbers (zero-based), `#/h/v` a vertical slide, `#/id` a label
revealHash : Hash → Maybe Nav
revealHash (flat n)         = just (goto n)
revealHash (grid h _)       = just (goto h)
revealHash (named l)        = just (gotoLabel l)

-- reveal binds all of `Nav`: the program commands are embedded, nothing is skipped
revealSupports : Supports Nav
revealSupports = record
  { S = RCmd ; _≟S_ = _≟R_
  ; inj = λ n → just (nav n)
  ; dec = λ { (nav n) → just n ; (aux _) → nothing }
  ; dec-inj = λ { refl → refl }
  ; inj-dec = λ { {s = nav _} refl → refl ; {s = aux _} () } }

------------------------------------------------------------------------
-- The standalone backend (`assets/plain.js`)

plainKinds : List (Kind Nav)
plainKinds =
    (⟨ arrowRight ⟩ ∷ ⟨ arrowDown ⟩ ∷ ⟨ space ⟩ ∷ ⟨ pageDown ⟩ ∷ [] , next)
  ∷ (⟨ arrowLeft ⟩ ∷ ⟨ arrowUp ⟩ ∷ ⟨ pageUp ⟩ ∷ [] , prev)
  ∷ (⟨ home ⟩ ∷ [] , first)
  ∷ (⟨ end ⟩ ∷ [] , last)
  ∷ []

plain-clash-free : clash-free plainKinds ≡ true
plain-clash-free = refl

-- `#n` is one-based and flat, read once on load (`#0` is the first slide)
plainHash : Hash → Maybe Nav
plainHash (flat zero)    = just (goto zero)
plainHash (flat (suc n)) = just (goto n)
plainHash _              = nothing

plainSupports : Supports Nav
plainSupports = idSupports _≟N_

------------------------------------------------------------------------
-- Every deck is presented unchanged

-- a backend that binds every command of `Nav` skips nothing
module _ {T D : Set} (b : Supports Nav) (tot : ∀ n → Σ[ s ∈ Supports.S b ] Supports.inj b n ≡ just s) where
  private
    no-nothing : ∀ {A : Set} {x : Maybe A} {s} → x ≡ just s → x ≡ nothing → ⊥
    no-nothing refl ()

  allSup : ∀ {A} (p : Program T D Nav A) → Sup.AllSup b p
  allSup (pure _)              = tt
  allSup (impure (inj₁ _ , k)) = λ q → allSup (k q)
  allSup (impure (inj₂ c , k)) = no-nothing (proj₂ (tot c)) , allSup (k tt)

  -- presenting a program on `b` leaves it unchanged
  presents : ∀ {A} (p : Program T D Nav A) → Sup.skipU b p ≈⋆ p
  presents p = Sup.lower-supported b p (allSup p)

reveal-total : ∀ n → Σ[ s ∈ RCmd ] Supports.inj revealSupports n ≡ just s
reveal-total n = nav n , refl

plain-total : ∀ n → Σ[ s ∈ Nav ] Supports.inj plainSupports n ≡ just s
plain-total n = n , refl
