{-# OPTIONS --safe --without-K #-}

-- Physical inputs of the browser backends and how a backend reads them (docs/Input.md,
-- "Backend bindings").
--
--   Key, Hash, Event   what the page sees: a key (name and modifier), a URL hash (`#n` flat,
--                      `#/h/v` two-dimensional) read on load or on `hashchange`;
--   Ext                the commands a deck may await beyond `Nav` (`overview`, `tick`);
--   Mode               whether a deck is one-dimensional (reveal moves linearly) or stacked;
--   on ks s            a decoder: the keys `ks` mean the command `s` (one *kind* of binding);
--   choice ds          the kinds combined by `Slides.Input.Binding._⊕_`;
--   bindWith ...       `choice`, accepted only when the kinds are pairwise `Disjoint`: decided by
--                      computation over the finite list of all keys, so two kinds on one key
--                      are "No instance of type" (tests/negative).
--
-- Laws: `Slides.Backend.Input.Properties`.  The backends' tables are
-- `Slides.Backend.Reveal.Supports` and `Slides.Backend.Plain.Supports`.

module Slides.Backend.Input where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_; cartesianProduct; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-cartesianProduct⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; allPairs?)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Relation.Nullary.Decidable using (Dec; yes; no; map′; True; ⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

open import Slides.Input.Binding

-- Decidable equality of an enumeration through a retraction into ℕ.
decVia : ∀ {A : Set} (f : A → ℕ) (g : ℕ → A) → (∀ a → g (f a) ≡ a) → DecidableEquality A
decVia f g gf a b = map′ (λ e → trans (sym (gf a)) (trans (cong g e) (gf b))) (cong f) (f a ≟ f b)

------------------------------------------------------------------------
-- Keys

data KeyName : Set where
  arrowRight arrowLeft arrowDown arrowUp space pageDown pageUp home end keyN keyP keyH keyJ keyK keyL keyO escape otherKey : KeyName

data Mods : Set where
  bare shift ctrl : Mods   -- ctrl: any of ctrl and meta (alt is not modelled)

Key : Set
Key = KeyName × Mods

private
  idx : KeyName → ℕ
  idx arrowRight = 0
  idx arrowLeft = 1
  idx arrowDown = 2
  idx arrowUp = 3
  idx space = 4
  idx pageDown = 5
  idx pageUp = 6
  idx home = 7
  idx end = 8
  idx keyN = 9
  idx keyP = 10
  idx keyH = 11
  idx keyJ = 12
  idx keyK = 13
  idx keyL = 14
  idx keyO = 15
  idx escape = 16
  idx otherKey = 17

  un : ℕ → KeyName
  un 0 = arrowRight
  un 1 = arrowLeft
  un 2 = arrowDown
  un 3 = arrowUp
  un 4 = space
  un 5 = pageDown
  un 6 = pageUp
  un 7 = home
  un 8 = end
  un 9 = keyN
  un 10 = keyP
  un 11 = keyH
  un 12 = keyJ
  un 13 = keyK
  un 14 = keyL
  un 15 = keyO
  un 16 = escape
  un _ = otherKey

  un-idx : ∀ a → un (idx a) ≡ a
  un-idx arrowRight = refl
  un-idx arrowLeft = refl
  un-idx arrowDown = refl
  un-idx arrowUp = refl
  un-idx space = refl
  un-idx pageDown = refl
  un-idx pageUp = refl
  un-idx home = refl
  un-idx end = refl
  un-idx keyN = refl
  un-idx keyP = refl
  un-idx keyH = refl
  un-idx keyJ = refl
  un-idx keyK = refl
  un-idx keyL = refl
  un-idx keyO = refl
  un-idx escape = refl
  un-idx otherKey = refl

_≟K_ : DecidableEquality KeyName
_≟K_ = decVia idx un un-idx

names : List KeyName
names = arrowRight ∷ arrowLeft ∷ arrowDown ∷ arrowUp ∷ space ∷ pageDown ∷ pageUp ∷ home ∷ end ∷ keyN ∷ keyP ∷ keyH ∷ keyJ ∷ keyK ∷ keyL ∷ keyO ∷ escape ∷ otherKey ∷ []

names-cover : ∀ a → a ∈ names
names-cover arrowRight = here refl
names-cover arrowLeft = there (here refl)
names-cover arrowDown = there (there (here refl))
names-cover arrowUp = there (there (there (here refl)))
names-cover space = there (there (there (there (here refl))))
names-cover pageDown = there (there (there (there (there (here refl)))))
names-cover pageUp = there (there (there (there (there (there (here refl))))))
names-cover home = there (there (there (there (there (there (there (here refl)))))))
names-cover end = there (there (there (there (there (there (there (there (here refl))))))))
names-cover keyN = there (there (there (there (there (there (there (there (there (here refl)))))))))
names-cover keyP = there (there (there (there (there (there (there (there (there (there (here refl))))))))))
names-cover keyH = there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))
names-cover keyJ = there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))
names-cover keyK = there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))
names-cover keyL = there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))
names-cover keyO = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))
names-cover escape = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))
names-cover otherKey = there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))

private
  mi : Mods → ℕ
  mi bare = 0
  mi shift = 1
  mi ctrl = 2
  um : ℕ → Mods
  um 0 = bare
  um 1 = shift
  um _ = ctrl
  um-mi : ∀ m → um (mi m) ≡ m
  um-mi bare = refl
  um-mi shift = refl
  um-mi ctrl = refl

_≟M_ : DecidableEquality Mods
_≟M_ = decVia mi um um-mi

mods : List Mods
mods = bare ∷ shift ∷ ctrl ∷ []

mods-cover : ∀ m → m ∈ mods
mods-cover bare = here refl
mods-cover shift = there (here refl)
mods-cover ctrl = there (there (here refl))

_≟Key_ : DecidableEquality Key
_≟Key_ = ≡-dec _≟K_ _≟M_

-- every key
keys : List Key
keys = cartesianProduct names mods

keys-cover : ∀ k → k ∈ keys
keys-cover (n , m) = ∈-cartesianProduct⁺ (names-cover n) (mods-cover m)

------------------------------------------------------------------------
-- Hashes and events

-- `#n` is `flat n`; `#/h/v` is `grid h v` (`#/h` is `grid h 0`).
data Hash : Set where
  flat : ℕ → Hash
  grid : ℕ → ℕ → Hash

data Event : Set where
  keydown    : Key → Event
  hashLoad   : Hash → Event
  hashChange : Hash → Event

-- Commands beyond `Nav` that a deck may await: toggle the overview, the page clock.
data Ext : Set where
  overview tick : Ext

private
  ei : Ext → ℕ
  ei overview = 0
  ei tick = 1
  ie : ℕ → Ext
  ie 0 = overview
  ie _ = tick
  ie-ei : ∀ e → ie (ei e) ≡ e
  ie-ei overview = refl
  ie-ei tick = refl

_≟E_ : DecidableEquality Ext
_≟E_ = decVia ei ie ie-ei

-- A deck without a vertical stack is navigated linearly by reveal; otherwise reveal moves
-- on a grid.
data Mode : Set where
  linear stacked : Mode

------------------------------------------------------------------------
-- Decoders and their kinds

module _ {I S : Set} (_≟I_ : DecidableEquality I) where
  open import Data.List.Membership.DecPropositional _≟I_ using (_∈?_)

  on : List I → S → Decoder I S
  on ks s i = if ⌊ i ∈? ks ⌋ then just s else nothing

choice : ∀ {I S} → List (Decoder I S) → Decoder I S
choice = foldr _⊕_ (λ _ → nothing)

disjoint*? : ∀ {I S} (xs : List I) → (∀ i → i ∈ xs) → (ds : List (Decoder I S)) →
             Dec (AllPairs Disjoint ds)
disjoint*? xs cov = allPairs? (λ r r′ → disjoint? r r′ xs cov)

-- The checked constructors: the instance argument is `⊤` exactly when the kinds are
-- pairwise disjoint on all keys (so the error for a clash is "No instance of type").
bindKeys : ∀ {S} (ds : List (Decoder Key S)) → {{_ : True (disjoint*? keys keys-cover ds)}} →
           Decoder Key S
bindKeys ds = choice ds

bindNames : ∀ {S} (ds : List (Decoder KeyName S)) → {{_ : True (disjoint*? names names-cover ds)}} →
            Decoder KeyName S
bindNames ds = choice ds
