{-# OPTIONS --safe --without-K #-}

-- What the standalone backend supports and how `assets/plain.js` reads physical input
-- (docs/NavInventory.md, 1.3).  The key table is part of the asset (its golden is byte-exact);
-- this module is its checked description.
--
--   PCmd        `Nav` and `tick` (the page clock, `clock` here); no overview.
--   plainKeys   keyed by the key *name*: plain.js looks at `e.key` only, so modifiers do not
--               matter (Shift+Space is `next`).  ArrowRight, ArrowDown, Space, PageDown
--               are `next`; ArrowLeft, ArrowUp, PageUp `prev`; Home `first`; End `last`.
--   plainHash   `#n`, one-based and flat, read once on load; a stack is flattened, so there is
--               no 2-D hash (`#/h/v` is not read).  There is no `hashchange` handler.
--
-- Laws and the facts the browser tests found: `Slides.Backend.Plain.Supports.Properties`.

module Slides.Backend.Plain.Supports where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary using (yes)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder; on)
open import Slides.Backend.Input

PCmd : Set
PCmd = Nav ⊎ ⊤

pattern nav n = inj₁ n
pattern clock = inj₂ tt

_≟P_ : DecidableEquality PCmd
_≟P_ = ⊎-dec _≟N_ (λ _ _ → yes refl)

plainKinds : List (Decoder KeyName PCmd)
plainKinds =
    on _≟K_ (arrowRight ∷ arrowDown ∷ space ∷ pageDown ∷ []) (nav next)
  ∷ on _≟K_ (arrowLeft ∷ arrowUp ∷ pageUp ∷ []) (nav prev)
  ∷ on _≟K_ (home ∷ []) (nav first)
  ∷ on _≟K_ (end ∷ []) (nav last)
  ∷ []

-- Checked at compile time: the kinds are pairwise disjoint.
plainKeys : Decoder KeyName PCmd
plainKeys = bindNames plainKinds

plainKey : Decoder Key PCmd
plainKey (n , _) = plainKeys n

-- `#0` is clamped to the first slide.
plainHash : Decoder Hash PCmd
plainHash (flat zero)    = just (nav (goto zero))
plainHash (flat (suc n)) = just (nav (goto n))
plainHash (grid _ _)     = nothing

plainRead : Decoder Event PCmd
plainRead (keydown k)    = plainKey k
plainRead (hashLoad h)   = plainHash h
plainRead (hashChange _) = nothing

plainRender : PCmd → Maybe Event
plainRender (nav next)          = just (keydown (space , bare))
plainRender (nav prev)          = just (keydown (pageUp , bare))
plainRender (nav first)         = just (keydown (home , bare))
plainRender (nav last)          = just (keydown (end , bare))
plainRender (nav (goto n))      = just (hashLoad (flat (suc n)))
plainRender (nav (gotoLabel _)) = nothing
plainRender clock                = nothing

module _ (V : Set) where
  open import Slides.Input.Supports V

  plainSupports : Supports Ext
  plainSupports = record
    { S = PCmd ; _≟S_ = _≟P_
    ; inj = λ { (inj₁ n) → just (nav n) ; (inj₂ overview) → nothing ; (inj₂ tick) → just clock }
    ; dec = λ { (nav n) → just (inj₁ n) ; clock → just (inj₂ tick) }
    ; dec-inj = λ { {inj₁ _} refl → refl ; {inj₂ overview} () ; {inj₂ tick} refl → refl }
    ; inj-dec = λ { {s = nav _} refl → refl ; {s = clock} refl → refl }
    }

  -- Plain can present every deck (an `await overview` is skipped: it has no overview).
  plainSupports-total : NavTotal plainSupports
  plainSupports-total n = nav n , refl
