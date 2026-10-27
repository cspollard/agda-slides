{-# OPTIONS --safe --without-K #-}

-- What reveal.js supports and how it reads physical input (docs/NavInventory.md, 1.3, 6;
-- docs/Input.md, "Backend bindings").  Reveal binds its keys itself (`js/controllers/keyboard.js`);
-- this is the description of what it does, not configuration.
--
--   RCmd        reveal's own command vocabulary: all of `Nav`, `Ext`, the grid moves, and the
--               goto of a vertical slide.  `revealSupports` embeds `Nav ⊎ Ext` into it; the
--               moves and `slideV` have no `Nav ⊎ Ext` meaning (`dec` is `nothing`).
--   revealKeys  the key kinds, by deck `Mode`: a linear deck moves with the arrows and h j k l
--               (`next`/`prev`); a stacked deck moves on the grid (`right left down up`).
--               Space, n, PageDown are `next` and Shift+Space, p, PageUp `prev` in both.
--               Ctrl and meta are ignored; Shift counts only for Space, n, p and the arrows.
--   revealHash  `#n`, `#/h`, `#/h/v` (zero-based, 2-D) read on load and on `hashchange`.
--   revealRender  the canonical physical input of each command (none where there is none yet).
--
-- Laws and the facts the browser tests found: `Slides.Backend.Reveal.Supports.Properties`.

module Slides.Backend.Reveal.Supports where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)
open import Data.Unit.Base using (tt)   -- the instance of ⊤ that discharges the `bindKeys` check
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Backend.Input

data Move : Set where
  right left down up : Move

private
  mv : Move → ℕ
  mv right = 0
  mv left = 1
  mv down = 2
  mv up = 3
  vm : ℕ → Move
  vm 0 = right
  vm 1 = left
  vm 2 = down
  vm _ = up
  vm-mv : ∀ m → vm (mv m) ≡ m
  vm-mv right = refl
  vm-mv left = refl
  vm-mv down = refl
  vm-mv up = refl

_≟Mv_ : DecidableEquality Move
_≟Mv_ = decVia mv vm vm-mv

-- `slideV h v`: the vertical slide `v` (≥ 1) of the stack at `h` (`#/h/v`).
RCmd : Set
RCmd = Nav ⊎ (Ext ⊎ (Move ⊎ (ℕ × ℕ)))

pattern nav n = inj₁ n
pattern ext e = inj₂ (inj₁ e)
pattern move m = inj₂ (inj₂ (inj₁ m))
pattern slideV h v = inj₂ (inj₂ (inj₂ (h , v)))

_≟R_ : DecidableEquality RCmd
_≟R_ = ⊎-dec _≟N_ (⊎-dec _≟E_ (⊎-dec _≟Mv_ (≡-dec _≟ℕ_ _≟ℕ_)))

------------------------------------------------------------------------
-- Keys

⟨_⟩ ⇧_ : KeyName → Key
⟨ n ⟩ = n , bare
⇧ n = n , shift

-- the same in both modes
commonKinds : List (Decoder Key RCmd)
commonKinds =
      on _≟Key_ (⟨ space ⟩ ∷ ⟨ pageDown ⟩ ∷ ⟨ keyN ⟩ ∷ ⇧ keyN ∷ []) (nav next)
    ∷ on _≟Key_ (⇧ space ∷ ⟨ pageUp ⟩ ∷ ⟨ keyP ⟩ ∷ ⇧ keyP ∷ []) (nav prev)
    ∷ on _≟Key_ (⟨ home ⟩ ∷ ⇧ arrowLeft ∷ []) (nav first)
    ∷ on _≟Key_ (⟨ end ⟩ ∷ ⇧ arrowRight ∷ []) (nav last)
    ∷ on _≟Key_ (⟨ keyO ⟩ ∷ ⟨ escape ⟩ ∷ []) (ext overview)
    ∷ []

linearKinds stackedKinds : List (Decoder Key RCmd)
linearKinds =
    on _≟Key_ (⟨ arrowRight ⟩ ∷ ⟨ keyL ⟩ ∷ ⟨ arrowDown ⟩ ∷ ⟨ keyJ ⟩ ∷ []) (nav next)
  ∷ on _≟Key_ (⟨ arrowLeft ⟩ ∷ ⟨ keyH ⟩ ∷ ⟨ arrowUp ⟩ ∷ ⟨ keyK ⟩ ∷ []) (nav prev)
  ∷ commonKinds
stackedKinds =
    on _≟Key_ (⟨ arrowRight ⟩ ∷ ⟨ keyL ⟩ ∷ []) (move right)
  ∷ on _≟Key_ (⟨ arrowLeft ⟩ ∷ ⟨ keyH ⟩ ∷ []) (move left)
  ∷ on _≟Key_ (⟨ arrowDown ⟩ ∷ ⟨ keyJ ⟩ ∷ []) (move down)
  ∷ on _≟Key_ (⟨ arrowUp ⟩ ∷ ⟨ keyK ⟩ ∷ []) (move up)
  ∷ commonKinds

-- Checked at compile time: the kinds of each mode are pairwise disjoint.
revealKeys : Mode → Decoder Key RCmd
revealKeys linear  = bindKeys linearKinds
revealKeys stacked = bindKeys stackedKinds

------------------------------------------------------------------------
-- Hashes and events

revealHash : Decoder Hash RCmd
revealHash (flat n)         = just (nav (goto n))
revealHash (grid h zero)    = just (nav (goto h))
revealHash (grid h (suc v)) = just (slideV h (suc v))

revealRead : Mode → Decoder Event RCmd
revealRead m (keydown k)    = revealKeys m k
revealRead m (hashLoad h)   = revealHash h
revealRead m (hashChange h) = revealHash h

revealRender : Mode → RCmd → Maybe Event
revealRender _       (nav next)         = just (keydown ⟨ space ⟩)
revealRender _       (nav prev)         = just (keydown (⇧ space))
revealRender _       (nav first)        = just (keydown ⟨ home ⟩)
revealRender _       (nav last)         = just (keydown ⟨ end ⟩)
revealRender _       (nav (goto n))     = just (hashLoad (grid n 0))
revealRender _       (nav (gotoLabel _)) = nothing
revealRender _       (ext overview)     = just (keydown ⟨ keyO ⟩)
revealRender _       (ext tick)         = nothing
revealRender linear  (move _)           = nothing
revealRender stacked (move right)       = just (keydown ⟨ arrowRight ⟩)
revealRender stacked (move left)        = just (keydown ⟨ arrowLeft ⟩)
revealRender stacked (move down)        = just (keydown ⟨ arrowDown ⟩)
revealRender stacked (move up)          = just (keydown ⟨ arrowUp ⟩)
revealRender _       (slideV h zero)    = nothing
revealRender _       (slideV h (suc v)) = just (hashLoad (grid h (suc v)))

------------------------------------------------------------------------
-- Supports

module _ (V : Set) where
  open import Slides.Input.Supports V

  revealSupports : Supports Ext
  revealSupports = record
    { S = RCmd ; _≟S_ = _≟R_
    ; inj = λ { (inj₁ n) → just (nav n) ; (inj₂ e) → just (ext e) }
    ; dec = λ { (nav n) → just (inj₁ n) ; (ext e) → just (inj₂ e)
              ; (move _) → nothing ; (slideV _ _) → nothing }
    ; dec-inj = λ { {inj₁ _} refl → refl ; {inj₂ _} refl → refl }
    ; inj-dec = λ { {s = nav _} refl → refl ; {s = ext _} refl → refl
                  ; {s = move _} () ; {s = slideV _ _} () }
    }
