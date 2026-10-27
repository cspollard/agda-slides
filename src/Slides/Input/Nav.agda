{-# OPTIONS --safe --without-K #-}

-- The navigation vocabulary every deck requires (docs/Input.md).
--
-- `next` and `pause` are the commands a program *awaits*; the others are sent by a
-- navigating backend and interpreted by `Slides.Input.Navigation.navM`.  `goto` is by
-- index, `gotoLabel` by the name given by `label` in the program.

module Slides.Input.Nav where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.String.Base using (String)
open import Relation.Nullary.Decidable using (map′; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Data.String.Properties as Str

data Nav : Set where
  next prev first last : Nav
  goto      : ℕ → Nav
  gotoLabel : String → Nav

_≟N_ : DecidableEquality Nav
next ≟N next = yes refl
prev ≟N prev = yes refl
first ≟N first = yes refl
last ≟N last = yes refl
goto m ≟N goto n = map′ (cong goto) (λ { refl → refl }) (m ≟ n)
gotoLabel a ≟N gotoLabel b = map′ (cong gotoLabel) (λ { refl → refl }) (a Str.≟ b)
next ≟N prev = no λ ()
next ≟N first = no λ ()
next ≟N last = no λ ()
next ≟N goto _ = no λ ()
next ≟N gotoLabel _ = no λ ()
prev ≟N next = no λ ()
prev ≟N first = no λ ()
prev ≟N last = no λ ()
prev ≟N goto _ = no λ ()
prev ≟N gotoLabel _ = no λ ()
first ≟N next = no λ ()
first ≟N prev = no λ ()
first ≟N last = no λ ()
first ≟N goto _ = no λ ()
first ≟N gotoLabel _ = no λ ()
last ≟N next = no λ ()
last ≟N prev = no λ ()
last ≟N first = no λ ()
last ≟N goto _ = no λ ()
last ≟N gotoLabel _ = no λ ()
goto _ ≟N next = no λ ()
goto _ ≟N prev = no λ ()
goto _ ≟N first = no λ ()
goto _ ≟N last = no λ ()
goto _ ≟N gotoLabel _ = no λ ()
gotoLabel _ ≟N next = no λ ()
gotoLabel _ ≟N prev = no λ ()
gotoLabel _ ≟N first = no λ ()
gotoLabel _ ≟N last = no λ ()
gotoLabel _ ≟N goto _ = no λ ()
