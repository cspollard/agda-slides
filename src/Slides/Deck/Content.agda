{-# OPTIONS --safe --without-K #-}

-- Content: the leaves of a slide.
--
-- Flow content (text, lists, math, tables) is laid out by the browser, so it is a carrier of its
-- own, sharing the temporal structure of scenes but not the geometry of diagrams.  Minimal
-- vocabulary first: inline text with emphasis, code and math (TeX source), and five blocks.
-- A `Flow` is a list of blocks, the free monoid on them; overlaying two leaves of a scene is
-- concatenation (`++`, associative, which is all `Slides.Scene.Sample` asks of a leaf carrier).
--
-- Its semantics is a monoid homomorphism to lines of plain text (`plain`, `plain-++`): the
-- reading a plain-text backend gives.  Richer backends are other homomorphisms
-- (`Slides.Backend.*` later); they need nothing else from this module.

module Slides.Deck.Content where

open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
import Data.List.Properties as ListP
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String; intersperse; concat) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

data Inline : Set where
  text emph strong code math : String → Inline

Text : Set
Text = List Inline

data Block : Set where
  heading     : ℕ → Text → Block
  paragraph   : Text → Block
  bullets     : List Text → Block
  displayMath : String → Block
  table       : (header : List Text) (rows : List (List Text)) → Block

Flow : Set
Flow = List Block

------------------------------------------------------------------------
-- Plain text

plainI : Inline → String
plainI (text s)   = s
plainI (emph s)   = s
plainI (strong s) = s
plainI (code s)   = s
plainI (math s)   = s

plainT : Text → String
plainT t = concat (map plainI t)

plainB : Block → List String
plainB (heading _ t)   = plainT t ∷ []
plainB (paragraph t)   = plainT t ∷ []
plainB (bullets ts)    = map (λ t → "- " ++ˢ plainT t) ts
plainB (displayMath s) = s ∷ []
plainB (table h rows)  = row h ∷ map row rows
  where row = λ cs → intersperse " | " (map plainT cs)

plain : Flow → List String
plain = concatMap plainB

plain-++ : ∀ xs ys → plain (xs ++ ys) ≡ plain xs ++ plain ys
plain-++ = ListP.concatMap-++ plainB
