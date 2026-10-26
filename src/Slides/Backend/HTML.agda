{-# OPTIONS --safe --without-K #-}

-- HTML5 smart constructors over parsnip's XML.
--
-- parsnip prints XML: an element without content self-closes (`<div />`),
-- which HTML5 only honours for void elements.  The R0 spike showed that a
-- browser nests everything after an empty `<div />` inside it.  These
-- constructors therefore give every empty non-void element a single space
-- of content, and leave void elements (`meta`, `link`, `img`, …) empty.

module Slides.Backend.HTML where

open import Data.Bool using (Bool; true; if_then_else_)
open import Data.List using (List; []; _∷_; null)
open import Data.Bool.ListAction using (any)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; _==_)

open import Data.List using (map)
open import Data.Vec as Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.XML.AST using (XMLM; node; fromContent)
open import Data.XML.Valid using (Text; isValidTexts)
open import Data.XML.Sanitize
  using ( element; textElement; fixName; fixAttrs; fixText; fixName-valid
        ; fixAttrs-valid; fixText-valid; fromEq; both )

private variable
  A : Set

Attrs : Set
Attrs = List (String × String)

-- Elements that must not have content in HTML5.
voidElements : List String
voidElements =
    "area" ∷ "base" ∷ "br" ∷ "col" ∷ "embed" ∷ "hr" ∷ "img" ∷ "input"
  ∷ "link" ∷ "meta" ∷ "source" ∷ "track" ∷ "wbr" ∷ []

isVoid : String → Bool
isVoid tag = any (tag ==_) voidElements

-- Non-empty text: the empty string becomes one space.
padText : String → String
padText s = if null (toList s) then " " else s

-- An element containing only text.
hText : String → Attrs → String → XMLM A
hText tag attrs t = textElement tag attrs (padText t)

-- An element containing only elements.
hElement : String → Attrs → List (XMLM A) → XMLM A
hElement tag attrs []       = if isVoid tag then element tag attrs [] else textElement tag attrs " "
hElement tag attrs (c ∷ cs) = element tag attrs (c ∷ cs)

-- An element with mixed content: text, then each child followed by text.
-- Like the other constructors, runtime strings are repaired by parsnip's
-- `Sanitize` functions and the repairs are proved valid.
private
  mapTexts-valid : ∀ {n} (v : Vec Text n) → isValidTexts (Vec.map fixText v) ≡ true
  mapTexts-valid Vec.[]       = refl
  mapTexts-valid (t Vec.∷ ts) = both (fixText-valid t) (mapTexts-valid ts)

hMixed : String → Attrs → String × List (XMLM A × String) → XMLM A
hMixed tag attrs (t , []) = hText tag attrs t
hMixed tag attrs (t , cs@(_ ∷ _)) with fromContent (toList t , map (λ { (x , s) → x , toList s }) cs)
... | n , texts , f =
  node (fixName (toList tag)) (fixAttrs (map (λ { (k , v) → toList k , toList v }) attrs))
       (Vec.map fixText texts) f
       {fromEq (fixName-valid (toList tag))}
       {fromEq (fixAttrs-valid (map (λ { (k , v) → toList k , toList v }) attrs))}
       {fromEq (mapTexts-valid texts)}

-- The doctype is not part of the XML AST; it is a constant prefix added when
-- a page is written out.
doctype : String
doctype = "<!DOCTYPE html>\n"
