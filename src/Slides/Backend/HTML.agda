{-# OPTIONS --safe --without-K #-}

-- HTML5 smart constructors over parsnip's XML.
--
-- parsnip prints XML: an element without content self-closes (`<div />`),
-- which HTML5 only honours for void elements.  The R0 spike showed that a
-- browser nests everything after an empty `<div />` inside it.  These
-- constructors therefore give every empty non-void element a single space
-- of content, and leave void elements (`meta`, `link`, `img`, …) empty.

module Slides.Backend.HTML where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; null)
open import Data.Bool.ListAction using (any)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; _==_)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element; textElement)

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

-- The doctype is not part of the XML AST; it is a constant prefix added when
-- a page is written out.
doctype : String
doctype = "<!DOCTYPE html>\n"
