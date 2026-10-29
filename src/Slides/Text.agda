{-# OPTIONS --safe --without-K #-}

-- Text: the one tree of styled runs behind slide prose and diagram labels.
--
-- An `Inline` is a run of characters (`text`, `codeSpan`), a node that wraps a list of
-- sub-runs (`emph`, `strong`, `sub`, `sup`, `link`), or an atom (`inlineMath`, `cite`).  Every
-- consumer is a fold over it: HTML (`Slides.Backend.Render`), plain text (`plainT` below, a
-- monoid homomorphism to strings: `plainT (xs ++ ys) ≡ plainT xs ++ plainT ys`), SVG `<tspan>`s
-- (`Slides.Diagram.Print`) and width (`Slides.Diagram.TextMetrics`).  A construct a backend
-- cannot show degrades through `plainT`.
--
-- Labels are written as strings with light markup: `_x` or `_{xyz}` is a subscript, `^x` or
-- `^{xyz}` a superscript, a backslash quotes the next character.  `parse` reads it once, where
-- a label is built: `parse "x_i^2"` is `text "x" ∷ sub (text "i" ∷ []) ∷ sup (text "2" ∷ []) ∷ []`.

module Slides.Text where

open import Data.Bool using (if_then_else_; _∨_)
open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_; reverse; [_]; concatMap)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Math using (Math; toLaTeX)

data Inline : Set where
  text codeSpan : String → Inline
  emph strong sub sup : List Inline → Inline
  inlineMath : Math → Inline
  link       : (url : String) → List Inline → Inline
  cite       : (key : String) → Inline          -- a bibliography key (checked by `Slides.Deck.DSL`)

Text : Set
Text = List Inline

mutual
  plainI : Inline → String
  plainI (text s)       = s
  plainI (codeSpan s)   = s
  plainI (emph is)      = plainT is
  plainI (strong is)    = plainT is
  plainI (sub is)       = plainT is
  plainI (sup is)       = plainT is
  plainI (inlineMath m) = toLaTeX m
  plainI (link _ is)    = plainT is
  plainI (cite k)       = "[" ++ˢ k ++ˢ "]"

  plainT : Text → String
  plainT []       = ""
  plainT (i ∷ is) = plainI i ++ˢ plainT is

private
  mutual
    runs : List Char → List Char → Text
    runs acc []               = flush acc []
    runs acc ('\\' ∷ c ∷ cs) = runs (c ∷ acc) cs
    runs acc ('_' ∷ cs)       = flush acc (scripted sub cs)
    runs acc ('^' ∷ cs)       = flush acc (scripted sup cs)
    runs acc (c ∷ cs)         = runs (c ∷ acc) cs

    scripted : (Text → Inline) → List Char → Text
    scripted k []         = []
    scripted k ('{' ∷ cs) = braced k [] cs
    scripted k (c ∷ cs)   = k [ text (fromList [ c ]) ] ∷ runs [] cs

    braced : (Text → Inline) → List Char → List Char → Text
    braced k acc []         = k [ text (fromList (reverse acc)) ] ∷ []
    braced k acc ('}' ∷ cs) = k [ text (fromList (reverse acc)) ] ∷ runs [] cs
    braced k acc (c ∷ cs)   = braced k (c ∷ acc) cs

    flush : List Char → Text → Text
    flush []  rest = rest
    flush acc rest = text (fromList (reverse acc)) ∷ rest

parse : String → Text
parse t = runs [] (toList t)

-- a label back to its markup (the browser-side player parses it again); scripts hold one run
private
  esc : Char → List Char
  esc c = if ⌊ c ≟ '\\' ⌋ ∨ ⌊ c ≟ '_' ⌋ ∨ ⌊ c ≟ '^' ⌋ then '\\' ∷ c ∷ [] else [ c ]

  script : String → String → String
  script m u with toList u
  ... | c ∷ [] = if ⌊ c ≟ '{' ⌋ then m ++ˢ "{" ++ˢ u ++ˢ "}" else m ++ˢ u
  ... | _      = m ++ˢ "{" ++ˢ u ++ˢ "}"

markup : Text → String
markup []             = ""
markup (sub is ∷ js)  = script "_" (plainT is) ++ˢ markup js
markup (sup is ∷ js)  = script "^" (plainT is) ++ˢ markup js
markup (i ∷ js)       = fromList (concatMap esc (toList (plainI i))) ++ˢ markup js

-- the label markup reads as the old segments did, and plain text drops exactly the markup
_ : parse "x_i^2" ≡ text "x" ∷ sub [ text "i" ] ∷ sup [ text "2" ] ∷ []
_ = refl

_ : parse "a\\_b_{cd}" ≡ text "a_b" ∷ sub [ text "cd" ] ∷ []
_ = refl

_ : plainT (parse "x_{ab}^2 \\^") ≡ "xab2 ^"
_ = refl

_ : markup (parse "x_i^{23}a\\_") ≡ "x_i^{23}a\\_"
_ = refl
