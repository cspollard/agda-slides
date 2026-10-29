{-# OPTIONS --safe --without-K #-}

-- Text: the one tree of styled runs behind slide prose and diagram labels.
--
-- An `Inline` is a run of characters (`text`, `codeSpan`), a node that wraps a list of
-- sub-runs (`emph`, `strong`, `sub`, `sup`, `link`), or an atom (`inlineMath`, `cite`).  Every
-- consumer is a fold over it: HTML (`Slides.Backend.Render`), plain text (`runsT`/`plainT` below, a
-- monoid homomorphism to lists of strings: `runsT (xs ++ ys) ≡ runsT xs ++ runsT ys`), SVG `<tspan>`s
-- (`Slides.Diagram.Print`) and width (`Slides.Diagram.TextMetrics`).  A construct a backend
-- cannot show degrades through `plainT`.
--
-- Labels are written as strings with light markup: `_x` or `_{xyz}` is a subscript, `^x` or
-- `^{xyz}` a superscript, a backslash quotes the next character.  `parse` reads it once, where
-- a label is built; a newline in a label is a line break (`br`). `parse "x_i^2"` is `text "x" ∷ sub (text "i" ∷ []) ∷ sup (text "2" ∷ []) ∷ []`.

module Slides.Text where

open import Data.Bool using (if_then_else_; _∨_)
open import Data.Maybe using (Maybe; just; nothing; maybe; _<∣>_)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
import Data.List.Properties as ListP
open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_; _++_; reverse; [_]; concatMap)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.String using (String; fromList; toList; concat) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Math using (Math; toLaTeX)

-- optional colour (a CSS colour), weight (a CSS font-weight) and size (percent); styles compose by
-- overriding, the inner one winning, as in a CSS cascade: `s <> t` is "inside `s`, then `t`"
record TextStyle : Set where
  constructor style
  field colour weight : Maybe String
        size : Maybe ℕ

noStyle : TextStyle
noStyle = style nothing nothing nothing

_<>_ : TextStyle → TextStyle → TextStyle
style c w z <> style c′ w′ z′ = style (c′ <∣> c) (w′ <∣> w) (z′ <∣> z)

-- a monoid (so nested `styled` runs collapse to one, `styled-compose`)
private
  style≡ : ∀ {c c′ w w′ z z′} → c ≡ c′ → w ≡ w′ → z ≡ z′ → style c w z ≡ style c′ w′ z′
  style≡ refl refl refl = refl

  or-idʳ : ∀ {A : Set} (x : Maybe A) → x <∣> nothing ≡ x
  or-idʳ (just _) = refl
  or-idʳ nothing  = refl

  or-assoc : ∀ {A : Set} (x y z : Maybe A) → (x <∣> y) <∣> z ≡ x <∣> (y <∣> z)
  or-assoc (just _) _ _ = refl
  or-assoc nothing  _ _ = refl

<>-idˡ : ∀ s → noStyle <> s ≡ s
<>-idˡ (style c w z) = style≡ (or-idʳ c) (or-idʳ w) (or-idʳ z)

<>-idʳ : ∀ s → s <> noStyle ≡ s
<>-idʳ s = refl

<>-assoc : ∀ s t u → (s <> t) <> u ≡ s <> (t <> u)
<>-assoc (style c w z) (style c′ w′ z′) (style c″ w″ z″) =
  style≡ (sym (or-assoc c″ c′ c)) (sym (or-assoc w″ w′ w)) (sym (or-assoc z″ z′ z))

data Inline : Set where
  text codeSpan : String → Inline
  emph strong sub sup : List Inline → Inline
  styled     : TextStyle → List Inline → Inline
  br         : Inline                            -- a line break
  inlineMath : Math → Inline
  link       : (url : String) → List Inline → Inline
  cite       : (key : String) → Inline          -- a bibliography key (checked by `Slides.Deck.DSL`)

Text : Set
Text = List Inline

-- the strings of a text, in order: a monoid homomorphism to lists (`runs-++`); plain text is
-- their concatenation (strings have no stdlib monoid laws, lists do)
mutual
  runsI : Inline → List String
  runsI (text s)       = [ s ]
  runsI (codeSpan s)   = [ s ]
  runsI (emph is)      = runsT is
  runsI (strong is)    = runsT is
  runsI (sub is)       = runsT is
  runsI (sup is)       = runsT is
  runsI (styled _ is)  = runsT is
  runsI br             = [ "\n" ]
  runsI (inlineMath m) = [ toLaTeX m ]
  runsI (link _ is)    = runsT is
  runsI (cite k)       = [ "[" ++ˢ k ++ˢ "]" ]

  runsT : Text → List String
  runsT []       = []
  runsT (i ∷ is) = runsI i ++ runsT is

plainI : Inline → String
plainI i = concat (runsI i)

plainT : Text → String
plainT is = concat (runsT is)

private
  mutual
    runs : List Char → List Char → Text
    runs acc []               = flush acc []
    runs acc ('\\' ∷ c ∷ cs) = runs (c ∷ acc) cs
    runs acc ('\n' ∷ cs)      = flush acc (br ∷ runs [] cs)
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
runs-++ : ∀ xs ys → runsT (xs ++ ys) ≡ runsT xs ++ runsT ys
runs-++ []       ys = refl
runs-++ (i ∷ xs) ys = trans (cong (runsI i ++_) (runs-++ xs ys)) (sym (ListP.++-assoc (runsI i) _ _))

-- nested styles collapse: the inner one overrides the outer, as `<>` says, and the text is the same
styled-compose : ∀ s t is → runsI (styled s [ styled t is ]) ≡ runsI (styled (s <> t) is)
styled-compose s t is = ListP.++-identityʳ (runsT is)

-- the lines of a text, split at its breaks (at least one)
lines : Text → List Text
lines []        = [] ∷ []
lines (br ∷ is) = [] ∷ lines is
lines (i ∷ is)  = cons i (lines is)
  where cons : Inline → List Text → List Text
        cons j []       = [ j ] ∷ []
        cons j (l ∷ ls) = (j ∷ l) ∷ ls

-- the HTML/SVG `style` text of a style: only the fields that are set
css : TextStyle → String
css (style c w z) = prop "color" c ++ˢ prop "font-weight" w ++ˢ prop "font-size" (Maybe.map (λ n → show n ++ˢ "%") z)
  where prop : String → Maybe String → String
        prop k = maybe (λ v → k ++ˢ ":" ++ˢ v ++ˢ ";") ""

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
