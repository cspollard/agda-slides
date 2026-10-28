{-# OPTIONS --safe --without-K #-}

-- Typed mathematics.
--
-- Formulas are a small AST rather than LaTeX strings, so structure is
-- checked when the deck is typechecked (a fraction has two arguments, a sum
-- has bounds) and the printer decides the braces: every argument of `frac`,
-- `^`, `_` and `\sqrt` is wrapped, so output cannot have unbalanced groups
-- or an ambiguous superscript.  `raw` is the escape hatch for anything the
-- AST lacks.  With `Slides.Deck.Literals` in scope, numbers and string literals are
-- overloaded: `2` is `num 2` and `"x"` is the identifier `x`.

module Slides.Deck.Math where

open import Data.List using (List; []; _∷_; map; concat)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; concat; fromList; toList) renaming (_++_ to _++ˢ_)
open import Data.Char using (Char)

data Greek : Set where
  alpha beta gamma delta epsilon theta lambda mu nu pi rho sigma tau phi chi psi omega : Greek
  Gamma Delta Theta Lambda Pi Sigma Phi Psi Omega : Greek

data Fn : Set where
  sin cos tan exp ln log : Fn

data Rel : Set where
  eq neq lt gt le ge approx to mid elem : Rel

data Math : Set where
  var       : String → Math              -- an identifier, printed as written
  num       : ℕ → Math
  greek     : Greek → Math
  add sub mul : Math → Math → Math       -- a + b, a - b, a \cdot b
  neg       : Math → Math
  frac      : (numerator denominator : Math) → Math
  pow       : (base exponent : Math) → Math
  idx       : (base subscript : Math) → Math
  sqrt      : Math → Math
  fn        : Fn → Math → Math           -- \sin\left(…\right)
  sum       : (lower upper body : Math) → Math
  integral  : (lower upper body : Math) → Math
  prod      : (lower upper body : Math) → Math
  paren     : Math → Math                -- \left( … \right)
  rel       : Rel → Math → Math → Math
  vec hat bar : Math → Math
  cal bb    : Math → Math                -- \mathcal, \mathbb
  call      : Math → List Math → Math    -- f\left(a, b\right)
  tuple     : List Math → Math           -- a, b, c (no brackets)
  juxt      : Math → Math → Math         -- a b, with a thin space
  dd        : Math → Math                -- \mathrm{d}x, with a thin space before
  text      : String → Math              -- upright text
  raw       : String → Math              -- LaTeX, verbatim

------------------------------------------------------------------------
-- Printing

private
  greekName : Greek → String
  greekName alpha = "alpha"; greekName beta = "beta"; greekName gamma = "gamma"
  greekName delta = "delta"; greekName epsilon = "epsilon"; greekName theta = "theta"
  greekName lambda = "lambda"; greekName mu = "mu"; greekName nu = "nu"
  greekName pi = "pi"; greekName rho = "rho"; greekName sigma = "sigma"
  greekName tau = "tau"; greekName phi = "phi"; greekName chi = "chi"
  greekName psi = "psi"; greekName omega = "omega"
  greekName Gamma = "Gamma"; greekName Delta = "Delta"; greekName Theta = "Theta"
  greekName Lambda = "Lambda"; greekName Pi = "Pi"; greekName Sigma = "Sigma"
  greekName Phi = "Phi"; greekName Psi = "Psi"; greekName Omega = "Omega"

  fnName : Fn → String
  fnName sin = "sin"; fnName cos = "cos"; fnName tan = "tan"
  fnName exp = "exp"; fnName ln = "ln"; fnName log = "log"

  relSymbol : Rel → String
  relSymbol eq = "="; relSymbol neq = "\\neq"; relSymbol lt = "<"
  relSymbol gt = ">"; relSymbol le = "\\leq"; relSymbol ge = "\\geq"
  relSymbol approx = "\\approx"; relSymbol to = "\\to"
  relSymbol mid = "\\mid"; relSymbol elem = "\\in"

  -- Characters that are special in LaTeX text mode.
  escapeChar : Char → String
  escapeChar '\\' = "\\textbackslash{}"
  escapeChar '{'  = "\\{"
  escapeChar '}'  = "\\}"
  escapeChar '_'  = "\\_"
  escapeChar '^'  = "\\^{}"
  escapeChar '&'  = "\\&"
  escapeChar '%'  = "\\%"
  escapeChar '#'  = "\\#"
  escapeChar '$'  = "\\$"
  escapeChar '~'  = "\\~{}"
  escapeChar c    = fromList (c ∷ [])

  escape : String → String
  escape s = Data.String.concat (map escapeChar (toList s))

  grp : String → String
  grp s = "{" ++ˢ s ++ˢ "}"

commaSep : List String → String
commaSep []           = ""
commaSep (x ∷ [])     = x
commaSep (x ∷ y ∷ xs) = x ++ˢ ", " ++ˢ commaSep (y ∷ xs)

mutual
  toLaTeXs : List Math → List String
  toLaTeXs []       = []
  toLaTeXs (m ∷ ms) = toLaTeX m ∷ toLaTeXs ms

  toLaTeX : Math → String
  toLaTeX (var s)            = s
  toLaTeX (num n)            = show n
  toLaTeX (greek g)          = "\\" ++ˢ greekName g
  toLaTeX (add a b)          = toLaTeX a ++ˢ " + " ++ˢ toLaTeX b
  toLaTeX (sub a b)          = toLaTeX a ++ˢ " - " ++ˢ toLaTeX b
  toLaTeX (mul a b)          = toLaTeX a ++ˢ " \\cdot " ++ˢ toLaTeX b
  toLaTeX (neg a)            = "-" ++ˢ toLaTeX a
  toLaTeX (frac a b)         = "\\frac" ++ˢ grp (toLaTeX a) ++ˢ grp (toLaTeX b)
  toLaTeX (pow a b)          = grp (toLaTeX a) ++ˢ "^" ++ˢ grp (toLaTeX b)
  toLaTeX (idx a b)          = grp (toLaTeX a) ++ˢ "_" ++ˢ grp (toLaTeX b)
  toLaTeX (sqrt a)           = "\\sqrt" ++ˢ grp (toLaTeX a)
  toLaTeX (fn f a)           = "\\" ++ˢ fnName f ++ˢ "\\left(" ++ˢ toLaTeX a ++ˢ "\\right)"
  toLaTeX (sum l u b)        = "\\sum_" ++ˢ grp (toLaTeX l) ++ˢ "^" ++ˢ grp (toLaTeX u) ++ˢ " " ++ˢ toLaTeX b
  toLaTeX (integral l u b)   = "\\int_" ++ˢ grp (toLaTeX l) ++ˢ "^" ++ˢ grp (toLaTeX u) ++ˢ " " ++ˢ toLaTeX b
  toLaTeX (prod l u b)       = "\\prod_" ++ˢ grp (toLaTeX l) ++ˢ "^" ++ˢ grp (toLaTeX u) ++ˢ " " ++ˢ toLaTeX b
  toLaTeX (paren a)          = "\\left(" ++ˢ toLaTeX a ++ˢ "\\right)"
  toLaTeX (rel r a b)        = toLaTeX a ++ˢ " " ++ˢ relSymbol r ++ˢ " " ++ˢ toLaTeX b
  toLaTeX (vec a)            = "\\vec" ++ˢ grp (toLaTeX a)
  toLaTeX (hat a)            = "\\hat" ++ˢ grp (toLaTeX a)
  toLaTeX (bar a)            = "\\bar" ++ˢ grp (toLaTeX a)
  toLaTeX (cal a)            = "\\mathcal" ++ˢ grp (toLaTeX a)
  toLaTeX (bb a)             = "\\mathbb" ++ˢ grp (toLaTeX a)
  toLaTeX (call f as)         = toLaTeX f ++ˢ "\\left(" ++ˢ commaSep (toLaTeXs as) ++ˢ "\\right)"
  toLaTeX (juxt a b)          = toLaTeX a ++ˢ "\\, " ++ˢ toLaTeX b
  toLaTeX (tuple as)          = commaSep (toLaTeXs as)
  toLaTeX (dd a)              = "\\,\\mathrm{d}" ++ˢ toLaTeX a
  toLaTeX (text s)           = "\\text" ++ˢ grp (escape s)
  toLaTeX (raw s)            = s

------------------------------------------------------------------------
-- Authoring: operators

infixl 6 _+_ _-_
infixl 7 _*_ _/_
infixr 8 _^_
infixl 9 _₍_₎
infix  4 _≡_ _≢_ _<_ _>_ _≤_ _≥_ _≈_ _⟶_

_+_ _-_ _*_ _/_ _^_ _₍_₎ : Math → Math → Math
_+_ = add
_-_ = sub
_*_ = mul
_/_ = frac
_^_ = pow
_₍_₎ = idx

_≡_ _≢_ _<_ _>_ _≤_ _≥_ _≈_ _⟶_ : Math → Math → Math
_≡_ = rel eq
_≢_ = rel neq
_<_ = rel lt
_>_ = rel gt
_≤_ = rel le
_≥_ = rel ge
_≈_ = rel approx
_⟶_ = rel to
