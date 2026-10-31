{-# OPTIONS --safe --without-K #-}

-- Typed mathematics: formulas as the free monad of a small signature (identifiers are variables,
-- so substitution is `>>=`), printed to LaTeX by `toLaTeX`, a fold.
--
-- Structure is checked when the deck typechecks (a fraction has two arguments, a sum has
-- bounds), and the printer wraps every argument of `frac`, `^`, `_` and `\sqrt` in braces, so
-- the output has no unbalanced group or ambiguous superscript.  `raw` is the escape hatch.
-- With `Slides.Deck.Literals` in scope, `2` is `num 2` and `"x"` the identifier `x`.

module Slides.Math where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_; map; lookup; tabulate)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.String using (String; concat; fromList; toList) renaming (_++_ to _++ˢ_)
open import Data.Char using (Char)
open import Function.Base using (_∘_)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
import Data.List.Properties as ListP
open import Function.Nary.NonDependent using (congₙ)
import Relation.Binary.PropositionalEquality as ≡P

open import Container.Pick using (pick2)
open import Container.Interpret.Plain using (Handler; pfold; Congruent; pfold-bind)

data Greek : Set where
  alpha beta gamma delta epsilon theta lambda mu nu pi rho sigma tau phi chi psi omega : Greek
  Gamma Delta Theta Lambda Pi Sigma Phi Psi Omega : Greek

data Fn : Set where
  sin cos tan exp ln log : Fn

data Rel : Set where
  eq neq lt gt le ge approx to mid elem : Rel

-- The signature: a command of `n` children is an `Op n`; its positions are `Fin n`.  Formulas are
-- the free monad over it with identifiers as variables (`var = pure`), so substituting a formula
-- for an identifier is `>>=`, and a printer is a handler read by `pfold`.
data Op : ℕ → Set where
  numO                    : ℕ → Op 0
  greekO                  : Greek → Op 0
  textO rawO              : String → Op 0               -- upright text; LaTeX, verbatim
  negO sqrtO parenO       : Op 1
  vecO hatO barO calO bbO : Op 1                        -- \vec, \hat, \bar, \mathcal, \mathbb
  ddO                     : Op 1                        -- \mathrm{d}x, with a thin space before
  fnO                     : Fn → Op 1                   -- \sin\left(…\right)
  addO subO mulO          : Op 2                        -- a + b, a - b, a \cdot b
  fracO powO idxO juxtO   : Op 2                        -- juxtaposed with a thin space
  relO                    : Rel → Op 2
  sumO integralO prodO    : Op 3                        -- lower, upper, body
  callO                   : (n : ℕ) → Op (suc n)        -- f\left(a, b\right): the head, then n arguments
  tupleO                  : (n : ℕ) → Op n              -- a, b, c (no brackets)

MathC : Container 0ℓ 0ℓ
MathC = Σ ℕ Op ▷ (Fin ∘ proj₁)

Math : Set
Math = MathC ⋆ String

-- Authoring: the constructors of the surface language

private
  node : ∀ {n} → Op n → (Fin n → Math) → Math
  node o k = impure ((_ , o) , k)

  atom : Op 0 → Math
  atom o = node o λ ()

  un : Op 1 → Math → Math
  un o a = node o λ _ → a

  bin : Op 2 → Math → Math → Math
  bin o a b = node o (pick2 a b)

  tri : Op 3 → Math → Math → Math → Math
  tri o a b c = node o λ { zero → a ; (suc zero) → b ; (suc (suc zero)) → c }

var : String → Math              -- an identifier, printed as written
var = pure

num : ℕ → Math
num n = atom (numO n)

greek : Greek → Math
greek g = atom (greekO g)

text raw : String → Math         -- upright text; LaTeX, verbatim
text s = atom (textO s)
raw s  = atom (rawO s)

add sub mul frac pow idx juxt : Math → Math → Math
add = bin addO; sub = bin subO; mul = bin mulO; frac = bin fracO
pow = bin powO; idx = bin idxO; juxt = bin juxtO

neg sqrt paren vec hat bar cal bb dd : Math → Math
neg = un negO; sqrt = un sqrtO; paren = un parenO; vec = un vecO; hat = un hatO
bar = un barO; cal = un calO; bb = un bbO; dd = un ddO

fn : Fn → Math → Math
fn f = un (fnO f)

rel : Rel → Math → Math → Math
rel r = bin (relO r)

sum integral prod : (lower upper body : Math) → Math
sum = tri sumO; integral = tri integralO; prod = tri prodO

call : Math → List Math → Math
call f as = node (callO _) λ { zero → f ; (suc i) → lookup as i }

tuple : List Math → Math
tuple as = node (tupleO _) (lookup as)

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

  big : String → (Fin 3 → String) → String
  big cmd k = cmd ++ˢ grp (k zero) ++ˢ "^" ++ˢ grp (k (suc zero)) ++ˢ " " ++ˢ k (suc (suc zero))

commaSep : List String → String
commaSep []           = ""
commaSep (x ∷ [])     = x
commaSep (x ∷ y ∷ xs) = x ++ˢ ", " ++ˢ commaSep (y ∷ xs)

-- the LaTeX of a command, given that of its children
latex : Handler MathC String
latex (_ , numO n)      _ = show n
latex (_ , greekO g)    _ = "\\" ++ˢ greekName g
latex (_ , textO s)     _ = "\\text" ++ˢ grp (escape s)
latex (_ , rawO s)      _ = s
latex (_ , negO)        k = "-" ++ˢ k zero
latex (_ , sqrtO)       k = "\\sqrt" ++ˢ grp (k zero)
latex (_ , parenO)      k = "\\left(" ++ˢ k zero ++ˢ "\\right)"
latex (_ , vecO)        k = "\\vec" ++ˢ grp (k zero)
latex (_ , hatO)        k = "\\hat" ++ˢ grp (k zero)
latex (_ , barO)        k = "\\bar" ++ˢ grp (k zero)
latex (_ , calO)        k = "\\mathcal" ++ˢ grp (k zero)
latex (_ , bbO)         k = "\\mathbb" ++ˢ grp (k zero)
latex (_ , ddO)         k = "\\,\\mathrm{d}" ++ˢ k zero
latex (_ , fnO f)       k = "\\" ++ˢ fnName f ++ˢ "\\left(" ++ˢ k zero ++ˢ "\\right)"
latex (_ , addO)        k = k zero ++ˢ " + " ++ˢ k (suc zero)
latex (_ , subO)        k = k zero ++ˢ " - " ++ˢ k (suc zero)
latex (_ , mulO)        k = k zero ++ˢ " \\cdot " ++ˢ k (suc zero)
latex (_ , fracO)       k = "\\frac" ++ˢ grp (k zero) ++ˢ grp (k (suc zero))
latex (_ , powO)        k = grp (k zero) ++ˢ "^" ++ˢ grp (k (suc zero))
latex (_ , idxO)        k = grp (k zero) ++ˢ "_" ++ˢ grp (k (suc zero))
latex (_ , juxtO)       k = k zero ++ˢ "\\, " ++ˢ k (suc zero)
latex (_ , relO r)      k = k zero ++ˢ " " ++ˢ relSymbol r ++ˢ " " ++ˢ k (suc zero)
latex (_ , sumO)        k = big "\\sum_" k
latex (_ , integralO)   k = big "\\int_" k
latex (_ , prodO)       k = big "\\prod_" k
latex (_ , callO n)     k = k zero ++ˢ "\\left(" ++ˢ commaSep (tabulate (k ∘ suc)) ++ˢ "\\right)"
latex (_ , tupleO n)    k = commaSep (tabulate k)

toLaTeX : Math → String
toLaTeX = pfold MathC latex (λ s → s)

-- The printer respects pointwise-equal children: each command reads its children at finitely many
-- positions, so it is a function of those values, and `cong` through that function applies the
-- equalities at those positions (a command of arity 2 or 3 is `latex` at `pick2` or `pick3`; of arity 1, at a constant family).
private
  pick3 : ∀ {A : Set} → A → A → A → Fin 3 → A
  pick3 a b c zero               = a
  pick3 a b c (suc zero)         = b
  pick3 a b c (suc (suc zero))   = c

latex-cong : Congruent MathC (≡P.setoid String) latex
latex-cong (_ , numO _)    e = ≡P.refl
latex-cong (_ , greekO _)  e = ≡P.refl
latex-cong (_ , textO _)   e = ≡P.refl
latex-cong (_ , rawO _)    e = ≡P.refl
latex-cong (_ , negO) e = ≡P.cong (λ x → latex (_ , negO) (λ _ → x)) (e zero)
latex-cong (_ , sqrtO) e = ≡P.cong (λ x → latex (_ , sqrtO) (λ _ → x)) (e zero)
latex-cong (_ , parenO) e = ≡P.cong (λ x → latex (_ , parenO) (λ _ → x)) (e zero)
latex-cong (_ , vecO) e = ≡P.cong (λ x → latex (_ , vecO) (λ _ → x)) (e zero)
latex-cong (_ , hatO) e = ≡P.cong (λ x → latex (_ , hatO) (λ _ → x)) (e zero)
latex-cong (_ , barO) e = ≡P.cong (λ x → latex (_ , barO) (λ _ → x)) (e zero)
latex-cong (_ , calO) e = ≡P.cong (λ x → latex (_ , calO) (λ _ → x)) (e zero)
latex-cong (_ , bbO) e = ≡P.cong (λ x → latex (_ , bbO) (λ _ → x)) (e zero)
latex-cong (_ , ddO) e = ≡P.cong (λ x → latex (_ , ddO) (λ _ → x)) (e zero)
latex-cong (_ , fnO f) e = ≡P.cong (λ x → latex (_ , fnO f) (λ _ → x)) (e zero)
latex-cong (_ , addO) e = ≡P.cong₂ (λ x y → latex (_ , addO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , subO) e = ≡P.cong₂ (λ x y → latex (_ , subO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , mulO) e = ≡P.cong₂ (λ x y → latex (_ , mulO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , fracO) e = ≡P.cong₂ (λ x y → latex (_ , fracO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , powO) e = ≡P.cong₂ (λ x y → latex (_ , powO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , idxO) e = ≡P.cong₂ (λ x y → latex (_ , idxO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , juxtO) e = ≡P.cong₂ (λ x y → latex (_ , juxtO) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , relO r) e = ≡P.cong₂ (λ x y → latex (_ , relO r) (pick2 x y)) (e zero) (e (suc zero))
latex-cong (_ , sumO) e = congₙ 3 (λ x y z → latex (_ , sumO) (pick3 x y z)) (e zero) (e (suc zero)) (e (suc (suc zero)))
latex-cong (_ , integralO) e = congₙ 3 (λ x y z → latex (_ , integralO) (pick3 x y z)) (e zero) (e (suc zero)) (e (suc (suc zero)))
latex-cong (_ , prodO) e = congₙ 3 (λ x y z → latex (_ , prodO) (pick3 x y z)) (e zero) (e (suc zero)) (e (suc (suc zero)))
latex-cong (_ , callO n)   e = ≡P.cong₂ (λ x y → x ++ˢ "\\left(" ++ˢ y ++ˢ "\\right)") (e zero) (≡P.cong commaSep (ListP.tabulate-cong (e ∘ suc)))
latex-cong (_ , tupleO n)  e = ≡P.cong commaSep (ListP.tabulate-cong e)

-- Substitution commutes with printing: print the formula with each identifier replaced by the
-- print of its substitute (`pfold-bind` at the setoid of strings).
toLaTeX-bind : ∀ (m : Math) (σ : String → Math) →
               toLaTeX (m >>= σ) ≡P.≡ pfold MathC latex (λ x → toLaTeX (σ x)) m
toLaTeX-bind m σ = pfold-bind (≡P.setoid String) latex-cong σ (λ _ → ≡P.refl) m

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
