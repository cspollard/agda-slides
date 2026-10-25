{-# OPTIONS --safe --without-K #-}

-- Text measurement for diagram layout.
--
-- There is no browser here, so widths come from a table: the advance of each
-- printable ASCII character in a humanist sans-serif (Helvetica's widths,
-- scaled by 92% toward reveal.js's Source Sans), in thousandths of an em.
-- Other characters count as `fallback`.  The numbers are an approximation
-- that is good to a few percent for ordinary text, which is what centring,
-- spacing and word wrapping need; give a box an explicit width when a fit
-- must be exact.  Subscripts and superscripts are 70% of the size.

module Slides.Diagram.TextMetrics where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; suc; _+_; _*_; _/_; _∸_)
open import Data.String using (String; toList)

open import Slides.Diagram.Markup

-- widths of ' ' … '~' (codes 32 … 126), per mille of Helvetica
private
  table : List ℕ
  table =
    278 ∷ 278 ∷ 355 ∷ 556 ∷ 556 ∷ 889 ∷ 667 ∷ 191 ∷ 333 ∷ 333 ∷ 389 ∷ 584 ∷ 278 ∷ 333 ∷ 278 ∷ 278 ∷
    556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 556 ∷ 278 ∷ 278 ∷ 584 ∷ 584 ∷ 584 ∷ 556 ∷
    1015 ∷ 667 ∷ 667 ∷ 722 ∷ 722 ∷ 667 ∷ 611 ∷ 778 ∷ 722 ∷ 278 ∷ 500 ∷ 667 ∷ 556 ∷ 833 ∷ 722 ∷ 778 ∷
    667 ∷ 778 ∷ 722 ∷ 667 ∷ 611 ∷ 722 ∷ 667 ∷ 944 ∷ 667 ∷ 667 ∷ 611 ∷ 278 ∷ 278 ∷ 278 ∷ 469 ∷ 556 ∷
    333 ∷ 556 ∷ 556 ∷ 500 ∷ 556 ∷ 556 ∷ 278 ∷ 556 ∷ 556 ∷ 222 ∷ 222 ∷ 500 ∷ 222 ∷ 833 ∷ 556 ∷ 556 ∷
    556 ∷ 556 ∷ 333 ∷ 500 ∷ 278 ∷ 556 ∷ 500 ∷ 722 ∷ 500 ∷ 500 ∷ 500 ∷ 334 ∷ 260 ∷ 334 ∷ 584 ∷ []

  nth : List ℕ → ℕ → ℕ → ℕ
  nth []       _       d = d
  nth (w ∷ ws) 0       d = w
  nth (w ∷ ws) (suc n) d = nth ws n d

-- Greek and other non-ASCII symbols
fallback : ℕ
fallback = 600

-- advance of a character, per mille of the font size
charWidth : Char → ℕ
charWidth c = (nth table (toℕ c ∸ 32) fallback * 92) / 100

private
  run : String → ℕ
  run t = foldr (λ c n → charWidth c + n) 0 (toList t)

-- width of a label (markup included) at a font size, per mille of the size
-- times the size, i.e. in the diagram's own units
textWidth : ℕ → String → ℕ
textWidth size t = (go (parse t) * size) / 1000
  where
    go : List Seg → ℕ
    go []              = 0
    go (flat u ∷ ss)   = run u + go ss
    go (sub u ∷ ss)    = (run u * 7) / 10 + go ss
    go (sup u ∷ ss)    = (run u * 7) / 10 + go ss

-- the width of a space at a font size
spaceWidth : ℕ → ℕ
spaceWidth size = (charWidth ' ' * size) / 1000
