{-# OPTIONS --safe --without-K #-}

-- Text measurement: there is no browser here, so widths come from a table of advances (per
-- mille of the font size) for printable ASCII, a humanist sans-serif scaled toward the slide
-- font; other characters count as `fallback`.  Good to a few percent, which is what centring
-- and spacing need.  Scripts are 70% of the size.  The result is a plain number of units;
-- `Syntax.text` turns it into the frame of a `Text` primitive (the only place a ℕ becomes a
-- length), so layout itself never measures anything.

module Slides.Diagram.TextMetrics where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; suc; _+_; _*_; _/_; _∸_)
open import Data.String using (String; toList)
open import Slides.Text using (Inline; text; sub; sup; plainT; parse)

private
  table : List ℕ   -- ' ' … '~' (codes 32 … 126)
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

  fallback : ℕ
  fallback = 600

  charWidth : Char → ℕ
  charWidth c = (nth table (toℕ c ∸ 32) fallback * 92) / 100

  run : String → ℕ
  run t = foldr (λ c n → charWidth c + n) 0 (toList t)

  -- a construct other than a script is measured by its plain text
  go : List Inline → ℕ
  go []            = 0
  go (sub u ∷ ss)  = (run (plainT u) * 7) / 10 + go ss
  go (sup u ∷ ss)  = (run (plainT u) * 7) / 10 + go ss
  go (i ∷ ss)      = run (plainT (i ∷ [])) + go ss

-- width of a label at a font size, in the diagram's units
inlineWidth : ℕ → List Inline → ℕ
inlineWidth size is = (go is * size) / 1000

-- the same for a label written with markup
textWidth : ℕ → String → ℕ
textWidth size t = inlineWidth size (parse t)

-- the width of a space at a font size
spaceWidth : ℕ → ℕ
spaceWidth size = (charWidth ' ' * size) / 1000
