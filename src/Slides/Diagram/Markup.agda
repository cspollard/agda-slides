{-# OPTIONS --safe --without-K #-}

-- Label markup, shared by the renderer (`Slides.Backend.Diagram`) and the text
-- measurement of `Slides.Diagram.Layout`: `_x` or `_{xyz}` is a subscript, `^x`
-- or `^{xyz}` a superscript, and a backslash quotes the next character.

module Slides.Diagram.Markup where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; reverse; [_])
open import Data.String using (String; fromList; toList)

data Seg : Set where
  flat sub sup : String → Seg

private
  mutual
    segs : List Char → List Char → List Seg
    segs acc []               = flush acc []
    segs acc ('\\' ∷ c ∷ cs) = segs (c ∷ acc) cs
    segs acc ('_' ∷ cs)       = flush acc (scripted sub cs)
    segs acc ('^' ∷ cs)       = flush acc (scripted sup cs)
    segs acc (c ∷ cs)         = segs (c ∷ acc) cs

    scripted : (String → Seg) → List Char → List Seg
    scripted k []          = []
    scripted k ('{' ∷ cs)  = braced k [] cs
    scripted k (c ∷ cs)    = k (fromList [ c ]) ∷ segs [] cs

    braced : (String → Seg) → List Char → List Char → List Seg
    braced k acc []          = k (fromList (reverse acc)) ∷ []
    braced k acc ('}' ∷ cs)  = k (fromList (reverse acc)) ∷ segs [] cs
    braced k acc (c ∷ cs)    = braced k (c ∷ acc) cs

    flush : List Char → List Seg → List Seg
    flush [] rest = rest
    flush acc rest = flat (fromList (reverse acc)) ∷ rest

parse : String → List Seg
parse t = segs [] (toList t)
