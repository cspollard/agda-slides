{-# OPTIONS --safe --without-K #-}

-- The fragments inside a block: what `forestCount (renderBlock b) ≡ blockSteps b` takes, under `sane`.
--
-- The page steps through the elements whose class has the token `fragment`.  The markup of a block
-- has such an element only where the model counts a step (`Slides.Deck.Steps.blockSteps`), except
-- where a string of the deck becomes a class, which can be anything, or an SVG, whose classes come
-- from style strings.  `sane` is the check of exactly those, decidable by computation:
--
--   `classed c`        the page sees as many fragment tokens in `c` as the model does (`fragClass`);
--                      they differ only when the sanitiser (`fixText`) repairs a character
--                      that separates words
--   `fragment (just s)`  the class `fragment s` has one (the sanitiser may join `fragment` to `s`)
--   `code lang _`      the class `language-lang` has none (`lang` could hold a space and `fragment`)
--   `diagram`, `still`, an animation  the printed `<svg>` has none (`svg?`): a style class
--                      comes from the deck's strings
--
-- Everything else (inline text, tables, figures, bullets, notes, ...) holds no fragment but its
-- own, whatever its strings: `Slides.Backend.Render.Inline`.

module Slides.Backend.Render.Sane where

open import Data.Bool.Base using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; length)
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (tt)
open import Data.Maybe.Base using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Data.Nat.Properties as ℕP
import Data.List.Properties as ListP

open import Data.XML.AST using (XMLDoc)
open import Slides.Scalar.Model.Nat using (natSpace)
import Slides.Diagram.Layout natSpace as DL
open import Slides.Diagram.Print using (natPrint; renderSVG)
open import Slides.Backend.Animation using (animationEl; steps; loop; both; qPrint; firstFrame; stillEl)
open import Slides.Deck.Anim using (sequence; rests)
open import Slides.Deck.Content
open import Slides.Deck.Syntax using (Slide; slide)
open import Slides.Deck.Talk using (Talk; slidesP)
open import Slides.Math using (toLaTeX)
open import Slides.Deck.Steps using (fragClass; blockSteps; flowSteps; columnsSteps; bulletSteps; bulletsSteps)
open import Slides.Backend.HTML using (div; hElement; hText; hMixed)
open import Slides.Backend.Fragments
open import Slides.Backend.Render
open import Slides.Backend.Render.Inline
open import Slides.Backend.Render.Svg

-- the class string `c` shows the page `m` fragment tokens
seen? : String → ℕ → Bool
seen? c m = classSeen c ≡ᵇ m

mutual
  sane : Block → Bool
  sane (code lang _)                  = seen? ("language-" ++ˢ lang) 0
  sane (diagram n p d)                = svg? natPrint n p (DL.layout d)
  sane (animation n p ms [])          = true
  sane (animation n p ms (a ∷ as))    = svg? qPrint n p (firstFrame (sequence (a ∷ as)))
  sane (animationLoop n p ms a)       = svg? qPrint n p (firstFrame a)
  sane (animationBoth n p ms k a rs)  = svg? qPrint n p (firstFrame a)
  sane (still n p l)                  = svg? qPrint n p l
  sane (columns cs)                   = saneC cs
  sane (box _ f)                      = saneF f
  sane (fragment nothing f)           = saneF f
  sane (fragment (just s) f)          = seen? ("fragment " ++ˢ s) 1 ∧ saneF f
  sane (classed c f)                  = seen? c (fragClass c) ∧ saneF f
  sane (placed _ _ _ _ f)             = saneF f
  sane (heading _ _)                  = true
  sane (paragraph _)                  = true
  sane (bulletTree _ _)               = true
  sane (displayMath _)                = true
  sane (figure _ _ _)                 = true
  sane (notes _)                      = true
  sane (table _ _)                    = true
  sane (references _)                 = true
  sane (script _)                     = true
  sane (mount _)                      = true

  saneF : Flow → Bool
  saneF []       = true
  saneF (b ∷ bs) = sane b ∧ saneF bs

  saneC : List Flow → Bool
  saneC []       = true
  saneC (f ∷ fs) = saneF f ∧ saneC fs

-- the class strings of a slide's chunks
saneSlide : Slide → Bool
saneSlide (slide _ (c ∷⁺ cs)) = saneF c ∧ saneC cs

saneTalk : Talk → Bool
saneTalk []       = true
saneTalk (p ∷ ps) = saneSlides (slidesP p) ∧ saneTalk ps
  where saneSlides : List Slide → Bool
        saneSlides []       = true
        saneSlides (s ∷ ss) = saneSlide s ∧ saneSlides ss

split : ∀ {a b} → T (a ∧ b) → T a × T b
split {true}  h = tt , h
split {false} ()

-- a single element is its own count
sing : ∀ d {n} → fragCount d ≡ n → forestCount (d ∷ []) ≡ n
sing d h = trans (ℕP.+-identityʳ (fragCount d)) h

-- Bullets: one step per item when incremental, the nested items included
private
  stepsB : Bool → Bullet → ℕ
  stepsB true  b = bulletSteps b
  stepsB false _ = 0

  stepsBs : Bool → List Bullet → ℕ
  stepsBs true  bs = bulletsSteps bs
  stepsBs false _  = 0

  incHit : ∀ inc → attrHit (if inc then ("class" , "fragment") ∷ [] else []) ≡ (if inc then 1 else 0)
  incHit true  = refl
  incHit false = refl

  -- an item is its own class, its text (no fragment) and its nested list
  bulletEl-core : ∀ inc t cs → fragCount (bulletEl inc (bullet t cs)) ≡ (if inc then 1 else 0) + forestCount (map proj₁ (nest inc cs))
  bulletEl-core inc t cs with normalise (pieces t) | normalise-count (pieces t)
  ... | s , xs | h =
    trans (hMixed-count "li" (if inc then ("class" , "fragment") ∷ [] else []) s (xs ++ nest inc cs))
          (cong₂ _+_ (incHit inc)
                 (trans (cong forestCount (ListP.map-++ proj₁ xs (nest inc cs)))
                        (trans (forestCount-++ (map proj₁ xs) (map proj₁ (nest inc cs)))
                               (cong (_+ forestCount (map proj₁ (nest inc cs))) (trans h (pieces-count t))))))

mutual
  bulletEl-count : ∀ inc b → fragCount (bulletEl inc b) ≡ stepsB inc b
  bulletEl-count true  (bullet t cs) = trans (bulletEl-core true t cs)  (cong suc (nest-count true cs))
  bulletEl-count false (bullet t cs) = trans (bulletEl-core false t cs) (nest-count false cs)

  nest-count : ∀ inc cs → forestCount (map proj₁ (nest inc cs)) ≡ stepsBs inc cs
  nest-count true  []         = refl
  nest-count false []         = refl
  nest-count inc   cs@(_ ∷ _) = sing (hElement "ul" [] (bulletList inc cs)) (trans (hElement-count "ul" [] (bulletList inc cs)) (bulletList-count inc cs))

  bulletList-count : ∀ inc bs → forestCount (bulletList inc bs) ≡ stepsBs inc bs
  bulletList-count true  []       = refl
  bulletList-count false []       = refl
  bulletList-count true  (b ∷ bs) = cong₂ _+_ (bulletEl-count true b)  (bulletList-count true bs)
  bulletList-count false (b ∷ bs) = cong₂ _+_ (bulletEl-count false b) (bulletList-count false bs)

-- Arithmetic of counts
add : ∀ n {a x y} → a ≡ n → x ≡ y → a + x ≡ n + y
add n ea ex = cong₂ _+_ ea ex

add₀ : ∀ {a x y} → a ≡ 0 → x ≡ y → a + x ≡ y
add₀ refl e = e

-- a table cell, row, ...: elements around text hold no fragment
row-count : ∀ cell cs → fragCount (row cell cs) ≡ 0
row-count cell cs = trans (hElement-count "tr" [] (map (rich cell []) cs)) (add₀ refl (forestCount-map₀ (rich cell []) cs (λ c → rich-count cell [] c)))

-- an image has no class
img-count : ∀ src alt w → fragCount (hElement "img" (("src" , src) ∷ ("alt" , alt) ∷ widthAttr w) []) ≡ 0
img-count src alt nothing  = hElement-count "img" (("src" , src) ∷ ("alt" , alt) ∷ widthAttr nothing) []
img-count src alt (just w) = hElement-count "img" (("src" , src) ∷ ("alt" , alt) ∷ widthAttr (just w)) []

-- The blocks.  A class that is counted (`fragment`, `classed`) is a hypothesis of `sane`; the rest is by computation.
mutual
  block-count : ∀ b → T (sane b) → forestCount (renderBlock b) ≡ blockSteps b
  block-count (heading n t)    _ = sing (rich (hTag n) [] t) (rich-count (hTag n) [] t)
  block-count (paragraph t)    _ = sing (rich "p" [] t) (rich-count "p" [] t)
  block-count (bulletTree inc is) _ =
    sing (hElement "ul" [] (bulletList inc is))
         (trans (hElement-count "ul" [] (bulletList inc is)) (add₀ refl (trans (bulletList-count inc is) (stepsBs≡ inc is))))
    where stepsBs≡ : ∀ inc is → stepsBs inc is ≡ (if inc then bulletsSteps is else 0)
          stepsBs≡ true  is = refl
          stepsBs≡ false is = refl
  block-count (code lang src)  h =
    sing (hElement "pre" [] (hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ []))
         (trans (hElement-count "pre" [] (hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ []))
                (add₀ refl (trans (ℕP.+-identityʳ _)
                                  (trans (hText-count "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src)
                                         (ℕP.≡ᵇ⇒≡ _ _ h)))))
  block-count (displayMath m)  _ =
    sing (hText "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ toLaTeX m ++ˢ " \\]"))
         (hText-count "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ toLaTeX m ++ˢ " \\]"))
  block-count (figure src w cap) _ =
    sing (hElement "figure" [] (hElement "img" (("src" , src) ∷ ("alt" , plainT cap) ∷ widthAttr w) [] ∷ rich "figcaption" [] cap ∷ []))
         (trans (hElement-count "figure" [] (hElement "img" (("src" , src) ∷ ("alt" , plainT cap) ∷ widthAttr w) [] ∷ rich "figcaption" [] cap ∷ []))
                (add₀ refl (add₀ (img-count src (plainT cap) w) (trans (ℕP.+-identityʳ _) (rich-count "figcaption" [] cap)))))
  block-count (notes t)        _ = sing (rich "aside" (("class" , "notes") ∷ []) t) (rich-count "aside" (("class" , "notes") ∷ []) t)
  block-count (table h rows)   _ =
    sing (hElement "table" [] (hElement "thead" [] (row "th" h ∷ []) ∷ hElement "tbody" [] (map (row "td") rows) ∷ []))
         (trans (hElement-count "table" [] (hElement "thead" [] (row "th" h ∷ []) ∷ hElement "tbody" [] (map (row "td") rows) ∷ []))
                (add₀ refl (add₀ (trans (hElement-count "thead" [] (row "th" h ∷ [])) (add₀ refl (trans (ℕP.+-identityʳ _) (row-count "th" h))))
                                 (trans (ℕP.+-identityʳ _)
                                        (trans (hElement-count "tbody" [] (map (row "td") rows))
                                               (add₀ refl (forestCount-map₀ (row "td") rows (row-count "td"))))))))
  block-count (references rs)  _ =
    sing (hElement "ol" (("class" , "references") ∷ []) (map (λ r → rich "li" (("id" , "ref-" ++ˢ proj₁ r) ∷ []) (proj₂ r)) rs))
         (trans (hElement-count "ol" (("class" , "references") ∷ []) (map (λ r → rich "li" (("id" , "ref-" ++ˢ proj₁ r) ∷ []) (proj₂ r)) rs))
                (add₀ refl (forestCount-map₀ (λ r → rich "li" (("id" , "ref-" ++ˢ proj₁ r) ∷ []) (proj₂ r)) rs
                                              (λ r → rich-count "li" (("id" , "ref-" ++ˢ proj₁ r) ∷ []) (proj₂ r)))))
  block-count (diagram n p d)  h =
    sing (hElement "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG natPrint n p (DL.layout d) ∷ []))
         (trans (hElement-count "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG natPrint n p (DL.layout d) ∷ []))
                (add₀ refl (trans (ℕP.+-identityʳ _) (svg-zero natPrint n p (DL.layout d) h))))
  block-count (animation n p ms []) _ = refl
  block-count (animation n p ms (a ∷ as)) h =
    sing (animationEl n p ms steps (sequence (a ∷ as)) (rests (a ∷ as)))
         (animation-count n p ms steps (sequence (a ∷ as)) (rests (a ∷ as)) h)
  block-count (animationLoop n p ms a) h = sing (animationEl n p ms loop a []) (animation-count n p ms loop a [] h)
  block-count (animationBoth n p ms k a rs) h = sing (animationEl n p ms (both k) a rs) (animation-count n p ms (both k) a rs h)
  block-count (still n p l)    h = sing (stillEl n p l) (still-count n p l h)
  block-count (script js)      _ = refl
  block-count (mount i)        _ = refl
  block-count (columns cs)     h =
    sing (div "columns" (renderColumns cs))
         (trans (hElement-count "div" (("class" , "columns") ∷ []) (renderColumns cs)) (add₀ refl (columns-count cs h)))
  block-count (box t f)        h =
    sing (div "box" (rich "div" (("class" , "box-title") ∷ []) t ∷ renderFlow f))
         (trans (hElement-count "div" (("class" , "box") ∷ []) (rich "div" (("class" , "box-title") ∷ []) t ∷ renderFlow f))
                (add₀ refl (add₀ (rich-count "div" (("class" , "box-title") ∷ []) t) (flow-count f h))))
  block-count (fragment nothing f) h =
    sing (div "fragment" (renderFlow f))
         (trans (hElement-count "div" (("class" , "fragment") ∷ []) (renderFlow f)) (add 1 refl (flow-count f h)))
  block-count (fragment (just s) f) h =
    sing (div ("fragment " ++ˢ s) (renderFlow f))
         (trans (hElement-count "div" (("class" , "fragment " ++ˢ s) ∷ []) (renderFlow f))
                (add 1 (ℕP.≡ᵇ⇒≡ _ _ (proj₁ (split h))) (flow-count f (proj₂ (split h)))))
  block-count (classed c f)    h =
    sing (div c (renderFlow f))
         (trans (hElement-count "div" (("class" , c) ∷ []) (renderFlow f))
                (add (fragClass c) (ℕP.≡ᵇ⇒≡ _ _ (proj₁ (split h))) (flow-count f (proj₂ (split h)))))
  block-count (placed x y w h′ f) h =
    sing (hElement "div" (("class" , "placed") ∷ ("style" , pct "left" x ++ˢ pct "top" y ++ˢ pct "width" w ++ˢ pct "height" h′) ∷ []) (renderFlow f))
         (trans (hElement-count "div" (("class" , "placed") ∷ ("style" , pct "left" x ++ˢ pct "top" y ++ˢ pct "width" w ++ˢ pct "height" h′) ∷ []) (renderFlow f))
                (add₀ refl (flow-count f h)))

  flow-count : ∀ f → T (saneF f) → forestCount (renderFlow f) ≡ flowSteps f
  flow-count []       _ = refl
  flow-count (b ∷ bs) h =
    trans (forestCount-++ (renderBlock b) (renderFlow bs)) (cong₂ _+_ (block-count b (proj₁ (split h))) (flow-count bs (proj₂ (split h))))

  columns-count : ∀ cs → T (saneC cs) → forestCount (renderColumns cs) ≡ columnsSteps cs
  columns-count []       _ = refl
  columns-count (f ∷ fs) h =
    cong₂ _+_ (trans (hElement-count "div" (("class" , "column") ∷ []) (renderFlow f)) (add₀ refl (flow-count f (proj₁ (split h)))))
              (columns-count fs (proj₂ (split h)))
