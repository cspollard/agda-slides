{-# OPTIONS --safe --without-K #-}

-- The standalone HTML backend.
--
-- It shares the vocabulary mapping with the reveal.js backend
-- (`Slides.Backend.Common`) and differs in the deck algebra and the page:
-- every slide is a `<section class="slide">`, a vertical stack is flattened
-- into consecutive slides, and navigation is a small external script
-- (`assets/plain.js`) with a print stylesheet (`assets/plain.css`) that shows
-- every slide and fragment.

module Slides.Backend.Plain where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Categories.Functor.Algebra using (F-Algebra)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (XMLSetoid)
open import Data.XML.Print using (renderXML)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Core
open import Slides.Steps using (steps)
open import Slides.Backend.HTML
open import Slides.Backend.Common

module D = Alg 0ℓ 0ℓ DeckC

-- A slide: a section of class `slide` (plus the slide options).
slideSection : SlideOptions → Forest → XMLDoc
slideSection o = hElement "section" (("class" , "slide") ∷ slideAttrs o)

deckAlg : F-Algebra D.F
deckAlg = record
  { A = ForestSetoid
  ; α = record
      { to   = λ { (slide o b , k)  → slideSection o (renderBody (steps b)) ∷ k tt
                 ; (stack o bs , k) → map (slideSection o ∘ renderBody ∘ steps) bs ++ k tt }
      ; cong = λ { {slide _ _ , _} {slide _ _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt
                 ; {stack o bs , _} {stack _ _ , _} (refl ,ₚ k≈) →
                     PW.++⁺ (Setoid.refl ForestSetoid {map (slideSection o ∘ renderBody ∘ steps) bs}) (k≈ tt) }
      }
  }

renderDeck : Deck → Forest
renderDeck = D.fold deckAlg {⊤ˢ} nil

------------------------------------------------------------------------
-- The page

record PlainConfig : Set where
  field
    title       : String
    stylesheets : List String       -- relative to the page
    -- URL or path of a KaTeX distribution (with trailing slash), for math
    katex       : Maybe String

defaultConfig : PlainConfig
defaultConfig = record
  { title       = "Slides"
  ; stylesheets = "plain.css" ∷ "slides.css" ∷ []
  ; katex       = nothing
  }

page : PlainConfig → Forest → XMLDoc
page cfg slides =
  hElement "html" (("lang" , "en") ∷ [])
    ( hElement "head" []
        ( hElement "meta" (("charset" , "utf-8") ∷ []) []
        ∷ hText "title" [] (PlainConfig.title cfg)
        ∷ map stylesheet (PlainConfig.stylesheets cfg)
        ++ katexCss (PlainConfig.katex cfg) )
    ∷ hElement "body" []
        ( hElement "div" (("class" , "deck") ∷ []) slides
        ∷ hElement "div" (("class" , "progress") ∷ []) []
        ∷ katexJs (PlainConfig.katex cfg)
        ++ scriptTag "animation.js" ∷ scriptTag "plain.js" ∷ [] )
    ∷ [] )
  where
    katexCss : Maybe String → List XMLDoc
    katexCss nothing  = []
    katexCss (just k) = stylesheet (k ++ˢ "katex.min.css") ∷ []

    katexJs : Maybe String → List XMLDoc
    katexJs nothing  = []
    katexJs (just k) = scriptTag (k ++ˢ "katex.min.js")
                     ∷ scriptTag (k ++ˢ "contrib/auto-render.min.js") ∷ []

-- `index.html`, with the (unverified, constant) doctype prefix.
renderPlain : PlainConfig → Deck → String
renderPlain cfg d = doctype ++ˢ renderXML (page cfg (renderDeck d))
