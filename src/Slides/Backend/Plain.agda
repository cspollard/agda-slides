{-# OPTIONS --safe --without-K #-}

-- The standalone HTML backend: the second `Shell` over the shared core (`Slides.Backend.Render`).
-- A slide is a `<section class="slide">`; a vertical stack is flattened into consecutive slides.
-- Navigation is `assets/plain.js`, and `assets/plain.css` prints every slide and fragment.
-- Blocks, fragments and laws are shared with `Slides.Backend.Reveal`.

module Slides.Backend.Plain where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Print using (renderXML)

open import Slides.Deck.Talk using (Talk)
open import Slides.Backend.HTML
open import Slides.Backend.Render

-- a slide: a section of class `slide` (plus the slide options)
slideSection : Attrs → Forest → XMLDoc
slideSection a = hElement "section" (("class" , "slide") ∷ a)

shell : Shell
shell = record
  { wrapSlide = λ a x → slideSection a x ∷ []
  ; wrapStack = λ a xs → map (slideSection a) xs }

record PlainConfig : Set where
  field
    title       : String
    stylesheets : List String       -- relative to the page
    katex       : Maybe String      -- URL or path of a KaTeX distribution (trailing slash), for math

defaultConfig : PlainConfig
defaultConfig = record { title = "Slides" ; stylesheets = "plain.css" ∷ "slides.css" ∷ [] ; katex = nothing }

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
    katexJs (just k) = scriptTag (k ++ˢ "katex.min.js") ∷ scriptTag (k ++ˢ "contrib/auto-render.min.js") ∷ []

renderPlain : PlainConfig → Talk → String
renderPlain cfg t = prologue ++ˢ renderXML (page cfg (renderTalk shell t))
