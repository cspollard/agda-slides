{-# OPTIONS --without-K --guardedness #-}

-- R0 spike (docs/Design.md): a hand-built reveal.js deck as a parsnip XML
-- value, printed with the verified printer.  Not part of the library; it
-- exists to find out what a browser makes of parsnip's output.
--
-- Build and run:  make spike

module Slides.Spike.Reveal where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Unit using ()
open import IO using (Main; run; writeFile; _>>_)

open import Data.XML.AST using (XMLM; XMLDoc)
open import Data.XML.Print using (renderXML)
open import Data.XML.Sanitize using (element; textElement)

private variable
  A : Set

base : String
base = "reveal/dist/"

-- A <script src> must not self-close in text/html, so it carries one space.
script : String → XMLM A
script src = textElement "script" (("src" , src) ∷ []) " "

stylesheet : String → XMLM A
stylesheet href = element "link" (("rel" , "stylesheet") ∷ ("href" , href) ∷ []) []

div : String → List (XMLM A) → XMLM A
div cls = element "div" (("class" , cls) ∷ [])

section : List (XMLM A) → XMLM A
section = element "section" []

fragment : String → XMLM A
fragment t = textElement "li" (("class" , "fragment") ∷ []) t

slides : List (XMLM A)
slides =
  -- 1. title
  section ( textElement "h1" [] "R0 spike"
          ∷ textElement "p" [] "parsnip → reveal.js"
          ∷ [] )
  -- 2. bullets with fragments
  ∷ section ( textElement "h2" [] "Fragments"
            ∷ element "ul" [] ( fragment "first" ∷ fragment "second" ∷ fragment "third" ∷ [] )
            ∷ [] )
  -- 3. a vertical stack, with speaker notes
  ∷ section ( section ( textElement "h2" [] "Vertical A" ∷ [] )
            ∷ section ( textElement "h2" [] "Vertical B"
                      ∷ textElement "aside" (("class" , "notes") ∷ []) "Speaker notes"
                      ∷ [] )
            ∷ [] )
  -- 4. math, and text that needs escaping
  ∷ section ( textElement "h2" [] "Math"
            ∷ textElement "p" [] "\\( E = mc^2 \\)"
            ∷ textElement "p" (("id" , "escaped") ∷ []) "if a < b && c > d"
            ∷ [] )
  -- 5. code
  ∷ section ( textElement "h2" [] "Code"
            ∷ element "pre" []
                ( textElement "code" (("class" , "language-agda") ∷ ("data-trim" , "") ∷ [])
                    "id : {A : Set} → A → A\nid x = x"
                ∷ [] )
            ∷ [] )
  -- 6. the self-closing gap: an empty <div> followed by a paragraph
  ∷ section ( textElement "h2" [] "Empty elements"
            ∷ element "div" (("id" , "unpadded") ∷ []) []
            ∷ textElement "p" (("id" , "after-unpadded") ∷ []) "after the unpadded div"
            ∷ textElement "div" (("id" , "padded") ∷ []) " "
            ∷ textElement "p" (("id" , "after-padded") ∷ []) "after the padded div"
            ∷ [] )
  ∷ []

page : XMLDoc
page =
  element "html" (("lang" , "en") ∷ [])
    ( element "head" []
        ( element "meta" (("charset" , "utf-8") ∷ []) []
        ∷ textElement "title" [] "R0 spike"
        ∷ stylesheet (base ++ "reset.css")
        ∷ stylesheet (base ++ "reveal.css")
        ∷ stylesheet (base ++ "theme/black.css")
        ∷ [] )
    ∷ element "body" []
        ( div "reveal" (div "slides" slides ∷ [])
        ∷ script (base ++ "reveal.js")
        ∷ script (base ++ "plugin/notes.js")
        ∷ script (base ++ "plugin/math.js")
        ∷ script "init.js"
        ∷ [] )
    ∷ [] )

initJS : String
initJS = "Reveal.initialize({hash: true, plugins: [RevealNotes, RevealMath.KaTeX]});\n"

main : Main
main = run
  ( writeFile "out/spike/index.html" ("<!DOCTYPE html>\n" ++ renderXML page)
  >> writeFile "out/spike/init.js" initJS )
