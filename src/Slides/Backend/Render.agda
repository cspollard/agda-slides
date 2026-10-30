{-# OPTIONS --safe --without-K #-}

-- Rendering: the fold of the deck's free monoids into the monoid of HTML forests (`List XMLDoc`),
-- shared by both HTML backends, which differ only in a `Shell` (how slides and stacks are
-- wrapped) and the page around the forest.
--
--   renderFlow   Flow → Forest           each block contributes its markup
--   renderSlide  Slide → Forest          first chunk shown, each later one a fragment
--   renderTalk   Shell → Talk → Forest   parts rendered one by one
-- Notes and scripts are never inside a fragment, which would hide them with its chunk.
-- Laws: `Slides.Backend.Render.Properties`.

module Slides.Backend.Render where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; filterᵇ)
open import Data.List.NonEmpty using (List⁺; _∷_)
import Data.List.NonEmpty as L⁺
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Data.XML.AST using (XMLDoc)

open import Slides.Scalar.Model.Nat using (natSpace)
open import Slides.Diagram.Print using (natPrint; renderSVG)
import Slides.Diagram.Layout natSpace as DL
open import Slides.Math using (toLaTeX)
open import Slides.Text using (css)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Backend.HTML
open import Slides.Backend.Animation using (animationEl; steps; loop; both; stillEl)
open import Slides.Deck.Anim using (sequence; rests)

Forest : Set
Forest = List XMLDoc

-- Inline markup

private
  Piece : Set
  Piece = String ⊎ XMLDoc

  -- merge adjacent text into the text slots of mixed content
  normalise : List Piece → String × List (XMLDoc × String)
  normalise []              = "" , []
  normalise (inj₁ s ∷ ps)   with normalise ps
  ... | t , cs = (s ++ˢ t) , cs
  normalise (inj₂ x ∷ ps)   with normalise ps
  ... | t , cs = "" , (x , t) ∷ cs

mutual
  pieces : List Inline → List Piece
  pieces []       = []
  pieces (i ∷ is) = piece i ++ pieces is

  piece : Inline → List Piece
  piece (text s)       = inj₁ s ∷ []
  piece (inlineMath m) = inj₁ ("\\(" ++ˢ toLaTeX m ++ˢ "\\)") ∷ []
  piece (emph is)      = inj₂ (rich "em" [] is) ∷ []
  piece (strong is)    = inj₂ (rich "strong" [] is) ∷ []
  piece br             = inj₂ (hElement "br" [] []) ∷ []
  piece (styled s is)  = inj₂ (rich "span" (("style" , css s) ∷ []) is) ∷ []
  piece (sub is)       = inj₂ (rich "sub" [] is) ∷ []
  piece (sup is)       = inj₂ (rich "sup" [] is) ∷ []
  piece (codeSpan s)   = inj₂ (hText "code" [] s) ∷ []
  piece (link u is)    = inj₂ (rich "a" (("href" , u) ∷ []) is) ∷ []
  piece (cite k)       = inj₂ (hText "span" (("class" , "cite") ∷ []) ("[" ++ˢ k ++ˢ "]")) ∷ []

  -- an element whose content is running text
  rich : String → Attrs → List Inline → XMLDoc
  rich tag attrs is = hMixed tag attrs (normalise (pieces is))

-- Blocks

hTag : ℕ → String
hTag n = "h" ++ˢ show (clamp n)
  where
    clamp : ℕ → ℕ
    clamp zero = 1
    clamp (suc zero) = 1
    clamp (suc (suc zero)) = 2
    clamp (suc (suc (suc zero))) = 3
    clamp (suc (suc (suc (suc zero)))) = 4
    clamp (suc (suc (suc (suc (suc zero))))) = 5
    clamp _ = 6

-- the attribute that sets an image's width, a percent of its container (the height follows)
widthAttr : Maybe ℕ → List (String × String)
widthAttr nothing  = []
widthAttr (just w) = ("style" , "width: " ++ˢ show w ++ˢ "%; height: auto") ∷ []

fragmentClass : Maybe String → String
fragmentClass nothing  = "fragment"
fragmentClass (just s) = "fragment " ++ˢ s

private
  div : String → List XMLDoc → XMLDoc
  div cls = hElement "div" (("class" , cls) ∷ [])

  pct : String → ℕ → String
  pct name n = name ++ˢ ":" ++ˢ show n ++ˢ "%;"

  -- a bullet's text, then its sub-bullets as a nested list
  mutual
    bulletEl : Bool → Bullet → XMLDoc
    bulletEl inc (bullet t cs) with normalise (pieces t)
    ... | s , xs = hMixed "li" (if inc then ("class" , "fragment") ∷ [] else []) (s , xs ++ nest inc cs)

    nest : Bool → List Bullet → List (XMLDoc × String)
    nest inc [] = []
    nest inc cs = (hElement "ul" [] (bulletList inc cs) , "") ∷ []

    bulletList : Bool → List Bullet → List XMLDoc
    bulletList inc []       = []
    bulletList inc (c ∷ cs) = bulletEl inc c ∷ bulletList inc cs

  row : String → List Text → XMLDoc
  row cell cs = hElement "tr" [] (map (rich cell []) cs)


mutual
  renderBlock : Block → Forest
  renderBlock (heading n t)    = rich (hTag n) [] t ∷ []
  renderBlock (paragraph t)    = rich "p" [] t ∷ []
  renderBlock (bulletTree inc is) = hElement "ul" [] (bulletList inc is) ∷ []
  renderBlock (code lang src)  =
    hElement "pre" [] (hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ []) ∷ []
  renderBlock (displayMath m)  = hText "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ toLaTeX m ++ˢ " \\]") ∷ []
  renderBlock (figure src w cap) =
    hElement "figure" []
      ( hElement "img" (("src" , src) ∷ ("alt" , plainT cap) ∷ widthAttr w) []
      ∷ rich "figcaption" [] cap ∷ [] )
    ∷ []
  renderBlock (notes t)        = rich "aside" (("class" , "notes") ∷ []) t ∷ []
  renderBlock (table h rows)   =
    hElement "table" []
      ( hElement "thead" [] (row "th" h ∷ [])
      ∷ hElement "tbody" [] (map (row "td") rows) ∷ [] )
    ∷ []
  renderBlock (references rs)  =
    hElement "ol" (("class" , "references") ∷ [])
      (map (λ r → rich "li" (("id" , "ref-" ++ˢ proj₁ r) ∷ []) (proj₂ r)) rs)
    ∷ []
  renderBlock (diagram n p d)  =
    hElement "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG natPrint n p (DL.layout d) ∷ []) ∷ []
  renderBlock (animation n p ms [])       = []
  renderBlock (animation n p ms (a ∷ as)) = animationEl n p ms steps (sequence (a ∷ as)) (rests (a ∷ as)) ∷ []
  renderBlock (animationLoop n p ms a)    = animationEl n p ms loop a [] ∷ []
  renderBlock (animationBoth n p ms k a rs) = animationEl n p ms (both k) a rs ∷ []
  renderBlock (still n p l)    = stillEl n p l ∷ []
  renderBlock (script js)      =
    hElement "div" (("class" , "js") ∷ ("hidden" , "") ∷ ("data-js" , js) ∷ []) [] ∷ []
  renderBlock (mount i)        = hElement "div" (("id" , i) ∷ ("class" , "mount") ∷ []) [] ∷ []
  renderBlock (columns cs)     = div "columns" (renderColumns cs) ∷ []
  renderBlock (box t f)        = div "box" (rich "div" (("class" , "box-title") ∷ []) t ∷ renderFlow f) ∷ []
  renderBlock (fragment st f)  = div (fragmentClass st) (renderFlow f) ∷ []
  renderBlock (classed cls f)  = div cls (renderFlow f) ∷ []
  renderBlock (placed x y w h f) =
    hElement "div" (("class" , "placed") ∷ ("style" , pct "left" x ++ˢ pct "top" y ++ˢ pct "width" w ++ˢ pct "height" h) ∷ [])
      (renderFlow f) ∷ []

  renderFlow : Flow → Forest
  renderFlow []       = []
  renderFlow (b ∷ bs) = renderBlock b ++ renderFlow bs

  renderColumns : List Flow → Forest
  renderColumns []       = []
  renderColumns (c ∷ cs) = div "column" (renderFlow c) ∷ renderColumns cs

-- Slides: the first chunk is shown, each later chunk is a fragment

aside? : Block → Bool
aside? (notes _)  = true
aside? (script _) = true
aside? _          = false

-- a later chunk: its visible blocks in a fragment, its notes and scripts beside it
renderStep : Flow → Forest
renderStep f = visible (filterᵇ (λ b → not (aside? b)) f) ++ renderFlow (filterᵇ aside? f)
  where visible : Flow → Forest
        visible []          = []
        visible v@(_ ∷ _)   = div "fragment" (renderFlow v) ∷ []

renderChunks : List⁺ Flow → Forest
renderChunks (c ∷ cs) = renderFlow c ++ concatMap renderStep cs

renderSlide : Slide → Forest
renderSlide s = renderChunks (Slide.chunkL s)

-- Parts and talks: the backend is a shell

-- how a backend wraps a slide's forest (attributes: the look and the label) and a vertical stack
record Shell : Set where
  field
    wrapSlide : Attrs → Forest → Forest
    wrapStack : Attrs → List Forest → Forest

private
  opt : String → Maybe String → Attrs
  opt k nothing  = []
  opt k (just v) = (k , v) ∷ []

-- slide options become `data-*` attributes; a slide's label is its `id`, so a browser goes to it
-- by `#/label` (a stack's label is on its outer section)
lookAttrs : Look → Maybe String → Attrs
lookAttrs o l = opt "data-background-color" (Look.background o) ++ opt "data-transition" (Look.transition o) ++ opt "id" l

renderPart : Shell → Part → Forest
renderPart sh (solo o s)          = Shell.wrapSlide sh (lookAttrs o (Slide.label s)) (renderSlide s)
renderPart sh (vstack o (s ∷ ss)) = Shell.wrapStack sh (lookAttrs o (Slide.label s)) (map renderSlide (s ∷ ss))

renderTalk : Shell → Talk → Forest
renderTalk sh = concatMap (renderPart sh)

-- Restyling is a homomorphism of backends

restyle : (XMLDoc → XMLDoc) → Shell → Shell
restyle f sh = record
  { wrapSlide = λ a x → map f (Shell.wrapSlide sh a x)
  ; wrapStack = λ a xs → map f (Shell.wrapStack sh a xs) }

