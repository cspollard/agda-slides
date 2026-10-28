{-# OPTIONS --safe --without-K #-}

-- The shared deck algebra: one core that both HTML backends use.
--
-- Rendering is the fold of the free monoids of the deck language into the monoid of forests
-- (`List XMLDoc`, `_++_`):
--
--   renderFlow   Flow → Forest        a monoid homomorphism (`renderFlow-++`): each block
--                                     contributes its markup (`renderBlock`);
--   renderSlide  Slide → Forest       the chunks of a slide (`Slides.Deck.Syntax`): the first is
--                                     shown, each later one is a fragment, one per tick
--                                     (`render-events`: the same list from the scene's events);
--   renderTalk   Shell → Talk → Forest  a monoid homomorphism in the talk (`renderTalk-++`).
--
-- The backends differ only in a `Shell`, how a slide and a vertical stack are wrapped, and in the
-- page around the forest.  A `Shell` is the whole interface a backend gives the core, so
-- everything proved here is proved for both.  Restyling is a homomorphism of backends:
-- `restyle f sh` applies `f` to the markup of every wrapped part and
-- `renderTalk (restyle f sh) t ≡ map f (renderTalk sh t)` (`restyle-hom`), and likewise on the
-- blocks of a flow (`restyleFlow-hom`).
--
--   pause-free   a body without pauses has one chunk and renders as its flow (`render-single`)
--   render-glue  a pause-free body in front of another renders as its flow followed by the
--                other's slide: the HTML reading of `chunks-++` (legacy `renderBody-bind`)
--
-- Speaker notes and scripts are not part of the slide's visible content, so they are never
-- inside a fragment (a fragment would hide them with its chunk).

module Slides.Backend.Render where

open import Data.Bool.Base using (Bool; true; false; not)
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

open import Data.Empty using (⊥)
open import Slides.Scalar.Model.Nat using (natSpace; natMon; natSub)
open import Slides.Diagram.Print using (natPrint; renderSVG)
import Slides.Diagram.Layout natSpace as DL
open import Slides.Deck.Math using (toLaTeX)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Deck.Read using (index; ol; fragment-index)
import Slides.Scene.Events {ℕ} {⊥} natMon natSub as E
open import Slides.Backend.HTML

Forest : Set
Forest = List XMLDoc

------------------------------------------------------------------------
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
  piece (codeSpan s)   = inj₂ (hText "code" [] s) ∷ []
  piece (link u is)    = inj₂ (rich "a" (("href" , u) ∷ []) is) ∷ []
  piece (cite k)       = inj₂ (hText "span" (("class" , "cite") ∷ []) ("[" ++ˢ k ++ˢ "]")) ∷ []

  -- an element whose content is running text
  rich : String → Attrs → List Inline → XMLDoc
  rich tag attrs is = hMixed tag attrs (normalise (pieces is))

------------------------------------------------------------------------
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

fragmentClass : Maybe String → String
fragmentClass nothing  = "fragment"
fragmentClass (just s) = "fragment " ++ˢ s

private
  div : String → List XMLDoc → XMLDoc
  div cls = hElement "div" (("class" , cls) ∷ [])

  pct : String → ℕ → String
  pct name n = name ++ˢ ":" ++ˢ show n ++ˢ "%;"

  bullet : Bool → Text → XMLDoc
  bullet true  t = rich "li" (("class" , "fragment") ∷ []) t
  bullet false t = rich "li" [] t

  row : String → List Text → XMLDoc
  row cell cs = hElement "tr" [] (map (rich cell []) cs)


mutual
  renderBlock : Block → Forest
  renderBlock (heading n t)    = rich (hTag n) [] t ∷ []
  renderBlock (paragraph t)    = rich "p" [] t ∷ []
  renderBlock (bullets inc ts) = hElement "ul" [] (map (bullet inc) ts) ∷ []
  renderBlock (code lang src)  =
    hElement "pre" [] (hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ []) ∷ []
  renderBlock (displayMath m)  = hText "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ toLaTeX m ++ˢ " \\]") ∷ []
  renderBlock (figure src cap) =
    hElement "figure" []
      ( hElement "img" (("src" , src) ∷ ("alt" , plainT cap) ∷ []) []
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

renderFlow-++ : ∀ xs ys → renderFlow (xs ++ ys) ≡ renderFlow xs ++ renderFlow ys
renderFlow-++ []       ys = refl
renderFlow-++ (b ∷ xs) ys = trans (cong (renderBlock b ++_) (renderFlow-++ xs ys)) (sym (ListP.++-assoc (renderBlock b) _ _))

------------------------------------------------------------------------
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

render-single : ∀ c → renderChunks (c ∷ []) ≡ renderFlow c
render-single c = ListP.++-identityʳ (renderFlow c)

-- the HTML reading of `chunks-++`: a pause-free body in front of another
glue-single : ∀ c ys → renderChunks (glue (c ∷ []) ys) ≡ renderFlow c ++ renderChunks ys
glue-single c (d ∷ ds) =
  trans (cong (_++ concatMap renderStep ds) (renderFlow-++ c d)) (ListP.++-assoc (renderFlow c) (renderFlow d) _)

render-glue : ∀ a b c → chunks a ≡ c ∷ [] → renderChunks (chunks (a ++ b)) ≡ renderFlow c ++ renderChunks (chunks b)
render-glue a b c e rewrite chunks-++ a b | e = glue-single c (chunks b)

-- the same list from the scene's events: the chunk starting at tick `k` is `index` of the
-- events of the slide (`Slides.Deck.Read.fragment-index`)
stepOf : ℕ × Flow → Forest
stepOf (zero  , f) = renderFlow f
stepOf (suc _ , f) = renderStep f

renderIdx : List (ℕ × Flow) → Forest
renderIdx = concatMap stepOf

private
  shifted : ∀ xs → renderIdx (map (λ x → suc (proj₁ x) , proj₂ x) xs) ≡ concatMap (λ x → renderStep (proj₂ x)) xs
  shifted []       = refl
  shifted (x ∷ xs) = cong (renderStep (proj₂ x) ++_) (shifted xs)

  cm-shift : ∀ xs → concatMap (λ x → renderStep (proj₂ x)) (map (λ x → suc (proj₁ x) , proj₂ x) xs)
                    ≡ concatMap (λ x → renderStep (proj₂ x)) xs
  cm-shift []       = refl
  cm-shift (x ∷ xs) = cong (renderStep (proj₂ x) ++_) (cm-shift xs)

  flows : ∀ c cs → concatMap (λ x → renderStep (proj₂ x)) (index c cs) ≡ renderStep c ++ concatMap renderStep cs
  flows c []       = refl
  flows c (d ∷ ds) = cong (renderStep c ++_) (trans (cm-shift (index d ds)) (flows d ds))

render-index : ∀ c cs → renderIdx (index c cs) ≡ renderChunks (c ∷ cs)
render-index c []       = refl
render-index c (d ∷ ds) = cong (renderFlow c ++_) (trans (shifted (index d ds)) (flows d ds))

-- so the HTML of a slide is a function of the events of its scene: slide, tick, content
render-events : ∀ c cs → renderIdx (map ol (E.events (chunkFrom c cs))) ≡ renderChunks (c ∷ cs)
render-events c cs = trans (cong renderIdx (fragment-index c cs)) (render-index c cs)

------------------------------------------------------------------------
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

-- a monoid homomorphism: a talk is rendered part by part
renderTalk-++ : ∀ sh xs ys → renderTalk sh (xs ++ ys) ≡ renderTalk sh xs ++ renderTalk sh ys
renderTalk-++ sh = ListP.concatMap-++ (renderPart sh)

-- the slides inside a part are rendered the same by every backend: only the wrapping differs
renderPart-solo : ∀ sh o s → renderPart sh (solo o s) ≡ Shell.wrapSlide sh (lookAttrs o (Slide.label s)) (renderSlide s)
renderPart-solo sh o s = refl

------------------------------------------------------------------------
-- Restyling is a homomorphism of backends

restyle : (XMLDoc → XMLDoc) → Shell → Shell
restyle f sh = record
  { wrapSlide = λ a x → map f (Shell.wrapSlide sh a x)
  ; wrapStack = λ a xs → map f (Shell.wrapStack sh a xs) }

restyle-hom : ∀ f sh t → renderTalk (restyle f sh) t ≡ map f (renderTalk sh t)
restyle-hom f sh []       = refl
restyle-hom f sh (p ∷ ps) =
  trans (cong₂ _++_ (restyle-part p) (restyle-hom f sh ps)) (sym (ListP.map-++ f (renderPart sh p) (renderTalk sh ps)))
  where
    restyle-part : ∀ p → renderPart (restyle f sh) p ≡ map f (renderPart sh p)
    restyle-part (solo _ _)          = refl
    restyle-part (vstack _ (_ ∷ _)) = refl

-- the same on the blocks of a flow: `f` applied to the markup of each block
restyleFlow : (XMLDoc → XMLDoc) → Flow → Forest
restyleFlow f = concatMap (λ b → map f (renderBlock b))

restyleFlow-hom : ∀ f bs → restyleFlow f bs ≡ map f (concatMap renderBlock bs)
restyleFlow-hom f []       = refl
restyleFlow-hom f (b ∷ bs) = trans (cong (map f (renderBlock b) ++_) (restyleFlow-hom f bs)) (sym (ListP.map-++ f (renderBlock b) _))
