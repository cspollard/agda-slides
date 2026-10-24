{-# OPTIONS --safe --without-K #-}

-- The vocabulary mapping shared by the HTML backends.
--
-- A backend is an algebra for each level of the vocabulary
-- (`Container.Interpret`).  The algebras for content, layout and (their sum)
-- slide bodies have the same carrier, a forest of XML documents
-- (`List XMLDoc` with pointwise `_≈ₓ_`): each command contributes its markup
-- and then the rest of the program.  The reveal.js and plain HTML backends
-- differ only in how slides are wrapped and in the page around them.

module Slides.Backend.Common where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Container.FreeMonad as FM
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)

open import Categories.Functor.Algebra using (F-Algebra)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (_≈ₓ_; XMLSetoid)
open import Data.XML.Print using (renderXML)
open import Data.JSON.AST using (JSON; objectFromList; trueⱼ; boolⱼ; stringⱼ)
open import Data.JSON.Print using (renderJSON)

open import Container.Polynomial using (Poly; Poly₀)
open import Container.Sum using (copair)
open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Core
open import Slides.Math using (toLaTeX)
open import Slides.Backend.HTML
open import Slides.Backend.Diagram using (renderDiagram)

------------------------------------------------------------------------
-- The carrier

Forest : Set
Forest = List XMLDoc

ForestSetoid : Setoid 0ℓ 0ℓ
ForestSetoid = PW.setoid XMLSetoid

-- The unit setoid: the leaves (`pure tt`) of programs.
⊤ˢ : Setoid 0ℓ 0ℓ
⊤ˢ = record
  { Carrier       = ⊤
  ; _≈_           = λ _ _ → ⊤
  ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  }

private
  forest-refl : ∀ (xs : Forest) → Setoid._≈_ ForestSetoid xs xs
  forest-refl xs = Setoid.refl ForestSetoid {xs}

-- A program ends by contributing no output.
nil : Func ⊤ˢ ForestSetoid
nil = record { to = λ _ → [] ; cong = λ _ → PW.[] }

------------------------------------------------------------------------
-- Inline markup

private
  Piece : Set
  Piece = String ⊎ XMLDoc

  -- Merge adjacent text into the text slots of mixed content.
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

  -- An element whose content is running text.
  rich : String → Attrs → List Inline → XMLDoc
  rich tag attrs is = hMixed tag attrs (normalise (pieces is))

------------------------------------------------------------------------
-- Rendering the commands of a slide

section : Attrs → List XMLDoc → XMLDoc
section attrs = hElement "section" attrs

-- Heading levels 1–6; anything outside is clamped.
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

bullet : Bool → Text → XMLDoc
bullet true  t = rich "li" (("class" , "fragment") ∷ []) t
bullet false t = rich "li" [] t

renderContent : ContentShape → Forest
renderContent (heading n t)       = rich (hTag n) [] t ∷ []
renderContent (paragraph t)       = rich "p" [] t ∷ []
renderContent (bullets inc ts)    = hElement "ul" [] (map (bullet inc) ts) ∷ []
renderContent (code lang src)     =
  hElement "pre" []
    ( hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ [] )
  ∷ []
renderContent (displayMath t)     = hText "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ toLaTeX t ++ˢ " \\]") ∷ []
renderContent (figure src cap)    =
  hElement "figure" []
    ( hElement "img" (("src" , src) ∷ ("alt" , plain cap) ∷ []) []
    ∷ rich "figcaption" [] cap
    ∷ [] )
  ∷ []
  where
    -- the alt text is the caption's plain text
    plain : Text → String
    plain []                 = ""
    plain (text s ∷ is)      = s ++ˢ plain is
    plain (inlineMath m ∷ is) = toLaTeX m ++ˢ plain is
    plain (codeSpan s ∷ is)  = s ++ˢ plain is
    plain (cite k ∷ is)      = "[" ++ˢ k ++ˢ "]" ++ˢ plain is
    plain (_ ∷ is)           = plain is
renderContent (notes t)           = rich "aside" (("class" , "notes") ∷ []) t ∷ []
renderContent (table header rows) =
  hElement "table" []
    ( hElement "thead" [] (row "th" header ∷ [])
    ∷ hElement "tbody" [] (map (row "td") rows)
    ∷ [] )
  ∷ []
  where
    row : String → List Text → XMLDoc
    row cell cs = hElement "tr" [] (map (rich cell []) cs)
renderContent (references refs)   =
  hElement "ol" (("class" , "references") ∷ [])
    (map (λ { (k , t) → rich "li" (("id" , "ref-" ++ˢ k) ∷ []) t }) refs)
  ∷ []

module A = Alg 0ℓ 0ℓ ContentC
module L = Alg 0ℓ 0ℓ LayoutC
module B = Alg 0ℓ 0ℓ BlockC

-- The content algebra: a command contributes its markup, then the rest.
contentα : Func (Poly₀ ContentC ForestSetoid) ForestSetoid
contentα = record
  { to   = λ { (c , k) → renderContent c ++ k tt }
  ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → PW.++⁺ (forest-refl _) (k≈ tt) }
  }

contentAlg : F-Algebra A.F
contentAlg = record { A = ForestSetoid ; α = contentα }

renderContentProgram : Content → Forest
renderContentProgram = A.fold contentAlg {⊤ˢ} nil

-- The layout algebra.
renderLayout : LayoutShape → Forest
renderLayout (columns cs) =
  hElement "div" (("class" , "columns") ∷ [])
    (map (λ c → hElement "div" (("class" , "column") ∷ []) (renderContentProgram c)) cs)
  ∷ []
renderLayout (box t c) =
  hElement "div" (("class" , "box") ∷ [])
    (rich "div" (("class" , "box-title") ∷ []) t ∷ renderContentProgram c)
  ∷ []

renderLayout (fragment style c) =
  hElement "div" (("class" , cls style) ∷ []) (renderContentProgram c) ∷ []
  where
    cls : Maybe String → String
    cls nothing  = "fragment"
    cls (just s) = "fragment " ++ˢ s

renderLayout (placed x y w h c) =
  hElement "div"
    ( ("class" , "placed")
    ∷ ("style" , pct "left" x ++ˢ pct "top" y ++ˢ pct "width" w ++ˢ pct "height" h)
    ∷ [])
    (renderContentProgram c)
  ∷ []
  where
    -- percentages of the slide; the stylesheets position the box with
    -- `position: fixed`, whose containing block is the slide canvas
    pct : String → ℕ → String
    pct name n = name ++ˢ ":" ++ˢ show n ++ˢ "%;"
renderLayout (diagram d) = renderDiagram d ∷ []

renderLayout pause = []
renderLayout (stepped style l) =
  hElement "div" (("class" , cls style) ∷ []) (renderLayout l) ∷ []
  where
    cls : Maybe String → String
    cls nothing  = "fragment"
    cls (just s) = "fragment " ++ˢ s

layoutα : Func (Poly₀ LayoutC ForestSetoid) ForestSetoid
layoutα = record
  { to   = λ { (c , k) → renderLayout c ++ k tt }
  ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → PW.++⁺ (forest-refl _) (k≈ tt) }
  }

layoutAlg : F-Algebra L.F
layoutAlg = record { A = ForestSetoid ; α = layoutα }

-- The algebra for slide bodies is the copairing of the two.
blockAlg : F-Algebra B.F
blockAlg = record { A = ForestSetoid ; α = copair ContentC LayoutC ForestSetoid contentα layoutα }

renderBody : Body → Forest
renderBody = B.fold blockAlg {⊤ˢ} nil

-- Slide options become `data-*` attributes.
slideAttrs : SlideOptions → Attrs
slideAttrs o = opt "data-background-color" (SlideOptions.background o)
            ++ opt "data-transition" (SlideOptions.transition o)
  where
    opt : String → Maybe String → Attrs
    opt k nothing  = []
    opt k (just v) = (k , v) ∷ []


------------------------------------------------------------------------
-- Structural properties

-- Rendering is a monoid homomorphism: sequencing programs concatenates the
-- markup.  (The fold of a program is the markup of its first command followed
-- by the fold of the rest, and the leaf contributes nothing.)
renderBody-bind : ∀ (b₁ b₂ : Body) →
                  renderBody (b₁ FM.>>= λ _ → b₂) ≡ renderBody b₁ ++ renderBody b₂
renderBody-bind (pure tt)             b₂ = refl
renderBody-bind (impure (inj₁ c , k)) b₂ =
  trans (cong (renderContent c ++_) (renderBody-bind (k tt) b₂))
        (sym (++-assoc (renderContent c) (renderBody (k tt)) (renderBody b₂)))
renderBody-bind (impure (inj₂ c , k)) b₂ =
  trans (cong (renderLayout c ++_) (renderBody-bind (k tt) b₂))
        (sym (++-assoc (renderLayout c) (renderBody (k tt)) (renderBody b₂)))
