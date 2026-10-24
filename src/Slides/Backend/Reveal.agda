{-# OPTIONS --safe --without-K #-}

-- The reveal.js backend.
--
-- A backend is an algebra for each level of the vocabulary
-- (`Container.Interpret`).  Both algebras here have the same carrier, a
-- forest of XML documents (`List XMLDoc` with pointwise `_≈ₓ_`): the content
-- algebra renders the commands of a slide, and the deck algebra wraps the
-- rendered content of each slide in a `<section>`.  Rendering a deck is
-- the unique fold out of the free algebra.
--
-- The page is printed with parsnip's `renderXML`, which has the proved round
-- trip `parse (print x) ≈ₓ x`; the options for `Reveal.initialize` are a
-- JSON value printed with parsnip's JSON printer.

module Slides.Backend.Reveal where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)

open import Categories.Functor.Algebra using (F-Algebra)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (_≈ₓ_; XMLSetoid)
open import Data.XML.Print using (renderXML)
open import Data.JSON.AST using (JSON; objectFromList; trueⱼ; stringⱼ)
open import Data.JSON.Print using (renderJSON)

open import Container.Polynomial using (Poly)
open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Core
open import Slides.Backend.HTML

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
-- Rendering the commands of a slide

section : List XMLDoc → XMLDoc
section = hElement "section" []

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

bullet : Bool → String → XMLDoc
bullet true  t = hText "li" (("class" , "fragment") ∷ []) t
bullet false t = hText "li" [] t

renderContent : ContentShape → Forest
renderContent (heading n t)       = hText (hTag n) [] t ∷ []
renderContent (paragraph t)       = hText "p" [] t ∷ []
renderContent (bullets inc ts)    = hElement "ul" [] (map (bullet inc) ts) ∷ []
renderContent (code lang src)     =
  hElement "pre" []
    ( hText "code" (("class" , "language-" ++ˢ lang) ∷ ("data-trim" , "") ∷ []) src ∷ [] )
  ∷ []
renderContent (displayMath t)     = hText "div" (("class" , "math") ∷ []) ("\\[ " ++ˢ t ++ˢ " \\]") ∷ []
renderContent (figure src cap)    =
  hElement "figure" []
    ( hElement "img" (("src" , src) ∷ ("alt" , cap) ∷ []) []
    ∷ hText "figcaption" [] cap
    ∷ [] )
  ∷ []
renderContent (notes t)           = hText "aside" (("class" , "notes") ∷ []) t ∷ []

module A = Alg 0ℓ 0ℓ ContentC
module D = Alg 0ℓ 0ℓ DeckC

-- The content algebra: a command contributes its markup, then the rest.
contentAlg : F-Algebra A.F
contentAlg = record
  { A = ForestSetoid
  ; α = record
      { to   = λ { (c , k) → renderContent c ++ k tt }
      ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) →
                   PW.++⁺ (forest-refl _) (k≈ tt) }
      }
  }

renderBody : Body → Forest
renderBody = A.fold contentAlg {⊤ˢ} nil

-- The deck algebra: each slide is a `<section>`; a stack is a `<section>`
-- of `<section>`s.
deckAlg : F-Algebra D.F
deckAlg = record
  { A = ForestSetoid
  ; α = record
      { to   = λ { (slide b , k)  → section (renderBody b) ∷ k tt
                 ; (stack bs , k) → section (map (section ∘ renderBody) bs) ∷ k tt }
      ; cong = λ { {slide _ , _} {slide _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt
                 ; {stack _ , _} {stack _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt }
      }
  }

renderDeck : Deck → Forest
renderDeck = D.fold deckAlg {⊤ˢ} nil

------------------------------------------------------------------------
-- The page

record RevealConfig : Set where
  field
    title      : String
    -- URL or path of the reveal.js distribution, with a trailing slash
    base       : String
    theme      : String
    transition : String

defaultConfig : RevealConfig
defaultConfig = record
  { title      = "Slides"
  ; base       = "reveal/"
  ; theme      = "black"
  ; transition = "slide"
  }

private
  script : String → XMLDoc
  script src = hText "script" (("src" , src) ∷ []) " "

  stylesheet : String → XMLDoc
  stylesheet href = hElement "link" (("rel" , "stylesheet") ∷ ("href" , href) ∷ []) []

  div : String → List XMLDoc → XMLDoc
  div cls = hElement "div" (("class" , cls) ∷ [])

page : RevealConfig → Forest → XMLDoc
page cfg slides =
  hElement "html" (("lang" , "en") ∷ [])
    ( hElement "head" []
        ( hElement "meta" (("charset" , "utf-8") ∷ []) []
        ∷ hText "title" [] title
        ∷ stylesheet (dist ++ˢ "reset.css")
        ∷ stylesheet (dist ++ˢ "reveal.css")
        ∷ stylesheet (dist ++ˢ "theme/" ++ˢ theme ++ˢ ".css")
        ∷ stylesheet (dist ++ˢ "plugin/highlight/monokai.css")
        ∷ [] )
    ∷ hElement "body" []
        ( div "reveal" (div "slides" slides ∷ [])
        ∷ script (dist ++ˢ "reveal.js")
        ∷ script (dist ++ˢ "plugin/notes.js")
        ∷ script (dist ++ˢ "plugin/highlight.js")
        ∷ script (dist ++ˢ "plugin/math.js")
        ∷ script "init.js"
        ∷ [] )
    ∷ [] )
  where
    open RevealConfig cfg
    dist = base ++ˢ "dist/"

-- The options for `Reveal.initialize`, as JSON.
options : RevealConfig → JSON
options cfg = objectFromList
  ( ("hash" , trueⱼ)
  ∷ ("transition" , stringⱼ (RevealConfig.transition cfg))
  ∷ [] )

-- `init.js`: the options plus the plugins (which are JavaScript values, not
-- JSON).
initScript : RevealConfig → String
initScript cfg =
  "Reveal.initialize(Object.assign(" ++ˢ renderJSON (options cfg) ++ˢ
  ", {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));\n"

-- `index.html`, with the (unverified, constant) doctype prefix.
renderReveal : RevealConfig → Deck → String
renderReveal cfg d = doctype ++ˢ renderXML (page cfg (renderDeck d))

------------------------------------------------------------------------
-- Structural properties of the rendering

-- The number of slide commands (slides and stacks) in a deck.
count : Deck → ℕ
count (pure _)         = 0
count (impure (_ , k)) = suc (count (k tt))

-- One top-level `<section>` per slide command, in order.
renderDeck-length : ∀ d → length (renderDeck d) ≡ count d
renderDeck-length (pure tt)                = refl
renderDeck-length (impure (slide _ , k))   = cong suc (renderDeck-length (k tt))
renderDeck-length (impure (stack _ , k))   = cong suc (renderDeck-length (k tt))
