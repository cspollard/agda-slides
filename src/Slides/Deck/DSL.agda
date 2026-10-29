{-# OPTIONS --safe --without-K #-}

-- The authoring vocabulary: smart constructors, `do`-notation and components for talks.
--
--   demo : Talk
--   demo = do
--     slide (do heading 1 "Title"
--               paragraph ("some " ∷ emph "marked up" ∷ " text" ∷ [])
--               pause
--               bullets ("and" ∷ "more" ∷ []))
--
-- A `Body` is the content of one slide: blocks and `pause`s, the free monoid on them
-- (`Slides.Deck.Syntax`); a `Flow` is nested content (columns, boxes); a `Talk` is a list of
-- parts.  All three are lists, so one `_>>_`, list append, sequences each of them and `do` needs
-- no instances.  Associativity and the unit are `Data.List.Properties`; the pause convention
-- across `_>>_` is `chunks-++`.  The commands of a `Flow` are in the `Content` submodule.
--
-- A component is an ordinary function into `Body` or `Talk` (`titled`, `twoColumn`, ...).
-- `Checked R` gives `figure` and `cite` against a declared `Resources`: the check is an implicit
-- argument that is the unit type when the name is declared (solved by eta) and an empty type
-- naming the missing resource when not, an unsolved meta (no instance search).

module Slides.Deck.DSL where

open import Data.Bool.Base using (true; false; Bool; T)
open import Data.Bool.ListAction using (any)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; proj₁)
open import Data.String using (String; _==_)
open import Data.Unit.Base using (⊤)

open import Slides.Deck.Literals public
open import Slides.Deck.Math using (Math)
open import Slides.Deck.Content hiding (cite; plain; heading; paragraph; bullets; code; displayMath; figure; notes; table;
                                       references; diagram; script; mount; columns; box; fragment; classed; placed)
open import Slides.Deck.Content using (Inline; Text; Flow; Block; text; codeSpan; emph; strong; inlineMath; link) public
import Slides.Deck.Content as C
open import Slides.Deck.Syntax using (Item; Body; block; mkSlide)
open import Slides.Deck.Syntax using (Body) public
open import Data.Unit using (tt) public
import Slides.Deck.Syntax as S
open import Slides.Deck.Talk
open import Slides.Diagram.Syntax using (Dia)
open import Slides.Deck.Anim using (Anim; bothScene; uniform?; rests)

------------------------------------------------------------------------
-- `do`-notation

infixl 1 _>>_
_>>_ : ∀ {A : Set} → List A → List A → List A
_>>_ = _++_

plain : String → Text
plain s = text s ∷ []

-- a check that is the unit type when it holds and an empty type naming the culprit when not
data Missing (kind name : String) : Set where

Found : Bool → String → String → Set
Found true  _    _    = ⊤
Found false kind name = Missing kind name

------------------------------------------------------------------------
-- Commands, stated once: as a `Flow` (`Content`, for columns and boxes) and as a `Body`

module Prims (X : Set) (one : Block → X) where

  heading : ℕ → Text → X
  heading n t = one (C.heading n t)
  paragraph : Text → X
  paragraph t = one (C.paragraph t)
  bullets incremental : List Text → X
  bullets xs = one (C.bullets false xs)
  incremental xs = one (C.bullets true xs)
  code : (language source : String) → X
  code l s = one (C.code l s)
  displayMath : Math → X
  displayMath m = one (C.displayMath m)
  figureUnchecked : String → Text → X
  figureUnchecked s c = one (C.figure s nothing c)
  -- … at a width, in percent of the slide's content width
  figureWidthUnchecked : String → ℕ → Text → X
  figureWidthUnchecked s w c = one (C.figure s (just w) c)
  notes : Text → X
  notes t = one (C.notes t)
  table : List Text → List (List Text) → X
  table h r = one (C.table h r)
  references : List (String × Text) → X
  references rs = one (C.references rs)
  diagram : String → ℕ → Dia ℕ → X
  diagram n p d = one (C.diagram n p d)
  animate : String → ℕ → ℕ → List Anim → X
  animate n p ms as = one (C.animation n p ms as)
  animateLoop : String → ℕ → ℕ → Anim → X
  animateLoop n p ms a = one (C.animationLoop n p ms a)
  -- `animateBoth name percent ms period acts`: the acts of `animate` (one per reveal step) over
  -- a loop of `period` phases; `acts φ` are the acts at phase φ, of equal lengths in every phase
  animateBoth : (n : String) (p ms period : ℕ) (acts : ℕ → List Anim) →
                {ok : Found (uniform? period acts) "equal-length phases" n} → X
  animateBoth n p ms k as = one (C.animationBoth n p ms k (bothScene k as) (rests (as 0)))
  script mount : String → X
  script js = one (C.script js)
  mount i = one (C.mount i)
  columns : List Flow → X
  columns cs = one (C.columns cs)
  box : Text → Flow → X
  box t f = one (C.box t f)
  fragment : Flow → X
  fragment f = one (C.fragment nothing f)
  fragmentWith : String → Flow → X
  fragmentWith s f = one (C.fragment (just s) f)
  classed : String → Flow → X
  classed c f = one (C.classed c f)
  placed : ℕ → ℕ → ℕ → ℕ → Flow → X
  placed x y w h f = one (C.placed x y w h f)

module Content = Prims Flow (_∷ [])

-- the same commands as slide bodies (`references` is a per-deck resource instead)
liftContent : Flow → Body
liftContent = map block

open Prims Body (λ b → block b ∷ []) public hiding (references)

-- everything from here on in the body appears step by step
pause : Body
pause = S.pause ∷ []

------------------------------------------------------------------------
-- Slides

background transition : String → Look
background c = look (just c) nothing nothing
transition t = look nothing (just t) nothing

labelled : String → Look → Look
labelled l (look b t _) = look b t (just l)

slideWith : Look → Body → Talk
slideWith o b = solo o (mkSlide (Look.label o) b) ∷ []

slide : Body → Talk
slide = slideWith plainLook

slideAs : String → Body → Talk
slideAs l = slideWith (labelled l plainLook)

-- a vertical stack; the label of the look is the first slide's
stackWith : Look → Body → List Body → Talk
stackWith o b bs = vstack o (mkSlide (Look.label o) b ∷ map (mkSlide nothing) bs) ∷ []

stack : Body → List Body → Talk
stack = stackWith plainLook

------------------------------------------------------------------------
-- Components

titled : Text → Body → Body
titled t b = heading 2 t >> b

withNotes : Text → Body → Body
withNotes n b = b >> notes n

titleBody : (title subtitle author : Text) → Body
titleBody t s a = heading 1 t >> paragraph s >> paragraph a

bulletBody incrementalBody : Text → List Text → Body
bulletBody t xs = titled t (bullets xs)
incrementalBody t xs = titled t (incremental xs)

twoColumn : Text → Flow → Flow → Body
twoColumn t l r = titled t (columns (l ∷ r ∷ []))

resultsTable : Text → List Text → List (List Text) → Body
resultsTable t h rows = titled t (table h rows)

sectionSlide : Text → Talk
sectionSlide t = slideWith (background "#1b1b2f") (heading 1 t)

titleSlide : (title subtitle author : Text) → Talk
titleSlide t s a = slide (titleBody t s a)

------------------------------------------------------------------------
-- Resources a talk refers to, checked when it typechecks

record Resources : Set where
  field
    figures    : List String                  -- image files the talk may include
    references : List (String × Text)         -- bibliography: key and entry

open Resources public

module Checked (R : Resources) where
  private declared = λ (x : String) (xs : List String) → any (x ==_) xs

  figure : (src : String) {ok : Found (declared src (figures R)) "figure" src} → Text → Body
  figure src c = figureUnchecked src c

  -- … at a width, in percent of the slide's content width: `figureWidth "plot.png" 60 "caption"`
  figureWidth : (src : String) {ok : Found (declared src (figures R)) "figure" src} → ℕ → Text → Body
  figureWidth src w c = figureWidthUnchecked src w c

  bibliography : Body
  bibliography = liftContent (Content.references (references R))

  cite : (key : String) {ok : Found (declared key (map proj₁ (references R))) "reference" key} → Inline
  cite key = C.cite key
