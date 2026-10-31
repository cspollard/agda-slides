{-# OPTIONS --safe --without-K #-}

-- Laws of the shared deck algebra (`Slides.Backend.Render`), proved once for both backends.
--   `renderFlow-++`, `renderTalk-++`   rendering is a monoid homomorphism
--   `render-single`  a pause-free body is one chunk and renders as its flow
--   `render-glue`    the HTML reading of `chunks-++`
--   `render-events`  a slide's HTML is a function of the events of its scene: the chunk
--                    after the first is a fragment (`Slides.Deck.Read.fragment-index`)
--   `render-fragments`  the elements with class `fragment` in a slide's page are the model's steps
--                    (`Slides.Deck.Steps.chunkSteps`), given the count inside blocks (`BlockLaw`)
--   `restyle-hom`, `restyleFlow-hom`   restyling is a homomorphism of backends

module Slides.Backend.Render.Properties where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Data.XML.AST using (XMLDoc; foldXMLM; node; Attributes; parentList; mixed)
open import Data.Maybe.Base using (nothing)
import Data.Container.Table as Tbl
open import Data.Container.Pos using (Pos)
open import Data.Container.List using (tabulate; length-tabulate; tabulate-map; tabulate-table; listToListC)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Data.Char.Base using (Char; isSpace)
import Data.Char.Properties as Char
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List.Base using (zip; length; wordsByᵇ)
open import Data.Nat.ListAction using (sum)
open import Data.String.Base using (toList)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function.Base using (_∘_)
import Data.Nat.Properties as ℕP
import Data.Nat.Base as ℕ
import Slides.Deck.Steps as St
open import Data.Empty using (⊥-elim)
open import Data.Bool.Base using (true; false; not)
open import Data.List.Base using (filterᵇ)

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Deck.Content
open import Slides.Deck.Steps using (gap)
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Deck.Read using (index; ol; fragment-index)
open import Slides.Deck.Clock using (module E)
open import Slides.Backend.Render
open import Slides.Backend.HTML using (div)
open import Data.XML.Sanitize using (fixAttrs; fixName)

renderFlow-++ : ∀ xs ys → renderFlow (xs ++ ys) ≡ renderFlow xs ++ renderFlow ys
renderFlow-++ []       ys = refl
renderFlow-++ (b ∷ xs) ys = trans (cong (renderBlock b ++_) (renderFlow-++ xs ys)) (sym (ListP.++-assoc (renderBlock b) _ _))

render-single : ∀ c → renderChunks (c ∷ []) ≡ renderFlow c
render-single c = ListP.++-identityʳ (renderFlow c)

glue-single : ∀ c ys → renderChunks (glue (c ∷ []) ys) ≡ renderFlow c ++ renderChunks ys
glue-single c (d ∷ ds) =
  trans (cong (_++ concatMap renderStep ds) (renderFlow-++ c d)) (ListP.++-assoc (renderFlow c) (renderFlow d) _)

render-glue : ∀ a b c → chunks a ≡ c ∷ [] → renderChunks (chunks (a ++ b)) ≡ renderFlow c ++ renderChunks (chunks b)
render-glue a b c e =
  trans (cong renderChunks (trans (chunks-++ a b) (cong (λ x → glue x (chunks b)) e))) (glue-single c (chunks b))

-- the same list from the scene's events: the first chunk of a slide is shown, each later one is a
-- fragment (`Slides.Deck.Read.fragment-index`).  The onsets are the steps at which the chunks appear
-- (`gap`), but the markup does not depend on them: a chunk can start at tick 0 and still be a fragment.
renderIdx : List (ℕ × Flow) → Forest
renderIdx []             = []
renderIdx ((_ , c) ∷ es) = renderFlow c ++ concatMap (λ x → renderStep (proj₂ x)) es

private
  -- shifting the onsets leaves the markup alone
  cm-shift : ∀ k xs → concatMap (λ x → renderStep (proj₂ x)) (map (λ x → k + proj₁ x , proj₂ x) xs)
                      ≡ concatMap (λ x → renderStep (proj₂ x)) xs
  cm-shift k []       = refl
  cm-shift k (x ∷ xs) = cong (renderStep (proj₂ x) ++_) (cm-shift k xs)

  flows : ∀ c cs → concatMap (λ x → renderStep (proj₂ x)) (index c cs) ≡ renderStep c ++ concatMap renderStep cs
  flows c []       = refl
  flows c (d ∷ ds) = cong (renderStep c ++_) (trans (cm-shift (gap c d) (index d ds)) (flows d ds))

render-index : ∀ c cs → renderIdx (index c cs) ≡ renderChunks (c ∷ cs)
render-index c []       = refl
render-index c (d ∷ ds) = cong (renderFlow c ++_) (trans (cm-shift (gap c d) (index d ds)) (flows d ds))

-- so the HTML of a slide is a function of the events of its scene: slide, tick, content
render-events : ∀ c cs → renderIdx (map ol (E.events (chunkFrom c cs))) ≡ renderChunks (c ∷ cs)
render-events c cs = trans (cong renderIdx (fragment-index c cs)) (render-index c cs)

-- a monoid homomorphism: a talk is rendered part by part
renderTalk-++ : ∀ sh xs ys → renderTalk sh (xs ++ ys) ≡ renderTalk sh xs ++ renderTalk sh ys
renderTalk-++ sh = ListP.concatMap-++ (renderPart sh)

-- the slides inside a part are rendered the same by every backend: only the wrapping differs
renderPart-solo : ∀ sh o s → renderPart sh (solo o s) ≡ Shell.wrapSlide sh (lookAttrs o (Slide.label s)) (renderSlide s)
renderPart-solo sh o s = refl

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

-- Counting fragments on the markup
--
-- The pages step through every element whose class has the token `fragment`.  `fragCount` counts
-- them as a fold of the XML tree (`foldXMLM`): an element counts for its own class, then its children.

classKey fragTok : List Char → Bool
classKey k = ⌊ ListP.≡-dec Char._≟_ k (toList "class") ⌋
fragTok  w = ⌊ ListP.≡-dec Char._≟_ w (toList "fragment") ⌋

-- 1 when the class attribute has `fragment` among its tokens
classHit : Attributes → ℕ
classHit []             = 0
classHit ((k , v) ∷ as) = if classKey k then (if any fragTok (wordsByᵇ isSpace v) then 1 else 0) else classHit as

fragCount : XMLDoc → ℕ
fragCount = foldXMLM (λ ()) (λ _ attrs cs → classHit attrs + sum (map proj₁ (proj₂ cs)))

forestCount : Forest → ℕ
forestCount = sum ∘ map fragCount

forestCount-++ : ∀ xs ys → forestCount (xs ++ ys) ≡ forestCount xs + forestCount ys
forestCount-++ []       ys = refl
forestCount-++ (x ∷ xs) ys = trans (cong (fragCount x +_) (forestCount-++ xs ys)) (sym (ℕP.+-assoc (fragCount x) _ _))

-- the sum over the children of a node: `zip` stops at the text slots, which are as many
private
  zip-sum : ∀ (L : List ℕ) {T : List (List Char)} → length L ≡ length T → sum (map proj₁ (zip L T)) ≡ sum L
  zip-sum []       {[]}    e = refl
  zip-sum (x ∷ L)  {_ ∷ T} e = cong (x +_) (zip-sum L (ℕP.suc-injective e))

  -- the children of a node, listed in order, with the text slots dropped
  mixed-sum : ∀ n (texts : Vec (List Char) (suc n)) (f : Pos n → ℕ) → sum (map proj₁ (proj₂ (mixed n texts f))) ≡ sum (tabulate n f)
  mixed-sum n texts f = zip-sum (tabulate n f) (trans (length-tabulate n f) (sym (VecP.length-toList (Vec.tail texts))))

  -- an element with element children counts for its own class and theirs
  parent-count : ∀ tag attrs (cs : List XMLDoc) {pt pa} → fragCount (parentList tag attrs cs {pt} {pa}) ≡ classHit attrs + forestCount cs
  parent-count tag attrs cs =
    trans (cong (classHit attrs +_) (mixed-sum (length cs) (Vec.replicate (suc (length cs)) []) (fragCount ∘ Tbl.table cs)))
          (cong (classHit attrs +_) (cong sum (trans (tabulate-map (length cs) (Tbl.table cs) fragCount) (cong (map fragCount) (tabulate-table cs)))))

-- the wrapper `div.fragment` counts for itself and what it holds
div-fragment : ∀ kids → forestCount (div "fragment" kids ∷ []) ≡ suc (forestCount kids)
div-fragment []         = refl
div-fragment (k ∷ kids) = trans (ℕP.+-identityʳ _) (parent-count (fixName (toList "div")) attrs (k ∷ kids))
  where attrs = fixAttrs ((toList "class" , toList "fragment") ∷ [])

-- Chunks: a later chunk is a fragment when it shows something, and holds the fragments of its blocks
--
-- `Slides.Deck.Steps.aside?` is the test `renderStep` applies, restated to avoid a cycle
aside?-agree : ∀ b → St.aside? b ≡ aside? b
aside?-agree (notes _)  = refl
aside?-agree (script _) = refl
aside?-agree (heading _ _) = refl
aside?-agree (paragraph _) = refl
aside?-agree (bulletTree _ _) = refl
aside?-agree (code _ _) = refl
aside?-agree (displayMath _) = refl
aside?-agree (figure _ _ _) = refl
aside?-agree (table _ _) = refl
aside?-agree (references _) = refl
aside?-agree (diagram _ _ _) = refl
aside?-agree (animation _ _ _ _) = refl
aside?-agree (animationLoop _ _ _ _) = refl
aside?-agree (animationBoth _ _ _ _ _ _) = refl
aside?-agree (still _ _ _) = refl
aside?-agree (mount _) = refl
aside?-agree (columns _) = refl
aside?-agree (box _ _) = refl
aside?-agree (fragment _ _) = refl
aside?-agree (classed _ _) = refl
aside?-agree (placed _ _ _ _ _) = refl

nonempty : Flow → ℕ
nonempty []      = 0
nonempty (_ ∷ _) = 1

-- what is shown and what is aside
shown asides : Flow → Flow
shown  = filterᵇ (λ b → not (aside? b))
asides = filterᵇ aside?

t≢f : ∀ {A : Set} → true ≡ false → A
t≢f ()

wraps-shown : ∀ f → St.wraps f ≡ nonempty (shown f)
wraps-shown []       = refl
wraps-shown (b ∷ bs) with St.aside? b in e₁ | aside? b in e₂
... | true  | true  = wraps-shown bs
... | false | false = refl
... | true  | false = t≢f (trans (sym e₁) (trans (aside?-agree b) e₂))
... | false | true  = t≢f (trans (sym e₂) (trans (sym (aside?-agree b)) e₁))

swap : ∀ x y z → x + (y + z) ≡ y + (x + z)
swap x y z = trans (sym (ℕP.+-assoc x y z)) (trans (cong (_+ z) (ℕP.+-comm x y)) (ℕP.+-assoc y x z))

-- the two parts hold the fragments of the whole
split-count : ∀ f → forestCount (renderFlow (shown f)) + forestCount (renderFlow (asides f)) ≡ forestCount (renderFlow f)
split-count []       = refl
split-count (b ∷ bs) with aside? b
... | true  = trans (cong (forestCount (renderFlow (shown bs)) +_) (forestCount-++ (renderBlock b) (renderFlow (asides bs))))
                    (trans (swap (forestCount (renderFlow (shown bs))) (forestCount (renderBlock b)) (forestCount (renderFlow (asides bs))))
                           (trans (cong (forestCount (renderBlock b) +_) (split-count bs)) (sym (forestCount-++ (renderBlock b) (renderFlow bs)))))
... | false = trans (cong (_+ forestCount (renderFlow (asides bs))) (forestCount-++ (renderBlock b) (renderFlow (shown bs))))
                    (trans (ℕP.+-assoc (forestCount (renderBlock b)) (forestCount (renderFlow (shown bs))) (forestCount (renderFlow (asides bs))))
                           (trans (cong (forestCount (renderBlock b) +_) (split-count bs)) (sym (forestCount-++ (renderBlock b) (renderFlow bs)))))

step-count : ∀ f → forestCount (renderStep f) ≡ St.wraps f + forestCount (renderFlow f)
step-count f with shown f | wraps-shown f | split-count f
... | []        | w | sp = trans sp (sym (cong (_+ forestCount (renderFlow f)) w))
... | v ∷ vs    | w | sp =
  trans (forestCount-++ (div "fragment" (renderFlow (v ∷ vs)) ∷ []) (renderFlow (asides f)))
        (trans (cong (_+ forestCount (renderFlow (asides f))) (div-fragment (renderFlow (v ∷ vs))))
               (trans (cong suc sp) (sym (cong (_+ forestCount (renderFlow f)) w))))

-- The slide.  What the renderer does at the level of chunks is proved; the count inside a block is
-- the `BlockLaw`, which the cases below prove for the blocks whose markup is known
-- (the rest are blocked on inline text, SVG and class strings, which are arbitrary).
BlockLaw : Set
BlockLaw = ∀ b → forestCount (renderBlock b) ≡ St.blockSteps b

flow-count : BlockLaw → ∀ f → forestCount (renderFlow f) ≡ St.flowSteps f
flow-count L []       = refl
flow-count L (b ∷ bs) = trans (forestCount-++ (renderBlock b) (renderFlow bs)) (cong₂ _+_ (L b) (flow-count L bs))

later-count : BlockLaw → ∀ cs → forestCount (concatMap renderStep cs) ≡ St.laterSteps cs
later-count L []       = refl
later-count L (d ∷ ds) =
  trans (forestCount-++ (renderStep d) (concatMap renderStep ds))
        (cong₂ _+_ (trans (step-count d) (cong (St.wraps d +_) (flow-count L d))) (later-count L ds))

-- the fragments of the page are the steps of the model
render-fragments : BlockLaw → ∀ s → forestCount (renderSlide s) ≡ St.chunkSteps (Slide.chunkL s)
render-fragments L (slide _ (c ∷ cs)) =
  trans (forestCount-++ (renderFlow c) (concatMap renderStep cs)) (cong₂ _+_ (flow-count L c) (later-count L cs))

-- so a slide has one state for the first chunk and one per fragment of its page
ticks-fragments : BlockLaw → ∀ s → ticks s ≡ suc (forestCount (renderSlide s))
ticks-fragments L s = sym (cong suc (render-fragments L s))

-- blocks whose count is known outright
fragment-count : ∀ f → forestCount (renderBlock (fragment nothing f)) ≡ suc (forestCount (renderFlow f))
fragment-count f = div-fragment (renderFlow f)

mount-count : ∀ i → forestCount (renderBlock (mount i)) ≡ 0
mount-count i = refl

script-count : ∀ js → forestCount (renderBlock (script js)) ≡ 0
script-count js = refl
