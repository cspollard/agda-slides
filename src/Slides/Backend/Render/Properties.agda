{-# OPTIONS --safe --without-K #-}

-- Laws of the shared deck algebra (`Slides.Backend.Render`), proved once for both backends.
--   `renderFlow-++`, `renderTalk-++`   rendering is a monoid homomorphism
--   `render-single`  a pause-free body is one chunk and renders as its flow
--   `render-glue`    the HTML reading of `chunks-++`
--   `render-events`  a slide's HTML is a function of the events of its scene: the chunk
--                    after the first is a fragment (`Slides.Deck.Read.fragment-index`)
--   `render-fragments`  the elements with class `fragment` in a slide's page are the model's steps
--                    (`Slides.Deck.Steps.chunkSteps`), given `saneSlide`: the class strings of the deck
--                    (`Slides.Backend.Render.Sane`); the count inside blocks is `block-count`
--   `restyle-hom`, `restyleFlow-hom`   restyling is a homomorphism of backends

module Slides.Backend.Render.Properties where

open import Data.Bool.Base using (true; false; not; T)
open import Data.XML.AST using (XMLDoc)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; filterᵇ)
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.List.Properties as ListP
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

import Slides.Deck.Steps as St

open import Slides.Deck.Content
open import Slides.Deck.Steps using (gap; aside?)
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Deck.Read using (index; ol; fragment-index)
open import Slides.Deck.Clock using (module E)
open import Slides.Backend.Render
open import Slides.Backend.Fragments
open import Slides.Backend.Render.Sane
open import Slides.Backend.HTML using (div)

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

-- Counting fragments on the markup: `Slides.Backend.Fragments`

-- the wrapper `div.fragment` counts for itself and what it holds
div-fragment : ∀ kids → forestCount (div "fragment" kids ∷ []) ≡ suc (forestCount kids)
div-fragment kids = trans (ℕP.+-identityʳ _) (hElement-count "div" (("class" , "fragment") ∷ []) kids)

-- Chunks: a later chunk is a fragment when it shows something, and holds the fragments of its blocks
--
nonempty : Flow → ℕ
nonempty []      = 0
nonempty (_ ∷ _) = 1

-- what is shown and what is aside
shown asides : Flow → Flow
shown  = filterᵇ (λ b → not (aside? b))
asides = filterᵇ aside?

wraps-shown : ∀ f → St.wraps f ≡ nonempty (shown f)
wraps-shown []       = refl
wraps-shown (b ∷ bs) with aside? b
... | true  = wraps-shown bs
... | false = refl

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

-- The slide.  The count inside a block is `Slides.Backend.Render.Sane.block-count`, given the class
-- strings of the deck (`saneSlide`, decidable by computation).
later-count : ∀ cs → T (saneC cs) → forestCount (concatMap renderStep cs) ≡ St.laterSteps cs
later-count []       _ = refl
later-count (d ∷ ds) h =
  trans (forestCount-++ (renderStep d) (concatMap renderStep ds))
        (cong₂ _+_ (trans (step-count d) (cong (St.wraps d +_) (flow-count d (proj₁ (split h))))) (later-count ds (proj₂ (split h))))

-- the fragments of the page are the steps of the model
render-fragments : ∀ s → T (saneSlide s) → forestCount (renderSlide s) ≡ St.chunkSteps (Slide.chunkL s)
render-fragments (slide _ (c ∷ cs)) h =
  trans (forestCount-++ (renderFlow c) (concatMap renderStep cs))
        (cong₂ _+_ (flow-count c (proj₁ (split h))) (later-count cs (proj₂ (split h))))

-- so a slide has one state for the first chunk and one per fragment of its page
ticks-fragments : ∀ s → T (saneSlide s) → ticks s ≡ suc (forestCount (renderSlide s))
ticks-fragments s h = sym (cong suc (render-fragments s h))
