{-# OPTIONS --safe --without-K #-}

-- Laws of the shared deck algebra (`Slides.Backend.Render`), proved once for both backends.
--
--   renderFlow-++     a monoid homomorphism: the markup of a flow is the markup of its blocks
--   renderTalk-++     the same in the talk: parts are rendered one by one
--   render-single     a body without pauses is one chunk and renders as its flow
--   render-glue       the HTML reading of `chunks-++` (legacy `renderBody-bind`)
--   render-events     the HTML of a slide is a function of the events of its scene: the chunk
--                     that starts at tick `k` is a fragment (`Slides.Deck.Read.fragment-index`)
--   restyle-hom       restyling is a homomorphism of backends (`restyleFlow-hom` on blocks)

module Slides.Backend.Render.Properties where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.NonEmpty using (_∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Data.XML.AST using (XMLDoc)

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Deck.Read using (index; ol; fragment-index)
import Slides.Scene.Events {ℕ} {⊥} natMon natSub as E
open import Slides.Backend.Render

renderFlow-++ : ∀ xs ys → renderFlow (xs ++ ys) ≡ renderFlow xs ++ renderFlow ys
renderFlow-++ []       ys = refl
renderFlow-++ (b ∷ xs) ys = trans (cong (renderBlock b ++_) (renderFlow-++ xs ys)) (sym (ListP.++-assoc (renderBlock b) _ _))

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
