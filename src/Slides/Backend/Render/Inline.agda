{-# OPTIONS --safe --without-K #-}

-- Inline text holds no fragment.
--
-- An inline is a program of the free monad over `InlineC` (`Slides.Text`), rendered by the handler
-- `pieceH` into pieces: running text, and elements (`code`, `br`, `cite`, and a wrapper around the
-- pieces of its sub-runs).  Every element the renderer writes for text has a fixed class (`cite`) or
-- none, so no inline contributes a fragment, whatever its strings: `rich-count`.
-- The induction over the program is `pfold-rel` (`Container.Interpret.Plain`) with the invariant
-- "the pieces count nothing" against the trivial fold.

module Slides.Backend.Render.Inline where

open import Data.List.Base using (List; []; _∷_; _++_; map; concat; concatMap; tabulate)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Container.Core using (Position)
open import Data.String.Base using () renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.XML.AST using (XMLDoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Data.Nat.Properties as ℕP

open import Container.Interpret.Plain using (pfold; pfold-rel)
open import Slides.Text using (Inline; InlineC; textO; codeO; brO; mathO; citeO; wrapO; emphW; strongW; subW; supW; styledW; linkW; fromKids)
open import Slides.Backend.HTML using (hText; hElement; hMixed; Attrs)
open import Slides.Backend.Fragments
open import Slides.Backend.Render using (Piece; normalise; pieceH; pieces; rich; wrapEl)

-- the fragments in the elements of some pieces
pieceCount : List Piece → ℕ
pieceCount []             = 0
pieceCount (inj₁ _ ∷ ps)  = pieceCount ps
pieceCount (inj₂ d ∷ ps)  = fragCount d + pieceCount ps

pieceCount-++ : ∀ xs ys → pieceCount (xs ++ ys) ≡ pieceCount xs + pieceCount ys
pieceCount-++ []             ys = refl
pieceCount-++ (inj₁ _ ∷ xs)  ys = pieceCount-++ xs ys
pieceCount-++ (inj₂ d ∷ xs)  ys = trans (cong (fragCount d +_) (pieceCount-++ xs ys)) (sym (ℕP.+-assoc (fragCount d) _ _))

-- merging text into slots keeps the elements
normalise-count : ∀ ps → forestCount (map proj₁ (proj₂ (normalise ps))) ≡ pieceCount ps
normalise-count []            = refl
normalise-count (inj₁ s ∷ ps) with normalise ps | normalise-count ps
... | t , cs | ih = ih
normalise-count (inj₂ d ∷ ps) with normalise ps | normalise-count ps
... | t , cs | ih = cong (fragCount d +_) ih

private
  concat-zero : ∀ n (k : Fin n → List Piece) → (∀ q → pieceCount (k q) ≡ 0) → pieceCount (fromKids k) ≡ 0
  concat-zero zero    k h = refl
  concat-zero (suc n) k h =
    trans (pieceCount-++ (k zero) (fromKids (λ q → k (suc q))))
          (trans (cong₂ _+_ (h zero) (concat-zero n (λ q → k (suc q)) (λ q → h (suc q)))) refl)

  -- the attributes a wrapper writes carry no class
  wrap-quiet : ∀ w → attrHit (proj₂ (wrapEl w)) ≡ 0
  wrap-quiet emphW       = refl
  wrap-quiet strongW     = refl
  wrap-quiet subW        = refl
  wrap-quiet supW        = refl
  wrap-quiet (styledW s) = refl
  wrap-quiet (linkW u)   = refl

  -- each command of the handler adds no fragment to the pieces of its sub-runs
  hom : ∀ c (k : Position InlineC c → List Piece) (k′ : Position InlineC c → ⊤) → (∀ q → pieceCount (k q) ≡ 0) → pieceCount (pieceH c k) ≡ 0
  hom (_ , textO s)   k k′ h = refl
  hom (_ , codeO s)   k k′ h = trans (ℕP.+-identityʳ _) (hText-count "code" [] s)
  hom (_ , brO)       k k′ h = refl
  hom (_ , mathO m)   k k′ h = refl
  hom (_ , citeO s)   k k′ h = trans (ℕP.+-identityʳ _) (hText-count "span" (("class" , "cite") ∷ []) ("[" ++ˢ s ++ˢ "]"))
  hom (_ , wrapO w n) k k′ h =
    trans (ℕP.+-identityʳ _)
      (trans (hMixed-count (proj₁ (wrapEl w)) (proj₂ (wrapEl w)) (proj₁ (normalise (fromKids k))) (proj₂ (normalise (fromKids k))))
             (trans (cong₂ _+_ (wrap-quiet w) (trans (normalise-count (fromKids k)) (concat-zero n k h))) refl))

-- one inline holds none
inline-count : ∀ i → pieceCount (pfold InlineC pieceH (λ ()) i) ≡ 0
inline-count i =
  pfold-rel {C = InlineC} (λ x _ → pieceCount x ≡ 0) {hB = λ _ _ → tt} hom {X = ⊥} {f = λ ()} {g = λ ()} (λ ()) i

pieces-count : ∀ is → pieceCount (pieces is) ≡ 0
pieces-count []       = refl
pieces-count (i ∷ is) = trans (pieceCount-++ (pfold InlineC pieceH (λ ()) i) (pieces is)) (trans (cong₂ _+_ (inline-count i) (pieces-count is)) refl)

-- so a text element is its own class and nothing else
rich-count : ∀ tag attrs is → fragCount (rich tag attrs is) ≡ attrHit attrs
rich-count tag attrs is =
  trans (hMixed-count tag attrs (proj₁ (normalise (pieces is))) (proj₂ (normalise (pieces is))))
        (trans (cong (attrHit attrs +_) (trans (normalise-count (pieces is)) (pieces-count is))) (ℕP.+-identityʳ _))
