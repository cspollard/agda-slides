{-# OPTIONS --safe --without-K #-}

-- Decks: a scene of scenes over content leaves.
--
--   Body        what an author writes for a slide: blocks and `pause`s (the free monoid)
--   chunks b    the blocks between pauses; chunk i appears at tick i
--   slideScene  `chunk 0 ∥ delay 1 (chunk 1 ∥ delay 1 (...))`, held for `1 + pauses` ticks
--   Deck        a scene whose leaves are slides in sequence: a scene of scenes
--   flat        the deck as one scene over `Flow`: substitution of each slide's scene, `_>>=_`
--
--   `length-chunks`  a body has `1 + pauses` chunks, one tick each
--   `chunks-++`      chunks (xs ++ ys) ≡ glue (chunks xs) (chunks ys): the last chunk of xs
--                    joins the first of ys, so a pause in one body affects the next

module Slides.Deck.Syntax where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
import Data.List.NonEmpty as L⁺
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; suc)
open import Data.String.Base using (String)
open import Data.Container.FreeMonad using (pure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; isEquivalence)
import Data.List.Properties as ListP
open import Level using (0ℓ)
open import Data.Product.Base using (_,′_)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MagmaMorphisms; module MonoidMorphisms)

open import Slides.Scene.Syntax
open import Slides.Deck.Content

data Item : Set where
  block : Block → Item
  pause : Item

Body : Set
Body = List Item

addBlock : Block → List⁺ Flow → List⁺ Flow
addBlock b (c ∷ cs) = (b ∷ c) ∷ cs

chunks : Body → List⁺ Flow
chunks []              = [] ∷ []
chunks (block b ∷ xs)  = addBlock b (chunks xs)
chunks (pause ∷ xs)    = [] ∷ toList (chunks xs)

pauses : Body → ℕ
pauses []              = 0
pauses (block _ ∷ xs)  = pauses xs
pauses (pause ∷ xs)    = suc (pauses xs)

length-chunks : ∀ b → L⁺.length (chunks b) ≡ suc (pauses b)
length-chunks []             = refl
length-chunks (block _ ∷ xs) with chunks xs | length-chunks xs
... | c ∷ cs | e = e
length-chunks (pause ∷ xs)   = cong suc (length-chunks xs)

-- the chunks of a concatenation: the last chunk of the first body joins the first of the second
glueL : Flow → List Flow → List⁺ Flow → List⁺ Flow
glueL c []       (d ∷ ds) = (c ++ d) ∷ ds
glueL c (e ∷ es) ys       = c ∷ toList (glueL e es ys)

glue : List⁺ Flow → List⁺ Flow → List⁺ Flow
glue (c ∷ cs) = glueL c cs

glue-nil : ∀ ys → glue ([] ∷ []) ys ≡ ys
glue-nil (d ∷ ds) = refl

private
  addBlock-glue : ∀ b xs ys → addBlock b (glue xs ys) ≡ glue (addBlock b xs) ys
  addBlock-glue b (c ∷ [])     (d ∷ ds) = refl
  addBlock-glue b (c ∷ e ∷ es) ys       = refl

chunks-++ : ∀ xs ys → chunks (xs ++ ys) ≡ glue (chunks xs) (chunks ys)
chunks-++ []             ys = sym (glue-nil (chunks ys))
chunks-++ (block b ∷ xs) ys = trans (cong (addBlock b) (chunks-++ xs ys)) (addBlock-glue b (chunks xs) (chunks ys))
chunks-++ (pause ∷ xs)   ys with chunks xs | chunks (xs ++ ys) | chunks-++ xs ys
... | c ∷ cs | _ | refl = refl

-- `glue` is a monoid on `List⁺ Flow`, unit a single empty chunk
private
  consHead : Flow → List⁺ Flow → List⁺ Flow
  consHead c (d ∷ ds) = (c ++ d) ∷ ds

  glueL-++ : ∀ c d ds ys → glueL (c ++ d) ds ys ≡ consHead c (glueL d ds ys)
  glueL-++ c d []       (e ∷ es) = cong (_∷ es) (ListP.++-assoc c d e)
  glueL-++ c d (_ ∷ ds) ys       = refl

  glueL-assoc : ∀ c cs ys zs → glue (glueL c cs ys) zs ≡ glueL c cs (glue ys zs)
  glueL-assoc c []       (d ∷ ds) zs = glueL-++ c d ds zs
  glueL-assoc c (e ∷ es) ys       zs = cong (λ r → c ∷ toList r) (glueL-assoc e es ys zs)

  glueL-unitʳ : ∀ c cs → glueL c cs ([] ∷ []) ≡ c ∷ cs
  glueL-unitʳ c []       = cong (_∷ []) (ListP.++-identityʳ c)
  glueL-unitʳ c (e ∷ es) = cong (λ r → c ∷ toList r) (glueL-unitʳ e es)

glue-assoc : ∀ xs ys zs → glue (glue xs ys) zs ≡ glue xs (glue ys zs)
glue-assoc (c ∷ cs) = glueL-assoc c cs

glue-unitʳ : ∀ xs → glue xs ([] ∷ []) ≡ xs
glue-unitʳ (c ∷ cs) = glueL-unitʳ c cs

glueMonoid : Monoid 0ℓ 0ℓ
glueMonoid = record
  { Carrier  = List⁺ Flow
  ; _≈_      = _≡_
  ; _∙_      = glue
  ; ε        = [] ∷ []
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ glue }
          ; assoc   = glue-assoc }
      ; identity = glue-nil ,′ glue-unitʳ }
  }

-- ... and `chunks` is a monoid homomorphism from bodies under concatenation
module _ where
  open MonoidMorphisms (Monoid.rawMonoid (ListP.++-monoid Item)) (Monoid.rawMonoid glueMonoid)
  open MagmaMorphisms (Monoid.rawMagma (ListP.++-monoid Item)) (Monoid.rawMagma glueMonoid)

  chunks-isMonoidHomomorphism : IsMonoidHomomorphism chunks
  chunks-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = cong chunks }
        ; homo = chunks-++ }
    ; ε-homo = refl }

-- Scenes

record Slide : Set where
  constructor slide
  field
    label  : Maybe String
    chunkL : List⁺ Flow

mkSlide : Maybe String → Body → Slide
mkSlide l b = slide l (chunks b)

-- the number of ticks (states) of a slide
ticks : Slide → ℕ
ticks s = L⁺.length (Slide.chunkL s)

-- chunk i from tick i
chunkFrom : Flow → List Flow → Scene ℕ ⊥ Flow
chunkFrom c []       = pure c
chunkFrom c (d ∷ ds) = pure c ∥ delay 1 (chunkFrom d ds)

chunkScene : List⁺ Flow → Scene ℕ ⊥ Flow
chunkScene (c ∷ cs) = chunkFrom c cs

slideScene : Slide → Scene ℕ ⊥ Flow
slideScene s = hold (ticks s) (chunkScene (Slide.chunkL s))

Deck : Set
Deck = Scene ℕ ⊥ Slide

-- slides in sequence
deckFrom : Slide → List Slide → Deck
deckFrom s []       = pure s
deckFrom s (t ∷ ts) = pure s ⨾ deckFrom t ts

deckOf : List⁺ Slide → Deck
deckOf (s ∷ ss) = deckFrom s ss

flat : Deck → Scene ℕ ⊥ Flow
flat d = d >>= slideScene
