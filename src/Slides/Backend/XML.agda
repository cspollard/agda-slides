{-# OPTIONS --safe --without-K #-}

-- Bridge between the generic container development and parsnip's XML.
--
-- parsnip's XML AST is the free monad over the container `XMLC`
-- (`XMLDoc = XMLC ⋆ ⊥`) with `Setoid 0ℓ 0ℓ` equality `XMLSetoid`, so the
-- `Container.*` machinery applies directly: `Poly XMLC` is an endofunctor on
-- `Setoids 0ℓ 0ℓ`, and XML-producing backends are algebras of slide
-- containers whose carrier is built from `XMLSetoid`.

module Slides.Backend.XML where

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Endofunctor)

open import Data.XML.AST using (XMLC; XMLDoc)
open import Data.XML.Equality using (XMLSetoid)
open import Data.XML.Print using (printXML)
open import Data.XML.RoundTrip using (xmlStage)

open import Container.Polynomial using (Poly)
open import Container.FreeMonad using (Free₀)

XMLEndo : Endofunctor (Setoids 0ℓ 0ℓ)
XMLEndo = Poly XMLC

-- Trees of XML nodes with leaves in `X`.
XMLTrees : Setoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ
XMLTrees = Free₀ XMLC
