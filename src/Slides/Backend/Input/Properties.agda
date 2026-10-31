{-# OPTIONS --safe --without-K #-}

-- Laws of the backends' bindings (`Slides.Backend.Input`).
--   `linear-clash-free`, `stacked-clash-free`, `plain-clash-free`   no key is in two kinds (`refl`)
--   `reveal-total`, `plain-total`   every `Nav` command has a binding
--   `presents`   a backend binding all of `Nav` skips nothing: presenting a program leaves it
--                unchanged (`lower-supported` of `Slides.Program.Supports`)

module Slides.Backend.Input.Properties where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Level using (lift)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (Σ-syntax; _,_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Container.Lowering using (_≈⋆_)

open import Slides.Deck.Talk using (linear; stacked)
open import Slides.Program.Navigation using (Nav)
open import Slides.Program.Supports using (Supports)
open import Slides.Program.Syntax using (Program)
import Slides.Program.Supports as Sup
open import Slides.Backend.Input
open import Slides.Program.Navigation using (_≟N_)
open import Slides.Program.Supports using (idSupports)
open import Data.Sum.Base using (inj₁; inj₂)

-- reveal binds all of `Nav`: the program commands are embedded, nothing is skipped
revealSupports : Supports Nav
revealSupports = record
  { S = RCmd ; _≟S_ = _≟R_
  ; inj = λ n → just (nav n)
  ; dec = λ { (nav n) → just n ; (aux _) → nothing }
  ; dec-inj = λ { refl → refl }
  ; inj-dec = λ { {s = nav _} refl → refl ; {s = aux _} () } }

plainSupports : Supports Nav
plainSupports = idSupports _≟N_

linear-clash-free : clash-free (revealKinds linear) ≡ true
linear-clash-free = refl

stacked-clash-free : clash-free (revealKinds stacked) ≡ true
stacked-clash-free = refl

plain-clash-free : clash-free plainKinds ≡ true
plain-clash-free = refl

-- Every deck is presented unchanged

-- a backend that binds every command of `Nav` skips nothing
module _ {T D : Set} (b : Supports Nav) (tot : ∀ n → Σ[ s ∈ Supports.S b ] Supports.inj b n ≡ just s) where
  private
    no-nothing : ∀ {A : Set} {x : Maybe A} {s} → x ≡ just s → x ≡ nothing → ⊥
    no-nothing refl ()

  allSup : ∀ {A} (p : Program T D Nav A) → Sup.AllSup b p
  allSup (pure _)              = lift tt
  allSup (impure (inj₁ _ , k)) = tt , λ q → allSup (k q)
  allSup (impure (inj₂ c , k)) = no-nothing (proj₂ (tot c)) , λ q → allSup (k q)

  -- presenting a program on `b` leaves it unchanged
  presents : ∀ {A} (p : Program T D Nav A) → Sup.skipU b p ≈⋆ p
  presents p = Sup.lower-supported b p (allSup p)

reveal-total : ∀ n → Σ[ s ∈ RCmd ] Supports.inj revealSupports n ≡ just s
reveal-total n = nav n , refl

plain-total : ∀ n → Σ[ s ∈ Nav ] Supports.inj plainSupports n ≡ just s
plain-total n = n , refl

-- Hashes are written as the page reads them (`revealHash`, `plainHash`)

_ : showHash (flat 3) ≡ "#3"
_ = refl
_ : showHash (grid 8 1) ≡ "#/8/1"
_ = refl
_ : showHash (named "intro") ≡ "#/intro"
_ = refl
