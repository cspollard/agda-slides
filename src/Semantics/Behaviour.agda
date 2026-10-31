{-# OPTIONS --safe --without-K #-}

-- Behaviours: what an interactive thing does, with no syntax.
--
--   Moore C O   the endofunctor X ↦ O × (C → X) on setoids: an output, and a next state per command
--   Beh C O     behaviours `List C → O` (pointwise equality), the terminal coalgebra of `Moore C O`
--   final       that statement (`Terminal (F-Coalgebras (Moore C O))`); `obs` is the unique map from
--               any machine, `obs-unique` its uniqueness, `obs-id` the map out of the behaviours
--   mapO        functor in the output; for an `O` that is a model of a theory, the operations
--               applied pointwise make `Beh C O` the power model, so every law of `O` holds
--   reindex     contravariant in the words: any `List C′ → List C` precomposes
--   const, hd   the constant behaviours: section and retraction (`hd∘const`)
--
-- The synchronous product of `Slides.Program.Sem` is the pointwise (power) operation; `await` is
-- not pointwise, it inspects the word.

module Semantics.Behaviour where

open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
open import Categories.Category.Construction.F-Coalgebras using (F-Coalgebras)
open import Categories.Object.Terminal using (Terminal; IsTerminal)

S₀ = Setoids 0ℓ 0ℓ

-- functions from a set, pointwise
_⇉_ : Set → Setoid 0ℓ 0ℓ → Setoid 0ℓ 0ℓ
C ⇉ X = record { Carrier = C → X.Carrier ; _≈_ = λ f g → ∀ c → f c X.≈ g c
               ; isEquivalence = record { refl = λ _ → X.refl ; sym = λ e c → X.sym (e c)
                                        ; trans = λ e e′ c → X.trans (e c) (e′ c) } }
  where module X = Setoid X

module _ (C : Set) (O : Setoid 0ℓ 0ℓ) where
  private module O = Setoid O

  -- X ↦ O × (C → X)
  Moore : Endofunctor S₀
  Moore = record
    { F₀ = λ X → ×-setoid O (C ⇉ X)
    ; F₁ = λ f → record { to = λ { (o , k) → o , λ c → f ⟨$⟩ k c }
                        ; cong = λ { (e , e′) → e , λ c → Func.cong f (e′ c) } }
    ; identity     = λ {X} → O.refl , λ c → Setoid.refl X
    ; homomorphism = λ {_} {_} {Z} → O.refl , λ c → Setoid.refl Z
    ; F-resp-≈     = λ e → O.refl , λ c → e }

  Beh : Setoid 0ℓ 0ℓ
  Beh = List C ⇉ O

  behCoalg : F-Coalgebra Moore
  behCoalg = record
    { A = Beh
    ; α = record { to = λ f → f [] , λ c cs → f (c ∷ cs)
                 ; cong = λ e → e [] , λ c cs → e (c ∷ cs) } }

  module _ (M : F-Coalgebra Moore) where
    open F-Coalgebra M renaming (A to X)
    private module X = Setoid X
    out : X.Carrier → O.Carrier
    out x = proj₁ (α ⟨$⟩ x)
    nxt : X.Carrier → C → X.Carrier
    nxt x = proj₂ (α ⟨$⟩ x)

    obs : X.Carrier → List C → O.Carrier
    obs x []       = out x
    obs x (c ∷ cs) = obs (nxt x c) cs

    obs-cong : ∀ {x y} → x X.≈ y → ∀ cs → obs x cs O.≈ obs y cs
    obs-cong e []       = proj₁ (Func.cong α e)
    obs-cong e (c ∷ cs) = obs-cong (proj₂ (Func.cong α e) c) cs

    obsF : Func X Beh
    obsF = record { to = obs ; cong = obs-cong }

    obs-hom : F-Coalgebra-Morphism M behCoalg
    obs-hom = record { f = obsF ; commutes = λ {x} → O.refl , λ c cs → O.refl }

    obs-unique : (h : F-Coalgebra-Morphism M behCoalg) →
                 Category._≈_ (F-Coalgebras Moore) obs-hom h
    obs-unique h {x} = go x
      where
        open F-Coalgebra-Morphism h renaming (f to g)
        go : ∀ x cs → obs x cs O.≈ (g ⟨$⟩ x) cs
        go x []       = O.sym (proj₁ (commutes {x}))
        go x (c ∷ cs) = O.trans (go (nxt x c) cs) (O.sym (proj₂ (commutes {x}) c cs))

  -- the behaviours, read as a machine, observe as themselves
  obs-id : ∀ f cs → obs behCoalg f cs O.≈ f cs
  obs-id f []       = O.refl
  obs-id f (c ∷ cs) = obs-id (λ cs′ → f (c ∷ cs′)) cs

  -- behaviours are the final Moore machine
  final : Terminal (F-Coalgebras Moore)
  final = record
    { ⊤ = behCoalg
    ; ⊤-is-terminal = record { ! = λ {M} → obs-hom M ; !-unique = λ {M} h → obs-unique M h } }

-- outputs: a functor (postcompose); inputs: any map of words reindexes (precompose)
mapO : ∀ {C} {O O′ : Setoid 0ℓ 0ℓ} → Func O O′ → Func (Beh C O) (Beh C O′)
mapO f = record { to = λ b cs → f ⟨$⟩ b cs ; cong = λ e cs → Func.cong f (e cs) }

reindex : ∀ {C C′} {O : Setoid 0ℓ 0ℓ} → (List C′ → List C) → Func (Beh C O) (Beh C′ O)
reindex r = record { to = λ b cs → b (r cs) ; cong = λ e cs → e (r cs) }

-- the constant behaviours: a split mono (section `const`, retraction `hd`, "read before any command")
const : ∀ {C} {O : Setoid 0ℓ 0ℓ} → Func O (Beh C O)
const = record { to = λ o _ → o ; cong = λ e _ → e }

hd : ∀ {C} {O : Setoid 0ℓ 0ℓ} → Func (Beh C O) O
hd = record { to = λ b → b [] ; cong = λ e → e [] }

-- `hd` after `const` is the identity: a constant behaviour reads as its constant
hd∘const : ∀ {C} {O : Setoid 0ℓ 0ℓ} →
           Category._≈_ S₀ (Category._∘_ S₀ (hd {C} {O}) const) (Category.id S₀)
hd∘const {O = O} = Setoid.refl O
