# Plan: Containers, polynomial functors, and the free monad (Phase 1)

This is the foundation of the project and the first thing to prove. Everything else (slide vocabulary, backends) sits on it. Module names below are verified against agda-categories at commit `c2e7c13e` and Agda 2.7.0.1.

## Goal

Show, inside agda-categories, that

1. a container `C = (S ▷ P)` determines a **polynomial endofunctor** `⟦C⟧ : Setoids c ℓ ⟶ Setoids c ℓ`, `⟦C⟧ X = Σ s. (P s → X)`;
2. container morphisms induce natural transformations between these functors (so `⟦_⟧` is a functor `Containers ⟶ [Setoids, Setoids]`, and is full and faithful on the right notion of container morphism — stretch);
3. the free monad `C ⋆ X` is the **free monad on the endofunctor `⟦C⟧`**: it is the monad part of the adjunction `Free ⊣ Forget` between `F-Algebras ⟦C⟧`-style algebras and `Setoids`; equivalently its Eilenberg–Moore category is `F-Algebras ⟦C⟧` (the category of `⟦C⟧`-algebras);
4. consequently, `C ⋆ X` is the initial algebra of the functor `X + ⟦C⟧(–)` (Lambek), and `fold` is the unique algebra morphism — the formal basis of "every backend is a fold".

## Setting and conventions

- Categories: `Setoids c ℓ` (`Categories.Category.Instance.Setoids`). Morphisms are `Func` with pointwise setoid equality. We use setoids (not plain `Set` with `≡`) because agda-categories is setoid-enriched, and because it avoids needing function extensionality for the equations on continuations.
- Containers: start with the stdlib `Data.Container` (`Container s p`, shapes and positions as plain `Set`s with `≡`), then generalise if needed to *setoid-valued* shapes/positions. Decide in step 1 (see "Open question").
- Options: all modules `--safe --without-K` (the lib file sets this). Keep these proof modules free of FFI.
- Stdlib already has `Data.Container.FreeMonad` (the inductive `_⋆_`, its fold/induction principles, a `RawMonad` instance `monad`, and the equivalence with `μ (C ⋆C X)`; confirm exact names when implementing step 3). Reuse as the *concrete* representation; the new work is the categorical statements about it.

## Steps

### 1. Polynomial functor on Setoids — `Slides.Polynomial`

- `⟦ C ⟧ˢ X`: the setoid on `Σ s. (P s → Carrier X)` with
  `(s , f) ≈ (s′ , f′)` iff `∃ e : s ≡ s′. ∀ p. f p ≈_X f′ (subst P e p)` (equivalently via a `Σ`-setoid of `ΣP`-equivalence from `Data.Container.Relation.Binary.Pointwise`, which already packages exactly this; check `Data.Container.Relation.Binary.Pointwise` first).
- Action on morphisms: `⟦C⟧₁ g (s , f) = (s , g ∘ f)`; show it respects `≈`, preserves identity and composition (`Functor` record fields `identity`, `homomorphism`, `F-resp-≈`).
- Deliverable: `Poly : Container s p → Endofunctor (Setoids c ℓ)` (levels to be made precise; likely `s p ≤ c` or via `Lift`), with all `Functor` fields filled, no holes.
- Sanity checks: `⟦ const A ⟧`, `⟦ id ⟧`, `⟦ C₁ ⊎ C₂ ⟧`, `⟦ C₁ × C₂ ⟧` agree with `Data.Container.Combinator` (prove the natural isomorphisms; these justify the `⊕` we use to compose slide features).

**Open question:** with plain-`Set` shapes the equality on shapes is `≡`, which makes `⟦C⟧` a functor but not the most general polynomial functor on `Setoids` (shape equality could be a setoid itself). Start with `≡` (simple, enough for syntax of a DSL); revisit if we need quotiented shapes (e.g. slides modulo reflow).

### 2. Container morphisms are natural transformations — `Slides.Polynomial.Morphism`

- Reuse `Data.Container.Morphism` (`Container` morphism `(u , f)`: shape map + position map contravariant) and its interpretation.
- Define `⟦ m ⟧ˢ : NaturalTransformation ⟦C₁⟧ ⟦C₂⟧` (agda-categories `Categories.NaturalTransformation`); show `⟦ id ⟧ ≃ id`, `⟦ m ∘ n ⟧ ≃ ⟦m⟧ ∘ ⟦n⟧`.
- Package as a functor `Containers ⟶ Endofunctors Setoids` (`Categories.Category.Instance.Cats`/`Categories.Category.Construction.Functors`). Faithfulness (and fullness, with `≡` shapes this should hold) is a stretch goal.
- Use: backends/rewrites that change the shape of a command but keep its structure (e.g. renaming a command, adding a style argument) are container morphisms; naturality is automatic.

### 3. Free monad as a monad on Setoids — `Slides.FreeMonad`

- Make `C ⋆ X` into a setoid-valued functor `Free C : Endofunctor (Setoids c ℓ)`, with equality the *structural* (tree-wise) pointwise equality (`Data.Container.Relation.Binary.Pointwise` again, folded by recursion; leaves compared with `≈_X`).
- Prove it is a `Monad` (`Categories.Monad`): `η = pure`, `μ = join`; discharge the three monad laws using setoid equality of trees (no funext needed).
- Prove `inn : ⟦C⟧ (Free C X) → Free C X` and `pure : X → Free C X` jointly give a morphism `X + ⟦C⟧(Free C X) → Free C X`, an isomorphism (the `μ (C ⋆C X)` equivalence from the stdlib).

### 4. The algebraic description — `Slides.FreeMonad.Algebraic`

State and prove, in order:

1. **Algebras**: `Alg C = F-Algebras ⟦C⟧` (`Categories.Category.Construction.F-Algebras`), the category of `⟦C⟧`-algebras (a carrier setoid `A` with `⟦C⟧ A ⟶ A`).
2. **Free algebra on `X`**: `(Free C X , inn)` is an `⟦C⟧`-algebra. For `X`, build a `FreeObject` (`Categories.FreeObjects.Free`) of the forgetful functor `U : Alg C → Setoids` on `X` with unit `pure` and `_* = fold` : `(X → A) → (Free C X → A)`. The two defining equations are `*-lift` (fold after `pure` is the given map) and `*-uniq` (any algebra morphism with that restriction equals fold) — the latter is structural induction on `Free C X`.
3. **Adjunction**: assemble the `FreeObject`s into `Free ⊣ U` (`Categories.FreeObjects.Free` provides `FO⇒Functor` and `FO⇒LAdj : FO⇒Functor F ⊣ U` from a family of `FreeObject`s, so no hand-built unit/counit is needed).
4. **Monad agrees**: the monad of this adjunction (`Categories.Adjoint.Monad` or `Categories.Adjoint.Properties`) is isomorphic as a monad to the monad from step 3. This identifies the stdlib free monad with the abstract free monad on the endofunctor `⟦C⟧`.
5. **Eilenberg–Moore comparison** (stretch): the comparison functor `Alg C → EilenbergMoore (Free C)` is an equivalence, i.e. `⟦C⟧`-algebras *are* the algebras of the free monad (`Categories.Category.Construction.EilenbergMoore`, `Categories.Adjoint.Monadic`). That is exactly "a backend is an algebra of the signature".
6. **Initiality**: by (2) at the right choice of `X`, the initial `⟦C⟧`-algebra `μC` exists (`Categories.Object.Initial`, `Categories.Category.Construction.F-Algebras` `Lambek` module gives `⟦C⟧ μC ≅ μC`); relate `μC ≅ Free C ⊥`.

### 5. Slide-facing corollaries — `Slides.Interpret`

- A *backend* is by definition an `⟦C⟧`-algebra on a target setoid `T` (or an `Alg C` object). `interpret : Free C ⊤ → T` is the fold; the theorem in step 4 is the statement that this is the unique homomorphism.
- Derived results we will use later: fusion (`fold alg ∘ ⟦C₁⟧-translation ≈ fold alg′`), i.e. rewriting a deck by a container morphism and then interpreting equals interpreting with the pulled-back algebra (a direct consequence of naturality from step 2 and uniqueness from step 4).

## Exit criteria for Phase 1

- Modules `Slides.Polynomial`, `Slides.Polynomial.Morphism`, `Slides.FreeMonad`, `Slides.FreeMonad.Algebraic`, `Slides.Interpret` typecheck with `--safe --without-K`, no holes, no postulates.
- `make check` passes from a clean checkout.
- Each module begins with a short header comment stating the theorem it proves and which agda-categories/stdlib module it instantiates.

## Order and checkpointing

Work step-by-step with `agda_load_and_goals`, one module at a time, committing after each module typechecks. Steps 1 and 3 are the critical path; step 2 and the stretch parts of step 4 can be deferred without blocking the DSL (Phases 2–3 of `Plan.md` only need steps 1, 3, 4.1–4.3 and 5).
