# Plan: Agda Slide DSL on Containers, Free Monads and agda-categories

Goals (from `Goals.md`):
1. A Container/FreeMonad-based DSL for producing high-quality scientific slide decks.
2. Eventually, export to JS-based slides, pure HTML, etc.

This file is the overview and the ordered work list. Detailed plans live beside it:

- `plan/Polynomial.md` — Phase 1 in detail: containers as polynomial functors on `Setoids`, and the algebraic description of the free monad. **This comes first.**

## Core design idea

A slide deck is a *program* in a free monad over a container of slide commands.

- A **container** `C = (Shape ▷ Position)` describes one command: `Shape` is the command with its arguments (e.g. `text "…"`, `figure path`), `Position s` is the type of results handed to the continuation (`⊤` for most layout commands, `Bool`/`Fin n` for branching ones).
- `Free C A` (stdlib `Data.Container.FreeMonad._⋆_`) is the program type; `do`-notation gives the authoring syntax.
- A **backend is an algebra** for the polynomial functor `⟦C⟧` (an object of `F-Algebras ⟦C⟧`); interpretation is the unique fold out of the free algebra. DSL syntax and backends are therefore independent: adding a backend never touches deck sources.

## Categorical architecture (agda-categories)

The container free monad is the *concrete presentation*; agda-categories supplies the structure used to transform and interpret it. Names verified at agda-categories commit `c2e7c13e`.

| Idea | Where in agda-categories |
| --- | --- |
| Containers give polynomial endofunctors on setoids | `Categories.Category.Instance.Setoids`, `Categories.Functor` (new: `Slides.Polynomial`) |
| Container morphisms are natural transformations | `Categories.NaturalTransformation` |
| Backends are algebras; fold is initiality | `Categories.Category.Construction.F-Algebras`, `Categories.Functor.Algebra`, `Categories.Object.Initial` |
| Syntax = free monad = left adjoint | `Categories.FreeObjects.Free`, `Categories.Adjoint`, `Categories.Monad` |
| Backend algebras = Eilenberg–Moore algebras of the free monad | `Categories.Category.Construction.EilenbergMoore`, `Categories.Adjoint.Monadic` |
| Reusable components as Kleisli arrows | `Categories.Category.Construction.Kleisli`, `Categories.Monad.Construction.Kleisli` |
| Layout as monoidal structure | `Categories.Category.Monoidal` |

Guiding rules:
- The categorical layer is **additive**: proofs live in `Slides.Polynomial*`/`Slides.FreeMonad*` modules, interpreters live in `Slides.Backend.*`. A deck must still render while a proof is unfinished.
- Prefer setoid-enriched statements; this avoids function extensionality for equalities on continuations.
- All modules are `--safe --without-K` (set in `agda-slides.agda-lib`). Only the executable `Main` may use FFI/IO and must opt out explicitly.

## Repository layout

```
agda-slides.agda-lib      depends: standard-library, agda-categories; flags --safe --without-K
Makefile                  `make check` typechecks everything under src/
src/Slides.agda           top-level module / public API
src/Slides/Polynomial.agda            (Phase 1)
src/Slides/Polynomial/Morphism.agda   (Phase 1)
src/Slides/FreeMonad.agda             (Phase 1)
src/Slides/FreeMonad/Algebraic.agda   (Phase 1)
src/Slides/Interpret.agda             (Phase 1)
src/Slides/Core.agda, DSL.agda        (Phase 2: slide containers, smart constructors)
src/Slides/Backend/*.agda             (Phases 3–4: HTML, reveal.js)
examples/                             sample decks
plan/                                 this plan and detailed sub-plans
```

`src/Slides/Smoke.agda` only checks that dependencies resolve; delete it when Phase 1 modules import the same things.

## Phases

### Phase 0 — Scaffolding (done)
`.agda-lib`, git repository, `.gitignore`, `Makefile`, README, smoke module that imports stdlib `Data.Container`, `Data.Container.FreeMonad` and the agda-categories modules listed above. Typechecks with Agda 2.7.0.1.

### Phase 1 — Containers, polynomial functors, free monad (see `plan/Polynomial.md`)
1. `⟦C⟧` as an endofunctor on `Setoids`.
2. Container morphisms as natural transformations.
3. `Free C` as a monad on `Setoids`.
4. `Free C ⊣ Forget` from `F-Algebras ⟦C⟧`; the induced monad is the stdlib free monad; Eilenberg–Moore comparison and initial algebra (Lambek).
5. `interpret` as the unique fold; fusion lemma.

Exit: all Phase 1 modules typecheck with no holes/postulates; `make check` passes.

### Phase 2 — Slide vocabulary
One container per concern, combined with container coproduct (`Data.Container.Combinator._⊎_`; its interpretation is proved in Phase 1 step 1):

| Concern | Commands |
| --- | --- |
| Structure | `deck`, `section`, `slide title body` |
| Text | `heading`, `paragraph`, `bullets`, `emph`, `code lang src` |
| Math | `inlineMath`, `displayMath` (LaTeX string first; typed math AST later) |
| Media | `figure path caption`, `table`, `plot` |
| Layout | `columns n`, `box`, `notes` |
| Incremental reveal | `pause` / `step` |
| Citation | `cite key` |

Open design question — nested vs flat slide bodies:
- *Nested*: `slide` carries a sub-program. Nicer authoring; needs a stratified container (outer `SlideC` with bodies in an inner `BodyC`) to keep strict positivity.
- *Flat*: `beginSlide`/`endSlide` commands plus a well-formedness check; easiest to interpret.
Resolve with a proof of equivalence (or adjunction) between the two presentations rather than picking one, using the Phase 1 machinery.

Deliverable: `Slides.DSL` with `slide "Title" do …` syntax and one hand-written deck.

### Phase 3 — HTML backend
- `render` is the fold for an algebra into a small HTML AST, plus a pretty-printer.
- Single self-contained page: one `<section>` per slide, 16:9 CSS, print stylesheet, math via KaTeX.
- `Main.agda` compiled with MAlonzo writes `out/deck.html`.
- Golden tests: render the example decks and diff against checked-in HTML.

### Phase 4 — JS slide backend
- reveal.js as the first target (`pause` → `class="fragment"`, `notes` → `<aside class="notes">`); same fold structure, reusing the HTML AST.
- Option: a minimal custom JS runtime later.

### Phase 5 — Authoring quality
- Theming (`Theme` record passed to backends); reusable components as Kleisli arrows.
- Typecheck-time resource checks (figures, citations) using indexed or proof-carrying commands.
- Plot/figure support (external images, small SVG DSL).

### Phase 6 — Stretch
- Indexed containers/monads for typed slide state.
- Layout as symmetric-monoidal structure, with its laws.
- Backends: Beamer/LaTeX, PDF, Markdown, pptx; watch mode.

## Milestones

1. **M1** — Phase 0 done; Phase 1 steps 1 and 3 (polynomial functor, free monad as `Monad`).
2. **M2** — Phase 1 step 4 (free adjunction, algebraic description) and step 5 (interpret/fusion).
3. **M3** — Phase 2: vocabulary and DSL, one example deck typechecks.
4. **M4** — Phase 3: HTML end to end with golden tests.
5. **M5** — Phase 4 reveal.js; then Phase 5 and 6.

## Risks and mitigations

- **Universe levels** in agda-categories (`Setoids c ℓ` indexing). Fix level conventions in Phase 1 step 1 (e.g. container shapes/positions live in the same level `c` as setoid carriers) and keep them uniform across the project.
- **Strict positivity** of nested slide bodies — stratify containers (Phase 2).
- **Proof effort** — categorical layer is additive; never block rendering on a proof.
- **`--safe` vs FFI** — keep IO in `Main` only.
- **Plain-`Set` vs setoid shapes** — start with `≡` on shapes; revisit only if quotienting becomes necessary.
- **Library drift** — dependencies are registered globally via `~/.config/agda/libraries`; the README records the agda-categories commit and Agda version used (`c2e7c13e`, 2.7.0.1).

## Immediate next steps

1. Commit the scaffold.
2. Implement `Slides.Polynomial` (Phase 1 step 1) with the agda MCP loop; commit when it typechecks.
3. Implement `Slides.FreeMonad` (step 3), then `Slides.FreeMonad.Algebraic` (step 4).
