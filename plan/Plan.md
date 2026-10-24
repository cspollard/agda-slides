# Plan: Agda Slide DSL on Containers, Free Monads and agda-categories

Goals (from `Goals.md`):
1. A Container/FreeMonad-based DSL for producing high-quality scientific slide decks.
2. Eventually, export to JS-based slides, pure HTML, etc.

**Priority:** the reveal.js backend is the first use case and is ranked ahead of plain HTML (Phase 3). Plain HTML follows (Phase 4).

This file is the overview and the ordered work list. Detailed plans live beside it:

- `plan/Polynomial.md` — Phase 1 in detail: containers as polynomial functors on `Setoids`, and the algebraic description of the free monad. **This comes first.**
- `plan/HTML.md` — reveal.js (top priority) and plain HTML production on top of the `parsnip` submodule (verified XML printing/parsing); covers Phases 3–5 export work.

## Core design idea

A slide deck is a *program* in a free monad over a container of slide commands.

- A **container** `C = (Shape ▷ Position)` describes one command: `Shape` is the command with its arguments (e.g. `text "…"`, `figure path`), `Position s` is the type of results handed to the continuation (`⊤` for most layout commands, `Bool`/`Fin n` for branching ones).
- `Free C A` (stdlib `Data.Container.FreeMonad._⋆_`) is the program type; `do`-notation gives the authoring syntax.
- A **backend is an algebra** for the polynomial functor `⟦C⟧` (an object of `F-Algebras ⟦C⟧`); interpretation is the unique fold out of the free algebra. XML/HTML output targets the XML AST of `parsnip`, which is itself a free monad over a container, with a proved print/parse round trip (see `plan/HTML.md`). DSL syntax and backends are therefore independent: adding a backend never touches deck sources.

## Categorical architecture (agda-categories)

The container free monad is the *concrete presentation*; agda-categories supplies the structure used to transform and interpret it. Names verified at agda-categories commit `c2e7c13e`.

| Idea | Where in agda-categories |
| --- | --- |
| Containers give polynomial endofunctors on setoids | `Categories.Category.Instance.Setoids`, `Categories.Functor` (new: `Container.Polynomial`) |
| Container morphisms are natural transformations | `Categories.NaturalTransformation` |
| Backends are algebras; fold is initiality | `Categories.Category.Construction.F-Algebras`, `Categories.Functor.Algebra`, `Categories.Object.Initial` |
| Syntax = free monad = left adjoint | `Categories.FreeObjects.Free`, `Categories.Adjoint`, `Categories.Monad` |
| Backend algebras = Eilenberg–Moore algebras of the free monad | `Categories.Category.Construction.EilenbergMoore`, `Categories.Adjoint.Monadic` |
| Reusable components as Kleisli arrows | `Categories.Category.Construction.Kleisli`, `Categories.Monad.Construction.Kleisli` |
| Layout as monoidal structure | `Categories.Category.Monoidal` |

Guiding rules:
- The categorical layer is **additive**: proofs live in generic `Container.*` modules, interpreters live in `Slides.Backend.*`. A deck must still render while a proof is unfinished.
- Prefer setoid-enriched statements; this avoids function extensionality for equalities on continuations.
- All modules are `--safe --without-K` (set in `agda-slides.agda-lib`). Only the executable `Main` may use FFI/IO and must opt out explicitly.

## Repository layout

```
agda-slides.agda-lib      depends: standard-library, agda-categories; include: src, parsnip/src; flags --safe --without-K
parsnip/                  git submodule: verified XML/JSON/SVG printers and parsers
Makefile                  `make check` typechecks everything under src/
src/Container/Polynomial.agda            (Phase 1) generic: containers as polynomial functors on Setoids
src/Container/Polynomial/Morphism.agda   (Phase 1)
src/Container/FreeMonad.agda             (Phase 1)
src/Container/FreeMonad/Algebraic.agda   (Phase 1)
src/Container/Interpret.agda             (Phase 1) initial algebra, fold/hom, fusion
src/Slides.agda                          slide-specific top-level module / public API
src/Slides/Core.agda, DSL.agda        (Phase 2: slide containers, smart constructors)
src/Slides/Backend/XML.agda           bridge to parsnip's XML (Container machinery at `XMLC`)
src/Slides/Backend/*.agda             (Phase 3: reveal.js, Phase 4: plain HTML)
examples/                             sample decks
plan/                                 this plan and detailed sub-plans
```

The `Container.*` namespace is deliberately independent of slides: nothing under `src/Container/` may import `Slides.*`, so it could be split out as its own library. The scaffold's smoke module has been removed now that the Phase 1 modules import the same dependencies.

## Phases

### Phase 0 — Scaffolding (done)
`.agda-lib`, git repository, `.gitignore`, `Makefile`, README. The `parsnip` submodule is on the include path (`parsnip/src`) and `Slides.Backend.XML` typechecks against it. Typechecks with Agda 2.7.0.1.

### Phase 1 — Containers, polynomial functors, free monad (see `plan/Polynomial.md`) — core done
Status (all modules typecheck with `--safe --without-K`, no holes, no postulates; `make check` passes):
- [x] `Container.Polynomial`: `⟦C⟧` as a functor `Setoids c ℓ ⟶ Setoids (s⊔p⊔c) (s⊔p⊔ℓ)` (endofunctor for `Set 0ℓ` containers).
- [x] `Container.Polynomial.Morphism`: container morphisms as natural transformations; preserves identity and composition.
- [x] `Container.FreeMonad`: `Free C` as a functor and a `Monad` on `Setoids` (structural tree equality, no funext).
- [x] `Container.FreeMonad.Algebraic`: forgetful functor from `F-Algebras ⟦C⟧`, `Free₀ C X` as a `FreeObject`, the adjunction `Free ⊣ Forget`, and the proof that the monad of that adjunction is isomorphic to `Free C` (two `Monad⇒-id` morphisms, mutually inverse).
- [x] `Container.Interpret`: initial algebra and Lambek's lemma, `fold-hom` (folds commute with algebra homomorphisms), `fusion` (translate along a container morphism = interpret with the pulled-back algebra).
- [ ] Deferred (stretch): Eilenberg–Moore comparison `Alg ≃ EilenbergMoore (Free C)`; faithfulness/fullness of `Poly-⇒`; natural isomorphisms between `⟦·⟧` and the `Data.Container.Combinator` operations (`⊎`, `×`, `const`, `id`) — needed before Phase 2 relies on `⊎` to compose slide features.

### Phase 2 — Slide vocabulary (minimal subset first)
Build only what the reveal.js backend needs first (`slide`, vertical `section`, `heading`, `paragraph`, `bullets`, `pause`, `notes`, `code`, math, `figure`, `columns`, backgrounds) and grow from there. One container per concern, combined with container coproduct (`Data.Container.Combinator._⊎_`; its interpretation is proved in Phase 1 step 1):

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

### Phase 3 — reveal.js backend (top priority; see `plan/HTML.md`)
- The reveal.js backend is an `⟦SlideC⟧`-algebra with a carrier built from parsnip's `XMLSetoid`; `render` is `fold` (`Container.Interpret`), printed with parsnip's `printXML` (proved round trip `parse (print x) ≈ₓ x`). Configuration is a JSON value printed by parsnip's JSON printer into `init.js`.
- Documents are well-formed by construction; runtime strings go through `Data.XML.Sanitize`.
- Work items R0–R4 in `plan/HTML.md`, in order: **R0 spike first** (a hand-built deck printed by parsnip and opened in a browser, to settle self-closing tags, doctype, and inline script/style), then HTML5 gap policy, carrier and bridge lemmas, the algebra, and the driver with golden and parse-back tests.
- Mapping: `slide` → `<section>`, vertical `section` → nested `<section>`, `pause` → `class="fragment"`, `notes` → `<aside class="notes">`, math via the reveal.js math plugin.

### Phase 4 — Plain standalone HTML backend
- Same XML pipeline and shared vocabulary mapping as Phase 3, with a small built-in navigation script (external file) and print stylesheet (R5 in `plan/HTML.md`). Option: a minimal custom JS runtime later.

### Phase 5 — Authoring quality
- Theming (`Theme` record passed to backends); reusable components as Kleisli arrows.
- Typecheck-time resource checks (figures, citations) using indexed or proof-carrying commands.
- Plot/figure support (external images; inline SVG via parsnip's `Data.SVG`, `plan/HTML.md` H6).

### Phase 6 — Stretch
- Indexed containers/monads for typed slide state.
- Layout as symmetric-monoidal structure, with its laws.
- Backends: Beamer/LaTeX, PDF, Markdown, pptx; watch mode.

## Milestones

1. **M1** — Phase 0 done; Phase 1 steps 1 and 3 (polynomial functor, free monad as `Monad`).
2. **M2** — Phase 1 step 4 (free adjunction, algebraic description) and step 5 (interpret/fusion).
3. **M3** — Phase 2: vocabulary and DSL, one example deck typechecks.
4. **M4** — R0 spike: a hand-built reveal.js deck printed by parsnip runs in a browser (can run in parallel with M1–M3, and should start now).
5. **M5** — Phase 3: reveal.js end to end from a Slides DSL deck, with golden and parse-back tests.
6. **M6** — Phase 4 plain HTML; then Phase 5 and 6.

## Risks and mitigations

- **HTML5 vs XML (blocks the reveal.js backend).** parsnip prints XML (empty elements self-close, text is XML-escaped, no doctype node). The R0 spike and R1 in `plan/HTML.md` decide between padding empty non-void elements, XHTML output, or a custom printer. Do R0 before designing the backend.
- **Submodule dependency.** parsnip is pinned by the submodule commit; builds need `git submodule update --init`. Its flags (`--cubical-compatible`, `-WnoUnsupportedIndexedMatch`) are compatible with our `--safe --without-K`.
- **Universe levels** in agda-categories (`Setoids c ℓ` indexing). Fix level conventions in Phase 1 step 1 (e.g. container shapes/positions live in the same level `c` as setoid carriers) and keep them uniform across the project.
- **Strict positivity** of nested slide bodies — stratify containers (Phase 2).
- **Proof effort** — categorical layer is additive; never block rendering on a proof.
- **`--safe` vs FFI** — keep IO in `Main` only.
- **Plain-`Set` vs setoid shapes** — start with `≡` on shapes; revisit only if quotienting becomes necessary.
- **Library drift** — dependencies are registered globally via `~/.config/agda/libraries`; the README records the agda-categories commit and Agda version used (`c2e7c13e`, 2.7.0.1).

## Immediate next steps

1. **R0 spike** (`plan/HTML.md`): build a minimal reveal.js page as an `XMLM` value, print it with parsnip, and open it with reveal.js in a browser. This de-risks the top-priority backend and settles the HTML5-vs-XML policy.
2. Sketch `Slides.Core` with the minimal reveal.js vocabulary (`slide`, `section`, `heading`, `paragraph`, `bullets`, `pause`, `notes`) and decide nested vs flat bodies.
3. Prove `⟦ C₁ ⊎ C₂ ⟧ ≅ ⟦C₁⟧ + ⟦C₂⟧` (and the `const`/`id` cases) as natural isomorphisms, needed to compose slide containers.
4. Prove the bridge lemma relating `Container.FreeMonad.Eq` on `Free₀ XMLC ⊥ˢ` to parsnip's `_≈ₓ_` (R2).
5. Write the reveal.js algebra and driver (R3–R4).
6. Optionally finish the Eilenberg–Moore comparison.
