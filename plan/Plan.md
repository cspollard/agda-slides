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
- Library modules are `--safe --without-K` (each carries its own `OPTIONS` pragma; the `.agda-lib` only sets `--without-K`). Only executables (`Main`, the spikes) drop `--safe` to use IO.

## Repository layout

```
agda-slides.agda-lib      depends: standard-library, agda-categories; include: src, parsnip/src; flags --without-K (each library module carries its own `--safe`)
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
- [x] `Container.FreeMonad.Monadic`: `Free ⊣ Forget` is a monadic adjunction (`IsMonadicAdjunction`): an inverse `Comparison⁻¹` to agda-categories' comparison functor, and both natural isomorphisms (identity on carriers; the content is `fold-action`: for a module `(A , a)`, folding the induced algebra over the identity is `a`). So `⟦C⟧`-algebras (backends) are the Eilenberg–Moore algebras of the free monad.
- [ ] Deferred (stretch): faithfulness/fullness of `Poly-⇒`; naturality of the sum isomorphism in the setoid argument, and the `×`/`const`/`id` cases of `Data.Container.Combinator` (not needed so far).
- [x] `Container.Sum`: `⟦C₁ ⊎ C₂⟧ A ≅ ⟦C₁⟧ A ⊎ ⟦C₂⟧ A` as a stdlib `Inverse` of setoids, and `copair` of algebras with its universal property (`copair-inj₁`, `copair-inj₂`, `copair-unique`); this is how backends for separate vocabularies combine.

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

Decision — nested vs flat slide bodies: **nested, by stratification** (implemented in `Slides.Core`).
- The shape of a `slide` command contains the slide's content program (`Body = ContentC ⋆ ⊤`), and `stack` (a reveal.js vertical stack) contains a list of bodies. No container mentions itself, so strict positivity is not an issue, and `do`-notation works at both levels (`Slides.DSL`).
- Why not a position-branching encoding (one position for the body, one for the rest): `bind` would substitute the continuation into the body's leaves too, which is wrong for scoped constructs. Stratifying avoids it.
- Consequence for backends: a backend is a pair of algebras, one for `ContentC` and one for `DeckC` whose `slide`/`stack` handlers use the fold of the content algebra on the body they contain.
- Further nesting (columns, boxes) adds another stratum (`LayoutC` whose `columns` shape contains content programs) combined with `ContentC` via container sum; this is why the `⊎` isomorphisms are needed.
- `pause` in the beamer sense (everything after appears incrementally) needs a stateful algebra (carrier a function out of the current fragment mode). v1 uses explicit incremental bullets; revisit `pause` once the first backend works.
- The flat begin/end presentation and its equivalence proof are optional and no longer on the critical path.

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
- Plot/figure support (external images; inline SVG via parsnip's `Data.SVG`, `plan/HTML.md` R6).

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

In progress: capability-indexed decks (positioned elements, diagrams, backends with different feature sets) — see `plan/Capabilities.md`.

Infrastructure for writing decks is in place: `docs/Authoring.md`, `Slides.Driver` (one-line `Main` modules), the `Showcase` deck, and the full test suite (`make check test test-browser test-playwright test-negative`). What remains is mostly optional:

Steps 1–6 of the previous list are done (vocabulary, theming, components, restyling lemma, explicit fragments, plain HTML backend); see the status notes above and `plan/HTML.md`. What remains, roughly in order of value:

1. **Author experience**
   - ~~Overloaded string literals~~ — done: a string literal at type `Text` or `Inline` is plain text (`heading 1 "Title"`, `paragraph ("a " ∷ emph "b" ∷ [])`), and the primed `′` variants are gone. Two scoping facts made it work: the user's module needs `fromString` in scope (the DSL re-exports `Agda.Builtin.FromString`) and the instance `tt : ⊤` for the literal's side condition (re-exported too); `String` literals then need an `IsString String` instance, also provided. The rendered output of all examples is unchanged.
   - ~~Typecheck-time resource checks~~ — done: `Slides.Resources` (a deck declares `Resources`: figure paths and a bibliography; `Checked R` provides `figure`, `cite`, `bibliography`). `figure` and `cite` take an instance argument `Found b kind name`, which is `⊤` (found with `tt`) when the name is declared and an error naming the resource otherwise (`No instance of type Found (figureDeclared "plto.svg") "figure" "plto.svg"`); `Missing kind name` is what it evaluates to. `make test-negative` checks that decks with a typo fail to typecheck; `make check-resources` checks that declared figures exist on disk (Agda cannot see the file system). New vocabulary: `Inline.cite` (rendered `<span class="cite">[key]</span>`) and `ContentShape.references` (an `<ol class="references">` with `ref-key` ids). The unchecked `figureUnchecked` remains for decks without declared resources. Not done: warning about declared-but-unused resources, and citation numbering/ordering.
   - ~~Typed math~~ — done: `Slides.Math` is a formula AST (identifiers, numbers, Greek letters, `+ - ·`, fractions, powers, subscripts, roots, functions, sums, integrals, parentheses, relations, `\vec`/`\hat`/`\bar`, upright text, and a `raw` escape hatch) with a printer to LaTeX that braces every argument of `\frac`, `^`, `_` and `\sqrt`; operators `_+_ _-_ _*_ _/_ _^_ _₍_₎ _≡_ _≤_ …` and overloaded literals (`2` is `num 2`, `"x"` is an identifier). `inlineMath` and `displayMath` now take `Math`. Literal instances live in `Slides.Literals` (re-exported by `Slides.DSL`). Not proved: that printed formulas have balanced braces (true by construction of the printer, but not stated as a lemma).
2. **Backends and tests** — done:
   - ~~Browser driver~~: `tests/browser/run.mjs` (Playwright, using the system Chrome) drives the rendered `Showcase` deck: reveal.js configuration, keyboard stepping through `pause` fragments, explicit fragments, KaTeX, inline markup, figure/citations, backgrounds, vertical stacks and the URL hash, and the standalone backend's arrow/space/Home/End navigation (42 checks). `make showcase test-playwright`.
   - ~~JSON numbers~~: `RevealConfig.width`/`height` are printed as JSON numbers by parsnip's printer.
   - ~~Implicit `pause`~~: `Slides.Steps.steps` elaborates a body into a pause-free one: after a `pause`, content commands become `fragment`s, other layout commands `stepped`, and `notes` are left alone. Both backends apply it to each slide body. The mode flows through sequencing and `go-bind` proves how (`go m (b₁ >> b₂)` elaborates `b₂` in the mode `after m b₁`), so a pause in one component affects what follows it. The old concatenation lemma `renderBody-bind` is unchanged because `pause` renders as nothing; elaboration is a separate, earlier pass.
   - A test deck: `Slides.Examples.Showcase` uses every feature (pause, fragments, typed math, marked-up text, checked figure and citations, table, background, stack with transition, box, references); `make showcase` renders it with both backends and golden-tests the output.
3. **Phase 1 stretch**
   - Fullness/faithfulness of `Poly-⇒`; naturality of the sum isomorphism in the setoid argument.
4. **Phase 6 ideas**: indexed containers for typed slide state, layout as a monoidal structure, further backends (Beamer/LaTeX, PDF, Markdown), watch mode.
