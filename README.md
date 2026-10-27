# agda-slides

A DSL, written in Agda, for scientific slide decks. A deck is a program in the free monad over a container of slide commands. Backends (reveal.js, plain HTML, …) are algebras for the container's polynomial functor, and rendering is the unique fold out of the free algebra. The generic part is proved with [agda-categories](https://github.com/agda/agda-categories); the HTML is printed by [parsnip](https://github.com/cspollard/parsnip) (a submodule) whose XML printer is verified.

Docs: `docs/Authoring.md` (command reference), `docs/PairsDeck.md` (a full example deck with SVG diagrams and animations), `docs/Design.md` (how it is put together, and why), `plan/Plan.md` (what is open), `Goals.md`.

## A first deck

Requirements: Agda 2.7.0.1, `standard-library` and `agda-categories` registered in `~/.config/agda/libraries` (developed against agda-categories commit `c2e7c13e`), GHC (for `--compile`), and a reveal.js distribution (`npm install reveal.js`, then `REVEAL=…/node_modules/reveal.js`). Clone with `git clone --recurse-submodules` (or `git submodule update --init`).

Write the deck, `src/MyTalk.agda`:

```agda
{-# OPTIONS --safe --without-K #-}
module MyTalk where

open import Data.List using (_∷_; [])
open import Slides.Core using (Deck; emph)
open import Slides.DSL
open import Slides.Components using (titleSlide)
import Slides.Math as M

talk : Deck
talk = do
  titleSlide "Hello" "a deck in Agda" "A. Speaker"
  slide (do heading 2 "Why?"
            bullets ("typed" ∷ "composable" ∷ ("checked by " ∷ emph "Agda" ∷ []) ∷ [])
            pause
            displayMath (M.frac "a" "b" M.≡ 2))
```

and a main module that renders it, `src/MyTalkMain.agda`:

```agda
{-# OPTIONS --without-K --guardedness #-}
module MyTalkMain where

open import IO using (Main; run)
open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import MyTalk using (talk)

main : Main
main = run (writeRevealDeck "out/mytalk" defaultConfig talk)
```

Then build and open it:

```
make deck MAIN=src/MyTalkMain.agda NAME=mytalk REVEAL=/path/to/node_modules/reveal.js
open out/mytalk/index.html
```

`make deck` compiles the main module, links reveal.js and the stylesheet next to the output, and runs it. Use `writePlainDeck` and `Slides.Backend.Plain` instead for a single self-contained page with its own navigation script. A mistake in the deck (an undeclared figure or citation, a wrong argument) is an Agda type error.

## Design choices

- **Decks are free-monad programs.** Each slide command is an operation of a container (`Slides.Core`: `ContentC`, `LayoutC`, `DeckC`), so `do`-notation sequences commands and ordinary functions are components (`Slides.Components`). Nothing in `src/Container/` knows about slides.
- **Backends are algebras.** A backend interprets every command by giving an algebra for the container's polynomial functor on `Setoids`; the interpretation of a deck is the unique fold. Rendering therefore respects sequencing (`renderBody-bind`), algebra homomorphisms commute with it (`fold-hom`, used for restyling), and translating a program along a container morphism then folding equals folding with the pulled-back algebra (`fusion`).
- **Nesting is stratified.** A slide's shape contains its body and `columns` contain content programs, so no container mentions itself and strict positivity is never an issue. Combined vocabularies are container sums, with algebras combined by `copair`.
- **No instance search in the core.** `do`-notation is the free monad's own bind, features such as `placed` and `diagram` are ordinary layout commands, and a backend that cannot render a feature will lower it or refuse the deck (`docs/Design.md` explains why an earlier capability-indexed design was dropped: overlapping instances made typechecking exponential). Instances remain only where Agda requires them (overloaded literals) and for the resource checks.
- **Resources are checked when the deck typechecks.** A deck declares its figure files and bibliography keys (`Slides.Resources`); `figure` and `cite` take an instance argument that only resolves for declared names.
- **Rewrites are lowerings.** A lowering sends each command to a program (a Kleisli arrow, `Container.Lowering`); `lower` extends it to whole programs, lowerings compose and form a category, and folding a lowered program equals folding the original with a pulled-back algebra (proved). `Slides.Lower` lifts content lowerings to decks, and components compose with `_>=>_`.
- **Verified HTML where it is cheap.** Output is built as parsnip XML values and printed by its XML printer, with the (unverified) doctype as a constant prefix; empty non-void elements are padded so browsers do not misparse them. The tree-equality and `≈ₓ` bridge to parsnip's equality is proved.
- **Everything is `--safe --without-K`** except the executables, which use IO.

## Available functionality

| Area | What there is |
| --- | --- |
| Slide structure | slides, vertical stacks, backgrounds, per-slide transitions, speaker notes |
| Content | headings, paragraphs, bullet lists (optionally incremental), code, tables, figures with captions, bibliography |
| Text | plain, emphasis, strong, code spans, links, citations, inline math |
| Math | typed formula AST (fractions, sums, integrals, Greek, relations, accents, …) printed to LaTeX and rendered by KaTeX; overloaded literals (`2`, `"x"`) |
| Layout | columns, boxes, `placed` boxes at fixed percentages of the slide |
| Diagrams | typed vector diagrams (rectangles, circles, lines, arrows, labels, groups) printed as inline SVG |
| Steps | `pause` (everything after appears step by step), explicit `fragment`s with reveal.js styles |
| Components | title and section slides, decorators, bullet/two-column/table bodies |
| Backends | reveal.js (themes, size, slide numbers, controls) and standalone HTML (own navigation script and print stylesheet) |
| Styling | `classed` (a `<div>` with CSS classes), custom stylesheets through the theme, diagram elements with classes, ids, rounded corners, dashes, opacity, paths |
| JavaScript | `script` (run when its slide is first shown), `mount` (an element to draw into), deck-level `RevealConfig.scripts`, extra files through `RevealConfig.scriptFiles` |
| Rewriting | `lowerDeck` with composable lowerings (`stripNotes`, `diagramPlaceholder`), Kleisli composition `_>=>_` |
| Checks | undeclared figure/citation rejected; `make check-resources` checks figure files exist |

Scripts are not type checked. Not yet: figure/table numbering, Beamer/LaTeX and Markdown backends.

## Repository layout

- `src/Container/` — generic: containers as polynomial functors on `Setoids`, the category of containers and morphisms with its functors to polynomial endofunctors and to lowerings (`Container.Category`), the free monad, its algebraic description (`Free ⊣ Forget`, monadic), interpretation and fusion, container sums. Nothing here imports `Slides.*`.
- `src/Slides/` — the DSL: `Core` (vocabulary), `DSL` (commands and `do`-notation), `Math`, `Literals`, `Steps` (`pause`), `Resources`, `Components`, `Diagram`, `Backend/*` (`Common`, `Reveal`, `Plain`, `Diagram`, `Restyle`, `HTML`), `Driver`, `Examples/*`.
- `parsnip/` — submodule: verified XML/JSON/SVG printers and parsers with proved round trips.
- `assets/` — stylesheets, navigation script, sample figure. `tests/` — golden files, browser checks, negative tests. `plan/`, `docs/`.

## Make targets

```
make check            # typecheck everything under src/
make deck MAIN=… NAME=…   # compile and render any deck (see above)
make example talk plain showcase   # render the example decks (REVEAL=… as above)
make test             # golden-file diffs
make test-browser     # headless Chrome checks (CHROME=… to override)
make test-playwright  # drive the showcase deck in a real browser (42+ checks)
make pairs test-pairs # reveal.js from a CDN (no REVEAL needed); `make pairs-local REVEAL=…` for a local copy; the "It Just Takes Two" deck and its browser test (docs/PairsDeck.md)
make test-negative    # undeclared resources, key conflicts, a deck on a backend without Nav must not typecheck
make check-resources  # declared figures exist next to the rendered decks
```
