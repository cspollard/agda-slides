# Writing a deck

A deck is an Agda module. Start from `src/Slides/Examples/Showcase.agda`, which uses every feature.

## The shape of a deck

```agda
{-# OPTIONS --safe --without-K #-}
module MyTalk where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Core using (NoCap; Deck; emph; strong; codeSpan; inlineMath; link)
open import Slides.DSL
open import Slides.Components
open import Slides.Resources
import Slides.Math as M

resources : Resources
resources = record
  { figures    = "plot.svg" ∷ []
  ; references = ("Knuth84" , "D. Knuth. The TeXbook. 1984.") ∷ [] }

open Checked resources

talk : Deck NoCap
talk = do
  titleSlide "Title" "Subtitle" "Author"
  slide (do heading 2 "A slide"
            paragraph ("some " ∷ emph "marked-up" ∷ " text, cited " ∷ cite "Knuth84" ∷ [])
            pause
            displayMath (M.frac "a" "b" M.≡ 2))
```

Place it under `src/` (or add a directory to `include:` in `agda-slides.agda-lib`).

## Commands

| Level | Commands |
| --- | --- |
| Deck (`Deck`) | `slide body`, `slideWith options body`, `stack bodies`, `stackWith options bodies`; options: `background "#hex"`, `transition "zoom"` |
| Body (`Body`, a `do` block) | `heading n text`, `paragraph text`, `bullets texts`, `incremental texts`, `code language source`, `displayMath math`, `figure path caption` (checked), `notes text`, `table header rows`, `columns [contents]`, `box title content`, `fragment content`, `fragmentWith style content`, `pause`, `bibliography` |
| Content (inside `columns`, `box`, `fragment`) | the same commands under `Content.`, for example `Content.paragraph` |
| Text | a string literal, or a list of `Inline`s: `text`, `emph`, `strong`, `codeSpan`, `link url text`, `inlineMath math`, `cite key` (checked) |
| Math (`Slides.Math`, imported qualified as `M`) | `M.var`, `M.num`, `M.greek`, `M.frac`, `M.sqrt`, `M.sum`, `M.integral`, `M.fn`, `M.paren`, `M.vec`, `M.text`, `M.raw`; operators `M.+ M.- M.* M./ M.^ M.≡ M.≤ …`; literals: `2` is a number and `"x"` an identifier |
| Components (`Slides.Components`) | `titleSlide`, `sectionSlide`, `bulletBody`, `incrementalBody`, `twoColumn`, `resultsTable`, decorators `titled`, `withNotes` |

Notes:
- `pause` makes everything after it in the same body appear step by step (notes stay put). Use `fragment` for a single explicit step.
- A figure or citation that is not declared in `resources` is a type error that names it. `make check-resources` checks that the declared figure files exist.
- To use a `String` variable as text, write `plain s`.
- Literals need `Slides.DSL` (which re-exports `Slides.Literals`) in scope in the module that writes them.

## Optional features (capabilities)

A deck has type `Deck K`, where `K` lists the optional features it uses:
`NoCap` for none, `Placed` for positioned boxes, and `K ⊕ L` for several. The
core commands work at any `K`. A capability command carries an instance
argument `Placed ⊑ K`, so it only typechecks in a deck whose type provides it:

```agda
open import Slides.Capability.Placed

talk : Deck Placed
talk = slide (do heading 2 "Placed"
                 placed 10 50 30 20 (Content.paragraph "at 10%, 50%")   -- x y w h, percent of the slide
                 pause
                 placed 60 50 30 20 (Content.paragraph "on the next step"))
```

A backend must support `K` (`HTMLCap K`); both HTML backends support `Placed`.
Rendering a deck with a capability the backend lacks fails with `No instance
of type HTMLCap …`. See `plan/Capabilities.md`.

## Rendering

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

Compile it with `agda --compile` (see the `showcase` target in the `Makefile` for the exact steps), put reveal.js and `assets/slides.css` next to the generated `index.html` (`out/mytalk/reveal` and `out/mytalk/slides.css`), and open it in a browser.

Configuration (`Slides.Backend.Reveal.RevealConfig`): title, location of reveal.js, `Theme` (`blackTheme`, `whiteTheme`, `serifTheme`, `solarizedTheme`), transition, slide number, controls, progress, width and height. `writePlainDeck` and `Slides.Backend.Plain` give a standalone page with its own navigation script.

## Tests

`make check` typechecks everything; `make example talk plain showcase` renders the example decks; `make test` diffs them against `tests/golden/`; `make test-browser` and `make test-playwright` load them in Chrome; `make test-negative` checks that undeclared resources are rejected.
