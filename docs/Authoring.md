# Writing a deck

A deck is an Agda module. Start from `src/Slides/Examples/Showcase.agda`, which uses every feature.

## The shape of a deck

```agda
{-# OPTIONS --safe --without-K #-}
module MyTalk where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Core using (Deck; emph; strong; codeSpan; inlineMath; link)
open import Slides.DSL
open import Slides.Components
open import Slides.Resources
import Slides.Math as M

resources : Resources
resources = record
  { figures    = "plot.svg" ∷ []
  ; references = ("Knuth84" , "D. Knuth. The TeXbook. 1984.") ∷ [] }

open Checked resources

talk : Deck
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
| Body (`Body`, a `do` block) | `placed x y w h content`, `diagram d`, `heading n text`, `paragraph text`, `bullets texts`, `incremental texts`, `code language source`, `displayMath math`, `figure path caption` (checked), `notes text`, `table header rows`, `columns [contents]`, `box title content`, `fragment content`, `fragmentWith style content`, `pause`, `bibliography` |
| Content (inside `columns`, `box`, `fragment`) | the same commands under `Content.`, for example `Content.paragraph` |
| Text | a string literal, or a list of `Inline`s: `text`, `emph`, `strong`, `codeSpan`, `link url text`, `inlineMath math`, `cite key` (checked) |
| Math (`Slides.Math`, imported qualified as `M`) | `M.var`, `M.num`, `M.greek`, `M.frac`, `M.sqrt`, `M.sum`, `M.integral`, `M.fn`, `M.paren`, `M.vec`, `M.text`, `M.raw`; operators `M.+ M.- M.* M./ M.^ M.≡ M.≤ …`; literals: `2` is a number and `"x"` an identifier |
| Components (`Slides.Components`) | `titleSlide`, `sectionSlide`, `bulletBody`, `incrementalBody`, `twoColumn`, `resultsTable`, decorators `titled`, `withNotes` |

Notes:
- `pause` makes everything after it in the same body appear step by step (notes stay put). Use `fragment` for a single explicit step.
- A figure or citation that is not declared in `resources` is a type error that names it. `make check-resources` checks that the declared figure files exist.
- To use a `String` variable as text, write `plain s`.
- Literals need `Slides.DSL` (which re-exports `Slides.Literals`) in scope in the module that writes them.

## Positioned boxes and diagrams

`placed x y w h content` puts a content program in a box at a fixed position;
the numbers are whole percentages of the slide (left, top, width, height).
After a `pause` it appears on the next step.

`diagram d` draws a small vector diagram (`Slides.Diagram`): a record with a
`name` (unique in the deck), a canvas `width` and `height`, the displayed
`percent` of the slide width, and a list of elements: `rect`, `circle`, `line`,
`arrow`, `label x y size text style` and `group`. Styles are built from
`defaultStyle` with `stroked`, `filled` and `thick`. A diagram is content, so
`Content.diagram d` can go inside `placed`, `columns` or `box`; there `percent`
is relative to the container.

```agda
open import Slides.Diagram

slide (do heading 2 "Pipeline"
          diagram (record
            { name = "pipeline" ; width = 300 ; height = 100 ; percent = 60
            ; elements = rect 10 25 100 50 defaultStyle
                       ∷ label 60 50 16 "parse" defaultStyle
                       ∷ arrow 110 50 190 50 defaultStyle
                       ∷ rect 190 25 100 50 (filled "#355" defaultStyle)
                       ∷ label 240 50 16 "render" defaultStyle ∷ [] })
          placed 60 70 35 20 (Content.paragraph "a note at 60%, 70%"))
```

Both backends render these. A future backend that cannot render a feature
lowers it or refuses the deck; see `plan/Capabilities.md`.

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
