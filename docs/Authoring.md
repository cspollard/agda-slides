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
| Body (`Body`, a `do` block) | `placed x y w h content`, `classed classes content`, `diagram d`, `script js`, `mount id`, `heading n text`, `paragraph text`, `bullets texts`, `incremental texts`, `code language source`, `displayMath math`, `figure path caption` (checked), `notes text`, `table header rows`, `columns [contents]`, `box title content`, `fragment content`, `fragmentWith style content`, `pause`, `bibliography` |
| Content (inside `columns`, `box`, `fragment`) | the same commands under `Content.`, for example `Content.paragraph` |
| Text | a string literal, or a list of `Inline`s: `text`, `emph`, `strong`, `codeSpan`, `link url text`, `inlineMath math`, `cite key` (checked) |
| Math (`Slides.Math`, imported qualified as `M`) | `M.var`, `M.num`, `M.greek`, `M.frac`, `M.sqrt`, `M.sum`, `M.integral`, `M.prod`, `M.fn`, `M.paren`, `M.call f [args]`, `M.tuple`, `M.juxt`, `M.dd`, `M.cal`, `M.bb`, `M.vec`, `M.hat`, `M.bar`, `M.text`, `M.raw`; relations include `M.mid` (∣) and `M.elem` (∈); operators `M.+ M.- M.* M./ M.^ M.≡ M.≤ …`; literals: `2` is a number and `"x"` an identifier |
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

### Subscripts and superscripts in labels

A `label` understands light markup: `_x` or `_{xyz}` sets a subscript, `^x`
or `^{xyz}` a superscript, and a backslash quotes the next character (`\_`
is a literal underscore). So `"t_ω"`, `"g(y_1) + g(y_2)"` and `"x^{n+1}"` come
out as typeset scripts. The renderer emits `<tspan>`s shifted by whole user
units (not `baseline-shift`, which browsers handle unevenly) in a smaller
font. A label without markup is unchanged. This is for diagram text only;
use `Slides.Math` for formulas in running text.

### Styling diagrams

Every element takes a `Style`, built from `defaultStyle` with `stroked`, `filled`,
`thick`, and the hooks for stylesheets and scripts:

| Style function | Effect |
| --- | --- |
| `withClass "a b"` | CSS class(es); a stylesheet can then restyle the element, and scripts can find it |
| `withId "x"` | element id (unique in the deck), e.g. to highlight a node from JavaScript |
| `rounded n` | corner radius of a `rect` |
| `dashed "6 4"` | `stroke-dasharray` |
| `faded n` | opacity in percent |
| `anchored "start"` | `text-anchor` of a `label` (default `"middle"`) |

`path d style` draws an SVG path (`d` as in the attribute). The `<div class="diagram">`
around the SVG has the diagram's `name` as its `id`, so a script can find it.
Classes override the default colours (a stylesheet rule beats the SVG
attributes), which is how `assets/pairs/pairs.css` themes a whole deck.

### Laying diagrams out: `Slides.Diagram.Layout`

Writing absolute coordinates gets tedious. `Slides.Diagram.Layout` is a small
layout language, in the spirit of Haskell's `diagrams`, that compiles to the same
`Diagram`. Like the rest of the library it is a free monad on a container:
one container `DiagramC S = Op S ▷ arity` (`Slides.Diagram.Syntax`), whose
operations are primitives (rectangles, text, spacers, …), the binary connectives
(beside, above, atop and the two captions) and the annotations (`named`,
`connect`). `S` is the scalar that sizes are written in; decks use ℕ. A
`Dia S` is a closed program `DiagramC S ⋆ ⊥`, a tree of operations; the
combinators below are smart constructors that build it. Gaps, margins and
minimum widths are not operations, they are spacers. Nothing is laid out until
it is interpreted: an interpretation is an `Algebra S A` (the operation and the
results for its children) and `fold` is the catamorphism. `layout` folds
into `Slides.Diagram.Place.Layout` (a sized rectangle that draws itself at an
offset and carries named anchors), `compile` turns that into a `Diagram`, and
`Slides.Diagram.Names.dangling` is a second algebra that lists the names a
`connect` refers to but nothing declares, so a deck can state
`dangling d ≡ []` and have a misspelled name fail to typecheck.

```agda
open import Slides.Diagram.Layout

step : String → String → Dia ℕ
step i t = named i (framed 330 200 (rounded 18 (withId i (cls "node")))
                      (text 28 t (cls "big")))

stages : Diagram
stages = compile "d-stages" 100 (margin 10 20 10 30
  (connectEW "a" "b" (cls "flow am")
    (hcat 45 (step "a" "Pretrain" ∷ step "b" "Cache" ∷ []))))
```

| Combinator | Effect |
|---|---|
| `rectangle w h style`, `disc r style`, `segment w h style`, `spacer w h` | leaves (`segment` is a line across a `w × h` box; `segment w 0` is a rule) |
| `text size s style`, `bold size s style`, `lines size ss style`, `paragraph align size maxWidth s style` | text (see below) |
| `hcat gap ds`, `vcat gap ds` | a row or column, centred on the other axis; `hcatA` / `vcatA` take an alignment (`top middle bottom`, `left centred right`) |
| `beside a b`, `above a b`, `atop a b` | binary forms (`besideA`, `aboveA` with an alignment); `atop` centres `b` on `a` |
| `framed w h style d` | a rectangle with `d` centred on it |
| `margin l t r b d`, `padded n d`, `boxWidth w d`, `topAligned h d` | extra space around, a minimum width, or top-aligning inside a frame (all built from `∥`, `═`, `⊙` and spacers) |
| `captionAbove gap lbl d`, `captionBelow gap lbl d` | a caption a gap away; empty space of the same size goes on the other side, so `d` stays at the centre (`labelAbove lbl d` is the same without a gap) |
| `named n d` | remember the extent of `d` under the name `n` |
| `connect a side b side style d`, `connectEW a b style d` | an arrow between two named boxes (`north south east west middle`); an unknown name draws nothing |
| `connectP a port b port style d` | the same, from a `side s` or `at s pct` (percent along the edge: `at north 40`), to spread arrows over an edge |
| `raw w h elements` | the escape hatch: `Element`s with the diagram's own coordinates (paths, curves) |
| `compile name percent d` | the `Diagram` the rest of the library takes |

**Operators.** `Slides.Diagram.Notation` (it re-exports `Layout`'s vocabulary)
writes the same terms with operators. `Dia` has three associative operations with
unit `empty`: `a ∥ b` (beside), `a ═ b` (above) and `a ⊙ b` (atop). A gap is
itself a diagram, `↔ n` or `↕ n`, so `a ∥ ↔ 40 ∥ b` has no gap parameter and
chains without nesting. There is no interchange law between `∥` and `═`: the two
groupings of a 2 × 2 block align their columns differently.

| Notation | Meaning |
|---|---|
| `a ∥ b`, `a ═ b`, `a ⊙ b` | beside, above, atop (`∥↑ ∥↓ ═◂ ═▸` align to an edge) |
| `↔ n`, `↕ n` | horizontal and vertical space |
| `⟨ ds ⟩ₕ g`, `⟨ ds ⟩ᵥ g` | a row or column with gap `g` |
| `"id" ⦂ d` | `named` |
| `d ⌄[ g ] lbl`, `lbl ⌃[ g ] d` | a caption below or above `d` |
| `"a" ⟶ "b"`, `"a" ⟱ "b"` | an edge, east to west or south to north |
| `"a" ⊢ at south 40 ⇒ "b" ⊢ side north` | an edge between any two ports |
| `d ▹[ style ] edges` | draw a list of edges over `d`, the first first |
| `d ▹ edge ∶ style` | one edge |

Precedence, loosest first: `⦂`, `▹`, `═`, `∥`, `⟶`/`⇒`, `⊙`, captions. Parenthesise
a `⦂` that sits next to a caption.

```agda
stages = compile "d-stages" 100 (margin 10 20 10 30
  (⟨ step "a" "Pretrain" ∷ step "b" "Cache" ∷ [] ⟩ₕ 45
     ▹[ cls "flow am" ] ("a" ⟶ "b" ∷ [])))
```

**Typing the operators in Emacs.** In `agda2-mode` (or any buffer using the Agda
input method) each symbol is `\` followed by a key sequence. Most are in the
standard table:

| Symbol | Keys | Symbol | Keys |
|---|---|---|---|
| `∥` | `\\|\|` (two bars) | `⟶` | `\r--` (or `\-->`) |
| `═` | `\--=` | `⟱` | `\d==` |
| `⊙` | `\o.` | `⇒` | `\=>` (or `\r=`) |
| `↔` | `\<->` (or `\lr-`) | `⊢` | `\\|-` |
| `↕` | `\ud-` | `∶` | `\:` |
| `⟨` `⟩` | `\<` `\>` | `↑` `↓` | `\u-` `\d-` |
| `ₕ` `ᵥ` | `\_h` `\_v` | `◂` | `\t` |

`⦂`, `⌄`, `⌃`, `▹` and `▸` have no direct key sequence (`⦂` and `▹` are later
entries of the `\:` and `\tw` candidate lists; `⌄` and `⌃` are not in the table).
Add them to your Emacs configuration:

```elisp
(with-eval-after-load 'agda-input
  (add-to-list 'agda-input-user-translations '("nm"   . ("⦂")))   ; \nm   named
  (add-to-list 'agda-input-user-translations '("lbld" . ("⌄")))   ; \lbld caption below
  (add-to-list 'agda-input-user-translations '("lblu" . ("⌃")))   ; \lblu caption above
  (add-to-list 'agda-input-user-translations '("t>"   . ("▹")))   ; \t>   edge list
  (add-to-list 'agda-input-user-translations '("tr"   . ("▸")))   ; \tr   align right
  (agda-input-setup))
```

so that `\nm`, `\lbld`, `\lblu`, `\t>` and `\tr` type them. The operators with
several symbols are typed one symbol at a time: `∥↑` is `\||` then `\u-`, `═◂` is
`\--=` then `\t`, and `▹[` is `\t>` then `[`. `agda-input-user-translations`
is the standard hook for this; `M-x describe-char` on a symbol shows its key
sequence if you want to check one.

Coordinates are natural numbers, so a diagram always grows to the right and
down; there is no rotation or scaling. Styles and CSS classes work exactly as
for raw elements. `Slides.Examples.Pairs` builds all its diagrams this way.

**Text.** There is no browser at layout time, so text is measured from a table:
`Slides.Diagram.TextMetrics` holds the advance of every printable ASCII character
in a humanist sans (Helvetica's widths scaled by 92%, close to reveal.js's Source
Sans), in thousandths of an em; other characters count 0.6 em. `_`/`^` markup is
measured at 70% size, as it is drawn. A `text` is `size × 3/2` high and as wide
as its characters, `bold` is 8% wider, and a size is a number in the diagram's
own units. This is good to a few percent, which is what centring, gaps and
wrapping need; give a box an explicit width where a fit has to be exact.
`paragraph align size maxWidth s style` breaks running text into lines of at most
`maxWidth` by words (keep markup inside one word) and stacks them left, centred
or right aligned.

### Scalars, half units and laws

The layout is computed in a scalar (`Slides.Diagram.Scalar.Ops`): `LayoutWith O`
for any `Ops S`, and, for decks, the same names at ℕ. ℤ and ℚ are also provided,
and `Slides.Examples.PairsScalar` checks that the Pairs diagrams, taken to ℤ and
ℚ by `mapDia` (the action of `Dia` on a change of scalar), lay out identically
in all three. Sizes are in diagram units, but positions are kept in
*half* units, so centring is `outer - inner` with no division and never rounds;
the positions are halved once, when the layout becomes a `Diagram`. A layout is
plain data (sizes, drawing commands, named anchors), not a function.

`Slides.Diagram.Laws` proves, for any scalar whose `Ops` form a commutative ring
up to an equivalence `_≈_` with a congruent, commutative, associative maximum
(`IsLawful`; ℤ and ℚ are, with `_≈_` = `_≡_`; ℕ is not, since its difference is
the monus), that, up to `_≈ᴸ_` (`Slides.Diagram.Equality`, the scalar's `_≈_`
lifted pointwise to sizes, drawing commands and anchors):

- translation is an action (`shift-0`, `shift-∘`);
- `∥`, `═` and `⊙` are associative (`∥-assoc`, `═-assoc`, `⊙-assoc`);
- the empty diagram is a unit of each, for a layout of non-negative size
  (`∥-unitˡ`, `∥-unitʳ`, …; `Valid`);
- `named` and `connect` leave a layout's size and anchors alone;
- size fusion: the width and height of `layout d` are the fold of `sizeAlgebra`.

`Raw` is outside the translation law: its elements are in the final diagram's
coordinates, so shifting a layout does not move them.

`Slides.Diagram.NamesSound` proves that `dangling d ≡ []` implies every `connect`
draws an arrow. `dangling` resolves a connection against the names declared
*inside that connect's own diagram*, since that is all `connect` can see: a name
declared next to the `connect` is reported.

## Styling slides: `classed`

`classed "card pink" content` wraps content in `<div class="card pink">`. It is the
hook for a deck's own stylesheet (cards, callouts, columns of your own). Content
inside is a `Content` program, so use `Content.paragraph`, `Content.bullets`, … and
`Content.diagram`. A stylesheet is added through the theme:

```agda
theme = record Reveal.blackTheme { stylesheets = "slides.css" ∷ "mydeck.css" ∷ [] }
```

Both backends render `classed`; with `pause` it appears on a later step like any
layout command.

Both backends render these. A future backend that cannot render a feature
lowers it or refuses the deck; see `plan/Capabilities.md`.

## JavaScript

`script js` runs a piece of JavaScript once, the first time its slide is shown,
with the slide element bound to `slide`; `mount id` adds an empty element with
that id for the script to draw into. Both work in the reveal.js and standalone
backends (and inside `placed`, `columns` and `box`, as `Content.script` and
`Content.mount`).

```agda
slide (do heading 2 "Live"
          mount "counter"
          script "document.getElementById('counter').textContent = 'hello';")
```

Extra JavaScript files go in `RevealConfig.scriptFiles` (paths relative to the
page; loaded after the reveal.js plugins and before `init.js`), so a deck can
keep its animations in a file and call them from `script`:

```agda
config = record Reveal.defaultConfig { scriptFiles = "mydeck.js" ∷ []
                                     ; scripts = "Reveal.configure({center: false});" ∷ [] }
```

`docs/PairsDeck.md` shows this in a full deck.

The code is not checked: it is carried in a `data-js` attribute (so the verified
printer escapes it correctly) and a small loader in `init.js` / `plain.js` runs
it. To run code for the whole deck, put strings in `RevealConfig.scripts`; they
are appended to `init.js` after `Reveal.initialize`, where `Reveal` is in scope.
A backend with no JavaScript would drop these commands with a lowering
(`Slides.Lower`).

## Composing and lowering

Components that take arguments compose with Kleisli composition,
`f >=> g = λ x → f x >>= g` (`Slides.DSL`). Rewriting a deck is a *lowering*
(`Container.Lowering`): a map from each command to a program, extended to whole
programs by `lower`. Lowerings compose with `_⋙_`, and containers with
lowerings form a category (`Container.Lowering.Category`).

```agda
open import Container.Lowering using (_⋙_)
open import Slides.Lower using (lowerDeck; stripNotes; diagramPlaceholder)

plainer : Deck → Deck
plainer = lowerDeck (stripNotes ⋙ diagramPlaceholder)
```

`lowerDeck` rewrites content wherever it occurs (slide bodies, columns, boxes,
fragments, placed boxes). Rendering the lowered deck equals rendering the
original with a pulled-back algebra (`lower-fusion`). Write your own lowering as
a function from a content command to a content program, for example
`stripNotes (notes _) = pure tt; stripNotes a = ret a`.

## Where reveal.js comes from

`RevealConfig.base` is the URL or path of the reveal.js distribution. The typed
choice is `Reveal.Source`: `local "reveal/"` (a copy linked next to the page,
what `make example` does) or `cdn "6.0.2"` (that version from jsDelivr, nothing to
install, but the browser needs network access). `Reveal.withSource s config` sets
it, so a deck can offer both:

```agda
build : List String → IO ⊤
build ("local" ∷ _) = writeRevealDeck "out/talk" (Reveal.withSource (Reveal.local "reveal/") cfg) talk
build _             = writeRevealDeck "out/talk" (Reveal.withSource (Reveal.cdn "6.0.2") cfg) talk

main = run (getArgs >>= build)
```

The math plugin loads KaTeX from a CDN in either case.

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
