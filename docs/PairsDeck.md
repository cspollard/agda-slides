# Example: an introduction to "It Just Takes Two"

`src/Slides/Examples/Pairs.agda` is an eleven-slide introduction to
*It Just Takes Two: Scaling Amortized Inference to Large Sets* (Wehenkel, Kagan,
Heinrich, Pollard; [arXiv:2605.07972](https://arxiv.org/abs/2605.07972)). It is
the largest example in the repository and uses most of the library: typed math,
SVG diagrams, a custom stylesheet, `Slides.Anim` animations and a little JavaScript.

```
make pairs                        # reveal.js from a CDN: out/pairs/ (needs network in the browser)
make pairs-local REVEAL=…/node_modules/reveal.js   # a local copy: out/pairs-local/
open out/pairs/index.html
make test-pairs                                      # drives it in headless Chrome
```

## The slides

| # | Title | What it shows |
| --- | --- | --- |
| 1 | It Just Takes Two | title; point pairs drifting on a canvas |
| 2 | Inference from a set of observations | SVG diagram of θ, the shared nuisance ψ and the observations; the hierarchical model as typed math |
| 3 | A bump hunt, event by event | a histogram of 2500 simulated events (background and signal) that fills on the first step |
| 4 | Two ways to scale, both costly | two cards; the question appears on the next step (`pause`) |
| 5 | Building blocks: NPE with a Deep Set | pipeline diagram with dashes marching along the arrows; mean pooling and the NPE objective |
| 6 | PAIRS: train on pairs, finetune on aggregates | the three stages, one lit up per step |
| 7 | Why two is enough | the theorem in words; the chain N = 1, N = 2, Cauchy, every N lit up one link per step |
| 8 | Does it work? Five test beds | cards for the four benchmarks and the Gaussian check |
| 9 | Results | bars and counters growing to the paper's Circle Radius NLLs on the first step |
| 10 | Cost and scale | four statistic tiles, counting up on the first step |
| 11 | Take-aways | closing slide with the point-pairs background |

The figures quoted (1.17, 0.35 and 0.05 for the Circle Radius test NLL at
N = 1000; about 100× and 3–4× in cost; 128 scenes per batch; novel-view MSE
0.011 to 0.004) are from the paper's text. The bar chart shows only the three
numbers the text gives, not the full figure.

## How it is built

- **Content and structure** are an ordinary deck (`pairs : Deck`), a `do` block of
  `slide`s. Formulas are `Slides.Math` values (`joint`, `meanPool`, `objective`,
  `cauchy`).
- **Diagrams** are `Slides.Diagram` values, one per slide (`problem`, `pipeline`,
  `stages`, `chain`, `results`, `tiles`). Every look comes from a CSS class set
  with `withClass`; the helpers `card`, `boxEl`, `txt`, `dim`, `big` and `flow`
  at the top of the module keep the coordinates readable. Each diagram's `name`
  is the `id` of its `<div>`, and nodes that are animated carry a `withId`.
- **Styling** is `assets/pairs/pairs.css`: a light, grayscale look over reveal.js's
  `white` theme, cards, callouts and the diagram classes (`node`, `on`, `flow`,
  `bar`, `stat`, …). The palette is the `:root` block: neutrals plus four muted
  accents (`blue`, `crimson`, `plum`, `rust`; no yellows or greens) used by the
  colour-role classes, kept for what should catch the eye. It is added through the theme's `stylesheets`.
- **Animation** comes in two kinds.
  - Anything that follows the slide's steps is an `animate` (`Slides.Anim`; see
    `docs/Authoring.md`): a parameter follows a track, the diagram is a function of
    it, and each act is one reveal step.
    - Slides 6 and 7: `stagesDia lit` and `chainDia k` give the diagram with some
      cards highlighted; the acts are the successive states.
    - Slides 3, 9 and 10: `grow ticks f` runs `q` from 0 to 1 along an ease-out
      curve, and `f q` draws the bars, counters and histogram at `q`
      (`part q v` is `q` of `v` in whole units; `fixed2` and `fixed3` print
      decimals). The histogram's bins are one baked-in realisation of the
      simulation (`backgroundBins`, `signalBins`).
  - Slides 2 and 5: the flow arrows' dashes march along them, a `loop`
    (`marching f` runs the phase `0 … 7` once through; `flow ph` puts the class `ph<k>`
    on the arrow and the stylesheet offsets the dashes by `k/8` of a period).
    On slides 6 and 7 the same march runs under the reveal steps (`animateBoth`).
  - Free-running decoration is `assets/pairs/pairs.js`, loaded with
    `RevealConfig.scriptFiles`. Each slide calls one function from a `script`
    command; it runs once, when the slide is first shown, and only advances while
    that slide is current:

    | Call | Effect |
    | --- | --- |
    | `PAIRS.title(slide, id)` | point pairs drifting on a canvas in the `mount` with that id |

    It stays in JavaScript because a random drift is not a track.

- **Configuration** is in `PairsMain.agda`. Where reveal.js comes from is an option
  (`Reveal.Source`): `cdn "6.0.2"` loads the pinned version from jsDelivr, so the
  output is just `index.html`, `init.js`, `pairs.js`, `pairs.css` and `slides.css`;
  `local "reveal/"` uses a copy linked next to the page. The executable takes the
  choice as an argument (`PairsMain cdn`, the default, or `PairsMain local`), which
  is what the two make targets pass. KaTeX comes from the CDN in both, so math
  needs network access either way. The rest of the configuration is a 1280×720 canvas, slide numbers, the two stylesheets, `pairs.js`, and a deck-level script
  (`Reveal.configure({center: false})`) so titles stay at the top.

## Library features added for this deck

- `classed`, a `<div>` with CSS classes around content (`Slides.DSL`);
- diagram styles `withClass`, `withId`, `rounded`, `dashed`, `faded`, `anchored`,
  the `path` element, and the diagram's `name` as the container `id`;
- math constructors `prod`, `call`, `tuple`, `juxt`, `dd`, `cal`, `bb` and the
  relations `mid` and `elem`;
- `RevealConfig.scriptFiles` for extra JavaScript files;
- `Reveal.Source` (`local path` or `cdn version`) and `withSource` to choose where reveal.js is loaded from.

They are described in `docs/Authoring.md`.

## Reusing it

To make your own animated deck, copy `Pairs.agda` and `PairsMain.agda`, keep
`pairs.css` as a starting stylesheet, and write your animations in a JavaScript
file next to it, called from `script`, for anything that free-runs. Use `animate`
for anything that should follow the slide's steps. Only use ids on diagram nodes
that a script needs, and keep ids unique across the deck (the frames of an
`animate` repeat their contents, so give those nodes names, not ids).
