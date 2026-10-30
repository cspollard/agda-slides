# Plots: basic plotting on `Dia`

Status: phases 0-3 built merged to main (`make plots` renders `out/plots`; `make check` clean, 107 s for the tree).
Built: `Slides.Plot.{Axis,Axis.Rat,Format,Ticks,Ticks.Rat,Mark,Clip,Data,Render,Laws}` (~770 lines),
`Examples/Plots`, `assets/plots.css`.  Proved: `px-max`, `px-mono`, `px-lo`, `px-hi`, `ap-sorted`,
`size-render` (the frame is exactly `width x height`).  Checked on closed values only: formatting, 1-2-5 ticks
(in range, spacing), clipping (all points in the box).  Not done: `plot` DSL combinator (a plot is a `Dia ℕ`
block via `render`, no new deck combinator), goldens untouched (look is in `plots.css`), phase 3b.
Phase 4 built: `Slides.Plot.Log` (`log10` by decade shift + 5-term atanh series, exact on powers of ten, checked on
closed values to 10⁻³; `logAxis`), `withRatio` (shared x, upper panel without x labels), `size-withRatio`.
Phase 5 built: `Slides.Plot.Anim` (`reveal`: one act per prefix of the series, for `animate`; `morph`: a flip
book of `lerpPlot`, axis range included; proved `lerp-0`, `lerp-1`, `lerp-same`).  A morph is a frame list, as the plan
said (no multiplication in `Space`), not a `Lerp` term.  Needs `animation.js` in the output (the `plots` target copies it).
Phase 6 built: `Slides.Plot.Csv` (pure: text to `List (List ℚ)`, exact decimals, header/blank lines skipped; closed
check) and `PlotsDataMain` (the only IO: `readFiniteFile`), `make plot-data` from `data/spectrum.csv`.
Phase 3b deferred: the spike and the examples show no quantisation problem at slide sizes; revisit for 1000-bin histograms.
Error bars on a log axis keep exact ends; the dot is a separate scatter.  Monotonicity of `log10` not proved.  Design context in `docs/Objects.md`, rules in `docs/Contributing.md`.
Branch `plots` (worktree `../agda-slides-plots`).

## Goal
A deck author writes data and a few mark declarations, and gets an inline SVG plot that restyles
with the deck (CSS classes), prints on every backend, and can sit in an animation.  "Basic" means:
line, scatter, step histogram, band, error bars, reference lines; linear axes with nice ticks,
labels, grid, legend; later a ratio panel under a main panel (shared x), log y, and animation of
data.  Not in scope: interactivity, 3D surfaces, statistical fitting, reading ROOT files.

**Vector only [decided].**  No rasterising and no raster marks: a plot is SVG from `Dia`, so it
restyles with CSS, stays crisp at any size, and its output is deterministic.  Dense data is
thinned (per pixel column for lines, a cap on scatter points).  2D histograms and heatmaps are
rectangles with a class-based colour ramp, up to a few thousand cells; beyond that is the one
place to revisit this.  A plot made elsewhere stays the existing `figure` block.

## Audit: is `Dia` a suitable backend?
**Yes, with no change to the signature for phases 1-3.**  A plot is a *computation of a `Dia ℕ`
term*; every fold, law, animation and backend then applies unchanged, as `Slides.Three.*` does.
What the audit found, against the sources:

### What already fits
- **Marks are primitives.**  `Polyline`/`Polygon` (scalar-parametric point lists: curves, step
  outlines, filled bands), `Disc`/`Ellipse`/`Rectangle` (markers, bars), `Segment` (ticks, error
  bars), `Text` (tick and axis labels).  One `Polyline` op carries a whole series, so a
  1000-point curve is one node, not 1000 (layout cost and the `Share` DAG stay small).  `Path` is
  *not* needed: a filled histogram is a closed polygon.
- **Absolute placement.**  `place w h x y d` and `layers w h` put marks in a plot frame of
  declared size; `layers` gives exactly `w × h` regardless of content, which is the frame law we
  want (a plot's size is independent of its data).  Sub-diagrams may stick out of a frame, so
  clipped curves are the only thing to take care of (below).
- **Styling.**  `Style` has stroke, fill, dash, width, opacity, `cls`, `ident`; series colour and
  line style come from CSS classes (`cls "plot-s1"`), so plots restyle with the deck (dark/light,
  Plain vs Reveal), as the `curve`/`axis` classes of `TitleAnim` already do.
- **Anchors.**  `named` marks and `connect` give annotation arrows (an arrow to a peak) for free.
- **Layout glue.**  `Convenience` (`margin`, `hcat`/`vcat`, `labelAbove`/`Below`, `boxWidth`)
  composes axis labels, legend and panels.
- **Animation.**  Polyline points are scalar terms, so a leaf can move with `now`
  (`Examples/AnimRef`), and a dataset morph is a point-wise `Lerp`.  A static plot lifts with
  `liftDia`; a frame list is a scene of one-tick frames (`TitleAnim.curveFrame` already animates a
  plot this way: the existing proof of concept, with `plotL`, `visible`, `rise` as hand-written
  magic numbers that this plan replaces).
- **Deck block.**  `Block.diagram name percent (Dia ℕ)` exists; `name` must be unique (marker id).

### Gaps and constraints, most important first
1. **Coordinates are ℕ in half units; y points down.**  Data are signed, rational, and y is
   flipped, so the data-to-pixel map is the heart of the work and lives outside `Dia`: data in ℚ
   (stdlib `Data.Rational`), `Axis` carries `lo hi` and a pixel extent, `px : Axis → ℚ → ℕ`
   computes `⌊(x − lo)·W/(hi − lo)⌋`, y is `H ∸ px`.  Resolution is one unit (the printer halves
   half-units), so a 400-unit frame resolves 1 part in 400: fine for slides.  `Dia ℕ` is the only
   printable instance (`natPrint`; no ℚ printer), so we compute in ℚ and round once at the end.
   Cost risk: `ℚ` normalisation (gcd) per point; the data run in compiled Haskell (GHC integers)
   so it is fine at run time, but proofs by evaluation must stay on small closed terms.  Measure
   with a 1000-point series before committing (TODO already notes `n / 1` blowing up `Hom`).
2. **No multiplication or division in `Space`**, only `+ ∸ ⊔ pct`, so scaling cannot be a scalar
   term.  Consequence: pixel positions are literals, and an animated data morph is `Lerp` between
   precomputed literals (fine) but an animated *axis range* is not expressible as one term: it is a
   frame list (`frames`), which is the existing approach.  Accept.
3. **No clipping.**  A curve leaving the axis range would draw over the margins.  Clip by
   computation (Liang-Barsky on each segment, or drop points as `TitleAnim.visible` does) and prove
   the result lies in the box.  No new constructor: a clip connective would touch every fold
   (`Natural`, `Valid`, `Names`, `Print`, `Share`, the `AnimRef` JS evaluator) for little.
4. **No rotated text.**  The y-axis label cannot be vertical.  Put it horizontally above the axis
   (as `TitleAnim` does with "−2 ln L").  A `Rotate` annotation is the clean fix but costs the
   same 17-case sweep as a new primitive; defer, revisit only if horizontal labels prove ugly.
5. **Text placement and measurement.**  `Text` is centred on its frame; `anchored` only sets
   `text-anchor`.  Right-aligning y tick labels means computing the left edge from
   `TextMetrics.textWidth` (good to a few percent: enough for ticks, not for exact alignment).
   Number formatting is missing: need `ℚ → String` with a fixed number of decimals (stdlib has
   `Data.Nat.Show` only for ℕ), and a unit scale for tick labels (`10³`).
6. **Labels are plain SVG text.**  `Inline.inlineMath` prints as raw LaTeX source in a diagram
   label (`runsI`), so `"p_T [GeV]"` works through `sub`/`sup` markup and Unicode, but `\sqrt{s}`
   does not.  Axis labels use markup and Unicode; KaTeX-in-SVG is out of scope.
7. **Log axes need a logarithm.**  No reals and no `Float` (`--safe`, reproducible output).  Decade
   ticks are exact (`10ⁿ`); mapping an arbitrary value needs `ln`, as `Slides.Trig` needs `sin`:
   a rational polynomial of chosen order with a closed-value test (`make test-numeric`).  Log y is
   the norm in collider plots, so it is phase 4, not "never".
8. **CSS surface.**  New classes (`plot-axis`, `plot-grid`, `plot-s1..s8`, `plot-tick`) land in
   `assets/slides.css` and `assets/plain.css`; the goldens copy the stylesheets, so this is an
   intended golden change, done in its own commit.  Palette: colour-blind-safe, 8 entries,
   defined once as CSS variables.
9. **Layout laws and validity.**  `Valid` needs non-negative sizes (plot frames are literals, so
   fine); `Names.usage` wants unique names (each plot prefixes its ids; Contributing's unique-name
   rule applies to SVG `id`s, which a `ident` style would put in the DOM).

### Verdict
`Dia` is suitable as the backend and needs no new constructor.  The two things it lacks (rotated
text, clipping) have workarounds that are better than new constructors.  All the real design is a
new front end above it.

## Design: a front end that lowers to `Dia`
Principles apply (every type motivated, folds, laws).  A plot is data plus a fold:

- **`Axis`**: `lo hi : ℚ`, `kind : Lin | Log`, pixel extent `n : ℕ`.  Folds: `px : Axis → ℚ → ℕ`
  (the unique affine map sending `lo` to 0 and `hi` to `n`), `ticks : Axis → List ℚ` (nice 1-2-5
  steps).
- **`Mark`** (the signature of what is drawn): `Line pts`, `Points pts`, `Steps edges counts`,
  `Band lo hi`, `Errors pts`, `HLine y`, `VLine x`, `Note x y text`; each with a `Style` and a
  legend entry.  Marks have no sub-terms, so a plot's content is `List Mark` (the free monoid;
  overlay is `++`), not a free monad.  Panels (ratio plot under a main plot) are the one
  connective with children: `Stack` shares an x axis.  If a second connective appears, that is the
  moment to make `Plot` a free monad over a container and state the lowering as a Kleisli map in
  `Container.Lowering` (reuse, do not reprove).
- **`render : Plot → Dia ℕ`**: the fold.  Meaning first: a `Mark` denotes a set of points in data
  space; `render` is a homomorphism of overlay (`render (p ++ q) = render p ⊙ render q` up to the
  frame) and natural in restyling.

### Laws to prove (state them first, in the module header, before the code)
- `px` is monotone, `px lo = 0`, `px hi = n`, and `px x ≤ n` inside the range (names from the
  affine map; model facts as hypotheses, no ℚ computation in proofs).
- Clip: every point emitted by `clip` lies in the box; a series wholly inside is unchanged.
- Ticks: increasing, all in `[lo, hi]`, equally spaced, include 0 when the range straddles it.
- Step outline: `2n + 2` points, x monotone, closes on the baseline (the polygon of `n` bins).
- Frame law: the `size` of `render p` is the declared `w × h`, whatever the data
  (from `layers`/`place`).
- Overlay: `render` of `++` is `layers` of the renders (same frame).

## Phases
Each is its own branch off `plots`, a line budget stated before starting, and the gate in
`docs/Contributing.md`.

| # | Deliverable | Budget | Modules |
|---|-------------|--------|---------|
| 0 | Spike: re-express `TitleAnim`'s plot (axes, curve, interval) with hand-built `Dia` and measure the pain; list the combinators missing.  Confirms or revises the audit. | 100 | `Examples/PlotSpike` (deleted after) |
| 1 | `Axis`: `px`, `ticks`, `format` (ℚ to decimal string), laws above | 250 | `Slides.Plot.Axis`, `.Axis.Properties` |
| 2 | Marks and `render`: line, points, steps, band, errors, ref lines; clip; frame law | 300 | `Slides.Plot.Mark`, `.Render`, `.Clip`, `.Render.Properties` |
| 3 | Decoration and deck: axes, ticks, grid, labels, legend, `plot` in the DSL, CSS classes and palette; one example slide; goldens | 250 | `Slides.Plot.Frame`, `Deck/DSL` (one combinator), `assets/*.css`, `Examples/Plots` |
| 3b | Optional: `Print ℚ`, a `Dia ℚ` deck block; plots lowered by the identity | 120 | `Slides.Diagram.Print`, `Deck/Content`, `Backend/Render` |
| 4 | Ratio panel (shared x); log y with the `ln` polynomial | 300 | `Slides.Plot.Stack`, `Slides.Plot.Log` |
| 5 | Animation: reveal series one by one (a scene of plots), morph between datasets by `Lerp`, frame list when the axis moves | 200 | `Slides.Plot.Anim` |
| 6 | Data in: CSV read by an executable, passed as `List (ℚ × ℚ)`; nothing in core does IO | 150 | `Examples/*Main`, `Driver` |

Stop after phase 3 if nothing needs more: it already replaces the static `assets/plot.svg` and
the magic numbers of `TitleAnim`.

## Optional target: `Dia ℚ`
`Dia` is scalar-parametric, so the front end computes in ℚ and its last step is a choice of
lowering: `round : ℚ → ℕ` gives `Dia ℕ` (every existing backend; phases 1-3), the identity gives
`Dia ℚ` (phase 3b).  What ℚ buys: sub-unit resolution (a 1000-bin histogram on 400 units collapses
bins in ℕ; curves are quantised to whole units), no silent truncation (`∸` clamps negatives to 0;
`TitleAnim` works around it by hand; ℚ has negative lengths, which `Valid` already covers), and
rounding once at the printer instead of compounding.  Safe because layout is natural in the scalar
(`Hom`, `layout-natural-ok` under `OkDia`): existing `Dia ℕ` decks embed in `Dia ℚ` and their
goldens do not change.  Costs: a `Print ℚ` (decimals, deterministic; the `ℚ → String` formatter
needed for tick labels is the same code) and a way to put a `Dia ℚ` in a deck (a `diagramQ` block
or a `Layout`-level block).  Unchecked: whether `Render`, `Share` and the JS evaluator assume ℕ;
static plots need only the printer and block, animated ℚ plots need that checked first.  Ship ℕ
first; if the spike shows quantisation hurting on a real plot, 3b moves earlier.

## Decisions to make before phase 1
1. **Data scalar**: ℚ (signed, exact, stdlib) versus ℤ fixed-point (cheaper, no gcd).  Default ℚ
   for data, output ℕ or ℚ by the choice above; the spike's timing decides.
2. **Where the pixel extent comes from**: the plot declares its frame in units; the deck's
   `diagram name percent` already scales the SVG to a percentage of the slide width, so fonts scale
   with the figure.  Default: pick a frame and font size once (e.g. 640×400, 22 px) and let the
   percentage scale it.
3. **Histogram input**: bin edges plus counts (general) with a constructor from uniform bins.
4. **Text rotation**: accepted as horizontal for now (gap 4).

## Follow-ups (after phase 6), in order
Status: 1(a) and 1(b) done (`ticks-in-range`, `ticks-sorted`, `clipLine-inside`), 1(c) stated as the contract (not provable as built); 2 done (`docs/Plots.md`); 3 done: rebased onto `main` (59c38c2), goldens `plots.index.html` and `plots.css` added to `make test` (needs `make plots`), no CI in the repo; not pushed, no PR.
1. **Prove what is only checked.**  (a) every tick lies in `[lo, hi]` and the ticks are sorted; (b) every point
   `clipLine` returns lies in the box; (c) `log10` monotone.  Route for (a) and (b): make the property hold by
   construction (filter ticks by the range; clamp clipped points to the box) so the law is `all-filter` / a `⊔ ⊓`
   bound, with faithfulness (nothing in range dropped, no point moved when already inside) kept as closed checks.
   (c) is not provable as built: two polynomial branches meet at 3.16 only to within the approximation error, so
   monotonicity would need interval bounds on the series; state the error bound as the contract instead.
2. **Docs**: `docs/Plots.md` (the `Plot` record, marks, `logAxis`, `withRatio`, `reveal`, `morph`, CSV flow, CSS
   classes) and a pointer in `plans/TODO.md`.
3. **Finish the branch**: rebase onto `main`; decide which targets/CI cover `plots` and `plot-data`; optional golden
   for the plots deck.  Not pushed, no PR yet.
4. **Quality gaps**: text widths approximate; y label horizontal; filled bands flattened (not clipped) at the box
   edge; no minor ticks on log axes; labels below 10⁻⁴ round to 0; a morph needs plots of one shape.
5. **Phase 3b** (`Print ℚ`, `Dia ℚ` block) only if quantisation shows on a large histogram.

## Smooth curves (built: the `Function` extension)
Today's curves (`line`) are sampled by the caller and drawn as straight segments.  Options weighed: a `Curve f lo hi`
in `Dia` (breaks functoriality: `mapOp h` cannot push `h : S → T` through `f : S → S`); a `smooth` flag on `Polyline`
(about twenty match sites); a Bézier `Path` made by the caller (opaque).  **Built**, in `Slides.Diagram.Curve`
(about 120 lines) and `Slides.Plot.Exact`:
- `CurveC S` holds `Function f lo hi style` (arity ⊥); `Dia⁺ S = (DiagramC S ⊎ CurveC S) ⋆ ⊥` (Data types à la
  carte, `Container.Sum`); `lowerDia sm n = lower (lowerCurve sm n)` is a Kleisli map `Dia⁺ → Dia`, so `Dia`, `Op` and
  every handler are untouched and run after lowering (function as meaning, sampling as implementation: Elliott,
  Functional Images; stat then geom as in ggplot2).  A `Sampler S` (arithmetic with a total division, an order, a
  decimal notation) is its argument; `Slides.Plot.Exact.ratSampler` is the one for ℚ.
- The lowering samples `n + 1` evenly spaced points and draws a monotone cubic (Fritsch-Carlson in the Fritsch-Butland
  form: the harmonic mean of neighbouring secants, 0 where they change sign; no sqrt, no overshoot) as one Bézier
  `Path`: smooth on every backend, opaque (no morph and no clipping inside; accepted).
- `exact style f` is a `Mark` (data coordinates).  `render` composes `f` with the axis maps (frame pixels in ℚ, so a
  log axis smooths after the log), cuts the pixel range into runs inside the box on a one-pixel grid (clip before
  sampling, no smoothing across a cut; a run ends within a pixel of the edge) and lowers each run.  Existing marks and
  goldens are unchanged; `lerpMark` leaves an `exact` mark as it is (a function cannot be interpolated), so it does not
  morph.
- Proved: `lower-inject`, a diagram embedded along `inl` and lowered is itself (`Dia⁺` agrees with `Dia`); the generic
  Kleisli laws `lower-bind`, `lower-⋙`, `lower-ret` of `Container.Lowering.Properties` apply to `lowerDia` as to any
  lowering.  Functoriality of `Dia` is untouched (nothing changed in `Syntax`).
- **`Dia⁺` is deliberately not functorial in `S`.**  `mapDia h` acts on every scalar of a term, but a `Function`
  holds a function on scalars; `h : S → T` has no way back, so `f : S → S` cannot become `T → T`.  Changing the scalar
  is done on `Dia`, after lowering (the plot does `mapDia ratFloor` on the lowered path).
- Named contract, not proved: `Within` (`Curve.agda`): the function the path denotes is within ε of `f` on [lo, hi]
  (needs bounds on `f`, real analysis or intervals, not in the repo).  The monotone-cubic shape property (no
  overshoot beyond the samples) is likewise stated in the comment only.
- Deferred: adaptive sampling (bisect where the midpoint leaves the chord) as a separate step of the lowering; a
  `Function` over a scalar without a `Sampler` (only ℚ has one); `exact` in `Sample`/legend morphs.

## Risks
- Tick labels are placed using approximate text widths; misalignment of a few percent in y tick
  labels is expected and cosmetic.
- Output size: a plot with thousands of points ships thousands of coordinates; fine static, heavy
  in an event list (the `Share` DAG helps only for repeated subtrees).  Thin dense series in
  `render` (keep every k-th point per pixel column).
- Golden churn from the stylesheet commit; keep it separate and reviewed on its own.
