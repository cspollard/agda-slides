# Plots

Vector plots, computed in ℚ and lowered to `Dia ℕ`, so every backend, the layout laws and the
animations apply unchanged.  Design and history: `plan/Plots.md`.  Build the examples with
`make plots` (`out/plots`) and `make plot-data` (`out/plot-data`, from `data/spectrum.csv`).

## Using it

```agda
open import Slides.Plot.Mark
open import Slides.Plot.Render

p : Plot
p = plot 640 400 (axisSpec lo hi "x") (axisSpec lo′ hi′ "y")
      ( series (line (colour 1) points) (just "model")
      ∷ series (scatter (colour 4) dots) (just "data") ∷ [] )

-- in a deck:  diagram "name" 80 (render p)
```

- **Plot** `plot width height xaxis yaxis content`: the frame is exactly `width × height` whatever
  the data (`size-render`).  An axis is `axisSpec lo hi label`, or `logAxis lo hi label` (the data
  values, positive; drawn at log₁₀).  The y label sits horizontally above the axis.
- **Marks** (data in ℚ): `line`, `scatter`, `steps edges heights` (a filled histogram), `band`
  `(x, lo, hi)`, `errors` `(x, y, err)`, `hline`, `vline`, `note x y text`.  Each series has an
  optional legend name; later series are drawn on top.
- **Ratio panel** `withRatio upper lower`: shared x axis (the upper's range, the lower's label),
  the upper without x labels (`size-withRatio`).
- **Animation** (`Slides.Plot.Anim`): `reveal p` is one reveal step per prefix of the series, for
  `animate`; `morph n easing a b` is a flip book of `lerpPlot` between two plots of one shape.
  Needs `animation.js` next to the deck (the Makefile targets copy it).
- **Data in** (`Slides.Plot.Csv`): `rows`, `xy`, `xye` turn the text of a CSV into exact ℚ (no
  floats); header and blank lines are skipped.  The file is read in an executable's `Main`; the
  deck is a pure function of the text (`Examples/PlotsData`).
- **Helpers** (`Slides.Plot.Data`): `decimal m k` is m / 10ᵏ, `linspace`, `graph f xs`, `inv`.

## Looks

Marks carry CSS classes (`plot-line`, `plot-fill`, `plot-dot`, `plot-axis`, `plot-grid`,
`plot-text`) and `colour n` adds `plot-sN`; `assets/plots.css` is the stylesheet (Okabe-Ito
palette in `--plot-1…8`).  Include it in the theme's `stylesheets` after `slides.css`.

## What is proved and what is checked

| Fact | Where | Status |
|---|---|---|
| `px` is monotone, within `0 … extent`, `px lo = 0`, `px hi = extent` | `Plot.Axis` | proved from the scalar theories |
| ticks are in range, in order | `Plot.Ticks.Rat` (`ticks-in-range`, `ticks-sorted`) | proved (by construction: the progression is cut to the range) |
| every clipped point is in the box | `Plot.Clip` (`clipLine-inside`) | proved (by construction: points are clamped) |
| frame is `width × height`; a ratio panel is `h₁ + h₂` high | `Plot.Laws` | proved |
| `lerp` starts at `a`, ends at `b`, fixes a fixed point | `Plot.Anim` | proved |
| the nice step, no tick in range is lost, clipping cuts where it should, formatting, CSV, `log10` | closed checks next to each definition | checked on values |
| `log10` is within 10⁻³ decades and exact on powers of ten | `Plot.Log` | checked; not monotone-proved (two polynomial branches meet at 3.16 only to the approximation error) |

## Limits

Text widths are approximate; the y label cannot be rotated; filled bands are flattened at the
box edge rather than clipped; log axes have no minor ticks and labels below 10⁻⁴ round to 0;
error bars on a log axis keep exact ends but their middle is not the data point.
