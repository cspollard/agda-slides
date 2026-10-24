# Plan: reveal.js (and HTML) production on top of parsnip

[parsnip](https://github.com/cspollard/parsnip) (git submodule at `parsnip/`) provides verified printers and parsers for XML (and JSON, and an SVG vocabulary). **The reveal.js backend is the top priority** (it is the first use case); a plain standalone HTML backend follows. Both emit HTML5 markup through the same parsnip pipeline, so the work here is shared and reveal.js simply comes first. This plan describes how Phase 3 (reveal.js) and Phase 4 (plain HTML) of `plan/Plan.md` use parsnip.

## What parsnip gives us (checked against commit `9ac93f3`)

| Module | Provides |
| --- | --- |
| `Data.XML.AST` | `XMLC : Container 0ℓ 0ℓ` (shape = tag, attributes, `n+1` text slots, validity evidence; positions = `Fin n`), `XMLDoc = XMLC ⋆ ⊥`, `XMLM A = XMLC ⋆ A`, constructors `node`, `leaf`, `parent`, `parentList`, and folds `foldXMLC`/`foldXMLM` |
| `Data.XML.Sanitize` | total constructors for runtime data (`element`, …): illegal characters become U+FFFD / `_`, duplicate attributes resolved, valid input unchanged, each repair proved valid |
| `Data.XML.Equality` | `_≈ₓ_` (bisimilarity) and `XMLSetoid : Setoid 0ℓ 0ℓ` |
| `Data.XML.Print` | `printXML : XMLDoc → List Char`, `renderXML : XMLDoc → String` |
| `Data.XML.RoundTrip` | `xmlStage : RightInverse XMLSetoid Chars` (to = `printXML`, from = total parser) so `parse (print x) ≈ₓ x`; `parseXML` and `parseXML-printXML` for the partial parser |
| `Data.SVG` | `svg`, `g`, `path`, `circle`, `rect`, `polygon`, `polyline` over `XMLM` |
| `Data.JSON.*` | JSON AST, printer, parser and round-trip (`jsonStage`) |
| `Data.Stage` | the `RightInverse`-based stage pattern and `mkStage` |

Two facts make the fit with this project direct:

1. The XML AST **is** a free monad over a `Container 0ℓ 0ℓ`, so everything in `Container.*` applies to it unchanged: `Poly XMLC` is an endofunctor on `Setoids 0ℓ 0ℓ`, `Free₀ XMLC` is the tree setoid, and `XMLSetoid` is a `Setoid 0ℓ 0ℓ`. `Slides.Backend.XML` records this bridge (typechecks today).
2. Documents are well-formed by construction (validity evidence lives in the node shapes), so the HTML backend cannot emit ill-formed markup.

## Pipeline

```
Deck : Free SlideC ⊤
   │  fold with the reveal.js algebra      (Container.Interpret)
   ▼
Forest of XMLDoc  ──wrap: <html><head>…</head><body><div class="reveal"><div class="slides">…
   │  printXML                             (parsnip, proved round trip)
   ▼
List Char ──► String ──► out/index.html    (+ "<!DOCTYPE html>" prefix in Main)

Config : JSON ──printJSON (parsnip)──► out/init.js = "Reveal.initialize(" ++ … ++ ");"
```

- A **backend is an algebra** `⟦SlideC⟧ T ⟶ T` for a carrier setoid `T` built from `XMLSetoid` (see R2). Rendering is `fold`; the fusion/hom lemmas in `Container.Interpret` give theme and rewrite correctness.
- The exported text is faithful: for the rendered document `d`, `parse (print d) ≈ₓ d` by `xmlStage` / `parseXML-printXML`.
- parsnip's theorem does **not** cover that `render` produces the intended document; that is a structural property proved by induction over decks (e.g. one `<section>` per `slide`, in order). Track these as backend lemmas.
- The reveal.js configuration is a JSON value printed by parsnip's verified JSON printer, written to a separate `init.js`, which avoids inline `<script>` content (see R1).

## reveal.js target (what the algebra must produce)

reveal.js expects `<div class="reveal"><div class="slides"><section>…</section>…</div></div>`, then its scripts and `Reveal.initialize({…})`. Mapping from the slide vocabulary:

| Slide command | reveal.js markup |
| --- | --- |
| `slide` | `<section>` |
| `section` (vertical stack) | `<section>` containing nested `<section>`s |
| `heading`, `paragraph`, `bullets` | `h1`–`h3`, `p`, `ul`/`li` |
| `pause` / incremental step | `class="fragment"` (optionally `data-fragment-index`, fragment style classes) |
| `notes` | `<aside class="notes">` (notes plugin) |
| `code` | `<pre><code class="language-…">` (highlight plugin) |
| `inlineMath` / `displayMath` | LaTeX text with the plugin's delimiters (`\(…\)`, `$$…$$`); XML escaping of `&`, `<`, `>` round-trips through the browser's text decoding, so the math plugin sees the original text |
| `figure` | `<img src>` or inline SVG (`Data.SVG`), with caption |
| `columns` | flex/grid `div`s with CSS classes from our stylesheet |
| backgrounds, transitions | `data-background-*`, `data-transition` attributes (parsnip names allow `data-*`) |
| theme | stylesheet link (`reveal.css` plus theme) chosen by a `Theme`/`RevealConfig` record |

Delivery layout: `out/index.html`, `out/init.js`, our `slides.css`, and a base URL or path for the reveal.js distribution (`RevealConfig.base`, default relative `reveal.js/`; a CDN URL also works). Decide vendoring vs CDN in R0; offline talks want a local copy.

## Work items (in priority order)

### R0 — Spike: a hand-built reveal.js deck through parsnip (done)

**Result** (`src/Slides/Spike/Reveal.agda`, `make spike REVEAL=<path to reveal.js>`; reveal.js 6.0.2 and headless Google Chrome, DOM inspected after load):
- reveal.js initialised (`ready`), with the notes and math plugins loaded from `<script src="…"> </script>` tags carrying a single space; `init.js` loaded the same way.
- Fragments (3), the nested vertical stack, the speaker-notes `aside`, and KaTeX-rendered math (`\( … \)`) all worked.
- Escaped text (`&lt;`, `&amp;`, `&gt;`) reached the DOM as the original characters.
- **The self-closing gap is real:** `<div id="unpadded" />` swallowed the following siblings (the paragraph and the next div became its children), while the padded `<div id="padded"> </div>` behaved. So the padding policy in R1 works and is required.
- `<meta … />` and `<link … />` (void elements) are fine as printed.

Original task:
- Write a few lines of Agda that build the minimal reveal.js page as an `XMLM` value (using `node`/`leaf`/`parent` and `Data.XML.Sanitize`), print it with `renderXML`, and open it in a browser with reveal.js alongside. No slide DSL needed.
- This settles the HTML5-vs-XML gaps below with evidence, before any backend design depends on them. Include one fragment, one nested section, one notes aside, and one math expression.

### R1 — HTML5 vs XML gaps (policy decided by R0: pad empty non-void elements)
- **Self-closing elements.** An element with no content prints as `<div/>`. HTML5 only honours this for void elements; `<script src="…"/>` and `<div/>` are wrong in `text/html`, and the AST cannot distinguish `<div/>` from `<div></div>`. Decided policy (confirmed by R0): an `html` smart-constructor layer that knows the void elements (`meta`, `link`, `img`, `br`, `hr`, `input`) and pads every other empty element with a single-space text slot (`<script src="…"> </script>` is valid; inline content is ignored when `src` is present). Prove the padding changes nothing except that slot. Alternatives: serve XHTML (reveal.js under `application/xhtml+xml` is unverified), or later a custom printer reusing `Data.Stage`.
- **Doctype.** No doctype node in the AST, so `<!DOCTYPE html>` is a constant prefix added in `Main`, outside the verified printer. State this in the docs.
- **Inline `<script>`/`<style>`.** Text is XML-escaped (`&`, `<`, `>`), which would corrupt inline JavaScript/CSS. Policy: no inline script or style; `init.js` and CSS are separate files (config via the JSON printer).
- **Entities and names.** Only the five XML entities; write other characters as UTF-8. parsnip names are ASCII `[A-Za-z_:][A-Za-z0-9_:.-]*`, which covers `data-*` and `aria-*`.
- **Payload type.** parsnip uses `List Char`; slide text is `String` converted one way at the boundary.

### R2 — Carrier and bridge lemmas (`Slides.Backend.XML`)
- Carrier: **forest** `T = List XMLDoc` with pointwise `_≈ₓ_` (recommended), or XML trees with holes (`XMLM X`) if Kleisli-style composition proves more natural.
- Relate `Container.FreeMonad.Eq` on `Free₀ XMLC ⊥ˢ` with parsnip's `_≈ₓ_` (both require equal shapes with arity transport and pairwise-equal children, so they should be equivalent) so generic fold lemmas apply to parsnip's equality.
- `wrap : T → XMLDoc` building the page shell.

### R3 — The reveal.js algebra for the core vocabulary
- Algebra for the minimal vocabulary (`slide`, `section`, `heading`, `paragraph`, `bullets`, `pause`, `notes`, `code`, math, `figure`, `columns`, backgrounds).
- Literal tags use `node`/`leaf`; runtime strings go through `Data.XML.Sanitize`; empties go through the R1 smart constructors.
- `renderReveal : Deck → String` and `revealConfig : RevealConfig → JSON`.
- Structural lemmas: number of top-level `<section>` elements equals the number of top-level slide commands, etc.

### R4 — Driver and tests
- `Main.agda` (MAlonzo) writes `out/index.html`, `out/init.js`, and copies or links the stylesheet.
- Golden-file tests on the example decks; a runtime check that `parseXML` on the output yields a document `≈ₓ` to the rendered one (the specification is `parseXML-printXML`).
- Optional `make test-browser`: load the deck in headless Chromium and check that reveal.js initialises and the slide count matches.

### R5 — Plain standalone HTML (Phase 4)
- Same XML pipeline with the reveal.js specifics replaced by a small built-in navigation script (external file) and print stylesheet. Share the algebra's vocabulary mapping by writing the common part once (a natural transformation between backend functors or a shared base algebra parameterised by tag/class choices).

### R6 — Figures and data (Phase 5)
- Inline SVG via `Data.SVG` for plots and diagrams (the plot DSL compiles to `XMLM`); SVG is XML, so it inherits the round trip.
- Chart or table data as JSON via `Data.JSON`.

## Acceptance
- A realistic example deck (title slide, bullets with fragments, a vertical section, notes, code, and an equation) renders to a directory that opens and runs in a browser with reveal.js.
- Golden tests pass and the parse-back check holds; `make check` passes from a fresh recursive clone.
