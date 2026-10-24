# Plan: HTML production on top of parsnip

[parsnip](https://github.com/cspollard/parsnip) (git submodule at `parsnip/`) provides verified printers and parsers for XML (and JSON, and an SVG vocabulary). This plan describes how the HTML backend (Phase 3 of `plan/Plan.md`) and later backends use it.

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
   │  fold with the HTML algebra          (Container.Interpret, Phase 3)
   ▼
Forest of XMLDoc  ──wrap in <html>──►  XMLDoc
   │  printXML                            (parsnip, proved)
   ▼
List Char ──► String ──► file             (prefix "<!DOCTYPE html>" in Main)
```

- An **HTML backend is an algebra** `⟦SlideC⟧ T ⟶ T` for a carrier setoid `T` built from `XMLSetoid` (see "Carrier" below). Rendering is `fold`; the fusion/hom lemmas in `Container.Interpret` give theme and rewrite correctness for free.
- The exported text is faithful: for the rendered document `d`, `parse (print d) ≈ₓ d` by `xmlStage` / `parseXML-printXML`. Nothing is lost or ambiguous in printing (escaping, attribute order, mixed-content text).
- What parsnip's theorem does **not** cover: that `render` produces the intended document. That is a separate, structural property proved by induction over decks (for example, one `<section>` per `slide` command, in order). Track these as backend lemmas, not as consequences of the round trip.

## Work items

### H0 — Wiring (done)
- Submodule `parsnip/`; `agda-slides.agda-lib` has `include: src parsnip/src` (parsnip depends only on `standard-library`, so no extra library registration is needed).
- `Slides.Backend.XML` imports the parsnip modules above and instantiates the container machinery at `XMLC`.
- Clone with `git clone --recurse-submodules` or run `git submodule update --init`.
- Only modules we import get typechecked; parsnip's own full check stays in its repo (`parsnip/make-everything.sh`).

### H1 — Bridge lemmas (`Slides.Backend.XML`, small)
- Relate `Container.FreeMonad.Eq` on `Free₀ XMLC ⊥ˢ` with parsnip's `_≈ₓ_`. Both ask for equal shapes (with arity transport) and pairwise-equal children, so they should be logically equivalent; proving it lets generic fold lemmas apply to parsnip's equality.
- Show `XMLSetoid` carries an `⟦XMLC⟧`-algebra structure (the constructor `impure`), making `XMLDoc` the free algebra on `⊥` in the sense of `Container.FreeMonad.Algebraic`.

### H2 — Carrier for backends
Decide between two options (recommend (a)):
- (a) **Forest**: `T = List XMLDoc` with pointwise `_≈ₓ_` (a setoid). A slide command's handler concatenates or wraps forests; the final step wraps the forest in `<html><body>…`.
- (b) **Fragments with holes**: `T = XMLM X` (nodes with leaves in `X`); closer to Kleisli composition but needs more bookkeeping.
Deliverable: `Slides.Backend.HTML.Carrier` with the setoid, and `wrap : T → XMLDoc`.

### H3 — HTML algebra for the core vocabulary
- Algebra for `heading`, `paragraph`, `bullets`, `slide`, `columns`, `figure`, `pause` (as a class attribute), math (LaTeX text in a `span`/`div`), notes.
- Use `Data.XML.AST.node`/`leaf` where tags and text are literals (Agda solves the validity evidence by computation) and `Data.XML.Sanitize` constructors for runtime strings.
- Entry point `renderHTML : Deck → String` = `renderXML ∘ wrap ∘ fold`, with the `<!DOCTYPE html>` prefix added by `Main`.
- Structural lemmas about the rendered shape (e.g. number of `<section>` elements equals number of `slide` commands).

### H4 — HTML5 vs XML gaps (spike before committing to a design)
parsnip prints XML, and browsers parse HTML5 differently. Known points to settle with a spike and browser tests:
- **Self-closing elements.** An element with no content prints as `<div/>`. HTML5 only honours this for void elements; `<div/>` or `<script src="…"/>` is wrong in `text/html`. The AST cannot distinguish `<div/>` from `<div></div>`. Options: serve as XHTML (`.xhtml`, `application/xhtml+xml`), or have `Slides.Backend.HTML` use a smart constructor that adds a non-empty text slot to non-void elements that would otherwise be empty (and prove this does not change the intended content), or add our own HTML token printer later, reusing `Data.Stage` for its round-trip.
- **Doctype and XML prolog.** The AST has no doctype node, so the `<!DOCTYPE html>` prefix is added outside the verified printer (a constant string; state this explicitly).
- **Inline `<script>`/`<style>` content.** Text is XML-escaped (`&`, `<`, `>`), which breaks inline JavaScript/CSS. Keep scripts and styles in external files referenced by attribute, or add a verified CDATA/raw-text node later.
- **Entities.** Only the five XML entities round-trip; write other characters directly (UTF-8).
- **Names.** parsnip's names are ASCII `[A-Za-z_:][A-Za-z0-9_:.-]*`, which covers `data-*`, `aria-*`, and `xlink:href`.
- **Payload type.** parsnip uses `List Char`, not `String` (the `String ↔ List Char` round trip is not provable under `--safe`). Slide text can be `String` and converted at the boundary; the conversion is one-way for printing, so it does not need the round trip.

### H5 — Reveal.js and other XML-ish backends (Phase 4)
- Reveal.js markup is the same algebra with a different tag/attribute vocabulary (`section`, `class="fragment"`, `aside.notes`); implement it as a second algebra or as a natural transformation between the two backend functors, so that the shared structure is proved once.
- Reveal's configuration and any chart data can be emitted with `Data.JSON` (`jsonStage` gives the same round-trip guarantee).

### H6 — Figures (Phase 5)
- Inline SVG via `Data.SVG` for plots and diagrams (the plot DSL compiles to `XMLM`). SVG is already XML, so it inherits the round trip.
- External images are plain `img` elements with a path.

## Acceptance
- `renderHTML` on the example decks produces files whose `parseXML` yields a document `≈ₓ` to the one rendered (a runtime test using `parseXML-printXML` as the specification), and golden-file diffs pass.
- `make check` from a fresh recursive clone passes.
