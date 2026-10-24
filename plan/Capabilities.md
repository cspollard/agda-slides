# Capabilities: backends with different feature sets

Goal: slide features beyond the core vocabulary (positioned elements, inline
diagrams, later animation, TikZ, …) are *optional*. A deck declares which it
uses, a backend declares which it supports, and a mismatch is a type error.

## Design

A **capability** is just the type of its command shapes (`K : Set`), with
container `capC K = K ▷ λ _ → ⊤`. (It is not a record: Agda cannot infer `K`
from `Body K` if `K` is hidden behind a projection such as `Shape K`.) How a
command appears on a later step (after a `pause`) is the `Steppable K`
instance (`later : K → K`); how an HTML backend renders it is the `HTMLCap K`
instance (`render : K → Forest`). Capabilities compose by `_⊕_` (the
disjoint sum, with componentwise instances); `NoCap = ⊥`.

The core vocabulary is unchanged (`BlockC = ContentC ⊎ LayoutC`). What a
deck may use is indexed by a capability `K`:

    BlockOf K = BlockC ⊎ capC K          Body K = BlockOf K ⋆ ⊤
    DeckC K   = DeckShape (Body K) ▷ ⊤   Deck K = DeckC K ⋆ ⊤

`DeckShape` becomes parametric in the type of bodies; nothing is recursive, so
the stratification (and strict positivity) is preserved. Content inside
`columns`/`box`/`placed` stays the plain `Content`.

Authoring: core commands are polymorphic in `K` (they inject along
`ContentC ⇒ BlockOf K`). A capability command takes an instance argument
`{{S ⊑ K}}` (data types à la carte): `placed : {{Placed ⊑ K}} → … → Body K`.
Instances: reflexivity, left and right injection into `⊕`; each capability may
appear once in a sum.

Backends: an HTML backend needs `HTMLCap K`, i.e. a function
`Shape K → Forest`, which determines an algebra for `capC K` (all positions
are `⊤`). The algebra for `BlockOf K` is `copair` of the core block algebra
and the capability algebra, exactly as `BlockC` is built today. Instances of
`HTMLCap` exist for `NoCap`, `⊕`, and each capability; render functions take
`{{HTMLCap K}}`, so a deck that uses a capability the backend does not
implement does not typecheck (`No instance of type HTMLCap …`).

**Degradation.** A backend without native support for a capability `S` may
instead give a shape map `S → S′` into capabilities it has (a container
morphism `capC S ⇒ capC S′`); `Container.Interpret.Translate.fusion` already
proves that translating and then folding equals folding with the pulled-back
algebra. Not built until a backend needs it (Beamer).

Non-goals: type-level capability lists, row polymorphism, subtyping inference.

## Stages (each committed separately; all tests green)

1. **Refactor, no new features (done).** `NoCap`, `Steppable`, `Body K`, `Deck K`,
   `HTMLCap`; thread `K` through DSL, Steps (`go`/`after`/`go-bind` get a
   capability case: apply `later` in step mode, mode unchanged), Common
   (`renderBody-bind` gets a third case), Reveal, Plain, Resources, Components,
   Driver, examples. Outputs byte-identical (golden tests unchanged).
2. **`placed` (done).** `Placed` capability: `placed x y w h Content` renders a
   `<div class="placed" style="left:…%; top:…%; …">` in slide-canvas
   coordinates, with `later` producing a fragment variant. Coordinates are
   whole percentages of the slide; the stylesheets use `position: fixed`, whose
   containing block is the transformed reveal.js canvas (or the window for the
   plain backend). Tests: golden, Playwright (position, fragment step).
3. **`Diagram`.** `rawSVG` (a string of SVG child markup validated by the XML
   parser at render time, or `XMLM` built with `Data.SVG`), then a small typed
   AST (rect, circle, path, text, arrow, group) printed with `Data.SVG`.
4. **Captions and numbering** for tables/figures, together with citation
   numbering (needs state threaded through the fold).
5. **Beamer backend**, with its capability instances and the first
   degradation (placed → flow box).

## Risks

- Instance search for `_∈_` with metas in `do` blocks: test in stage 2.
- Instances are only visible when their names are in scope, so `Slides.DSL` and
  `Slides.Driver` re-export the `Steppable`/`HTMLCap` instances.
- `go-bind`/`renderBody-bind` need one extra case each; same shape as the
  content case.
- Every example annotation `Deck`/`Body` becomes `Deck NoCap`/`Body NoCap`.
