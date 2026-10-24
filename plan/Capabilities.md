# Optional features and backends with different feature sets

Goal: features beyond the core vocabulary (positioned boxes, inline diagrams,
later animation, TikZ, …) must be usable in decks even though not every backend
can render every feature, and a mismatch must be detected rather than silently
dropped.

## Decision: ordinary vocabulary, no instances

Features are ordinary commands of `LayoutShape` (`placed`, `diagram`), the same
way `columns` and `box` are. Decks have the single type `Deck`; there is no
index of "required capabilities" and no instance search anywhere in the
capability machinery.

This replaces a first design, tried and abandoned (commits `15c968f` and
`516d33d`), in which decks were indexed by a capability type `K`
(`Deck (Placed ⊕ Diagram)`) with the injection `S ⊑ K` and the backend duties
(`Steppable K`, `HTMLCap K`) supplied by instance arguments. It worked with a
single capability, but:

- finding `Placed ⊑ (Placed ⊕ Diagram)` needs overlapping instances, which
  Agda only accepts with `--backtracking-instance-search`;
- with that flag, `do`-notation's `RawMonad` instance search interacts with the
  pending injection goals and typechecking becomes exponential: two `placed`
  commands in one `do` block took more than two minutes instead of a few
  seconds, and checking the showcase deck took over 14 minutes;
- every example needed a `NoCap` annotation and every instance had to be in
  scope by name.

`do`-notation itself now needs no instances either: sequencing is the free
monad's own `_>>=_`, which is generic in the container, so content, body and
deck programs all use it.

## Backends and unsupported features

A backend interprets every command (an algebra, as before). For a feature a
backend cannot render natively it chooses one of:

1. render it natively (reveal.js and plain HTML render `placed` and `diagram`);
2. **lower** it into commands it does support, a plain function on shapes
   (for example a Beamer backend lowering `placed` to a flowed box). If the
   lowering is a container morphism, `Container.Interpret.Translate.fusion`
   already proves that translating then folding equals folding with the
   pulled-back algebra;
3. refuse. For this a backend will export `supports : Feature → Bool`, and a
   function `uses : Deck → List Feature` (a fold over the deck) tells which
   features a deck needs; `Slides.Driver` checks `uses ⊆ supports` and aborts
   with the names of the unsupported features. Not built until a backend lacks
   a feature (Beamer).

## Stages

1. ~~Index decks by capabilities~~ (abandoned, see above).
2. **`placed`** (done): `placed x y w h content`, coordinates are whole
   percentages of the slide; the stylesheets use `position: fixed`, whose
   containing block is the transformed reveal.js canvas (or the window for the
   plain backend). After a `pause` it appears on a later step through the
   existing `stepped` wrapper.
3. **`diagram`** (done): typed AST `Slides.Diagram` (rect, circle, line, arrow,
   label, group; styles), printed as inline SVG with parsnip's `Data.SVG`
   (`Slides.Backend.Diagram`). Arrowhead ids are derived from the diagram's
   name, which must be unique in the deck.
4. Captions and numbering for tables/figures, with citation numbering (needs
   state threaded through the fold).
5. Beamer backend, with `supports`/`uses` and the first lowering
   (`placed` → flowed box, `diagram` → TikZ).

## Build time

Typechecking time matters: the instance-heavy design above was the main cause
of a 14-minute check. Other measures: `make check` runs one Agda process over
all library modules (`_build/Everything.agda`), and all executables share one
compile directory (`_build/ghc`, `-O0` by default; `GHCFLAGS=-O1` to optimise),
so the translated and GHC-compiled library is built once.
