# Design

How the library is put together, and why. `docs/Authoring.md` is the command
reference; `plan/Plan.md` lists what is still open.

## The idea

A deck, and every diagram in it, is a *program* in a free monad over a
container. A container `C = (Shape ▷ Position)` describes one command: `Shape` is
the command with its arguments, `Position s` is what the command hands to its
continuation (nothing for a leaf, `Fin 2` for a command with two children).
`C ⋆ X` (stdlib `Data.Container.FreeMonad`) is the type of programs; a closed
program is `C ⋆ ⊥`. A **backend is an algebra** `⟦C⟧ A → A`, and rendering is
`fold`, the unique algebra homomorphism out of the initial algebra. Syntax and
backends are independent: adding a backend never touches a deck.

Library modules are `--safe --without-K` (each carries its own pragma);
only executables (`*Main`, `Spike`) drop `--safe` to use IO. The `Container.*`
namespace never imports `Slides.*`, so it could be split out as its own library.

## The generic part: `Container.*`

Proved with agda-categories (commit `c2e7c13e`) and stdlib 2.3, on `Setoids`, so
that equalities of continuations need no function extensionality:

| Module | What it gives |
|---|---|
| `Container.Polynomial` | `⟦C⟧` as an endofunctor on `Setoids` |
| `Container.Polynomial.Morphism` | container morphisms are natural transformations; identity and composition are preserved |
| `Container.FreeMonad` | `Free C` is a `Monad` on `Setoids`; tree equality is by recursion, not an inductive family (an indexed family would live in a universe that depends on the carrier level) |
| `Container.FreeMonad.Algebraic` | the forgetful functor from `F-Algebras ⟦C⟧`, `Free C X` as a `FreeObject`, the adjunction `Free ⊣ Forget`, and its monad is isomorphic to `Free C` (key lemma: `fold-bind`) |
| `Container.FreeMonad.Monadic` | that adjunction is monadic: `⟦C⟧`-algebras (backends) are exactly the Eilenberg–Moore algebras of the free monad |
| `Container.Interpret` | `Free C ⊥` is the initial algebra (Lambek); folds commute with algebra homomorphisms; fusion (translating along a container morphism, then folding, is folding with the pulled-back algebra) |
| `Container.Sum` | `⟦C₁ ⊎ C₂⟧ A ≅ ⟦C₁⟧ A ⊎ ⟦C₂⟧ A`, and `copair` of algebras with its universal property: this is how backends for separate vocabularies combine |
| `Container.Lowering`, `Container.Category` | a *lowering* sends each command to a program (a Kleisli map between containers); `lower`, `_>=>_`, the category of containers and lowerings, and `lower-fusion` |

Not done: fullness and faithfulness of `Poly-⇒`, and naturality of the sum
isomorphism in the setoid argument (neither is needed so far).

## Slides: `Slides.*`

**Stratified, not nested through positions.** The shape of a `slide` command
contains the slide's content program (`Body = ContentC ⋆ ⊤`), and `stack` (a
vertical stack) contains a list of bodies. No container mentions itself, so strict
positivity is not an issue, and `do`-notation works at every level. The
alternative, one position for the body and one for the rest, is wrong: `>>=`
would substitute the continuation into the body's leaves too. Consequence: a
backend is a family of algebras, one per stratum, whose `slide` and `stack`
handlers fold the content algebra over the body they contain. Further strata
(columns, boxes) combine with `⊎`.

**`pause`.** `Slides.Steps.steps` elaborates a body into a pause-free one: after a
`pause`, content commands become `fragment`s and other layout commands
`stepped`; `notes` are left alone. The mode flows through sequencing and
`go-bind` proves how (`go m (b₁ >> b₂)` elaborates `b₂` in the mode `after m b₁`),
so a pause in one component affects what follows. Both backends apply it to each
slide body.

**Authoring conveniences.** A string literal at type `Text` or `Inline` is plain
text (the user's module needs `fromString` and the instance `tt : ⊤` in scope;
`Slides.DSL` re-exports both). `Slides.Math` is a formula AST printed to LaTeX
with every argument of `\frac`, `^`, `_`, `\sqrt` braced (literals: `2` is a
number, `"x"` an identifier; not proved: balanced braces, true by construction).
`Slides.Resources` makes `figure` and `cite` take an instance argument that is `⊤`
when the name was declared and an error naming the resource otherwise, so a typo
fails to typecheck (`make test-negative`); `make check-resources` checks the
declared figures exist on disk.

**No instance search in the core.** An earlier design indexed decks by a
capability type (`Deck (Placed ⊕ Diagram)`) with the injection `S ⊑ K` found by
instance search. Finding `Placed ⊑ (Placed ⊕ Diagram)` needs overlapping
instances (`--backtracking-instance-search`), and then `do`-notation's `RawMonad`
instance search interacts with the pending goals and typechecking is
exponential: two `placed` commands in one block took more than two minutes, the
showcase deck over 14 minutes. So features (`placed`, `diagram`) are ordinary
layout commands, decks have one type `Deck`, and sequencing is the free monad's
own `_>>=_`. A backend that cannot render a feature natively either lowers it
(a `Lowering`; `Slides.Lower` has `stripNotes`, `diagramPlaceholder` and
`lowerDeck`) or refuses; refusing needs `supports : Feature → Bool` and
`uses : Deck → List Feature`, not built until a backend lacks a feature.

## HTML: `Slides.Backend.*`

Backends build on [parsnip](https://github.com/cspollard/parsnip) (submodule): its
XML AST is itself a free monad over a container (`XMLC`, `XMLDoc = XMLC ⋆ ⊥`), so
everything above applies to it. Documents are well-formed by construction
(validity evidence is in the node shapes), runtime strings go through
`Data.XML.Sanitize`, and `parse (print d) ≈ₓ d` (`xmlStage`). That theorem says the
text is faithful to the document, not that the document is the intended one;
structural lemmas about the renderer are proved by induction over decks.

```
Deck ── fold (backend algebra) ──► forest of XMLDoc ── wrap ──► printXML ──► index.html
Config : JSON ── printJSON ──► init.js
```

The carrier is a forest `List XMLDoc` under pointwise `_≈ₓ_` (`Slides.Backend.Reveal`).
Mapping: `slide` → `<section>`, vertical `section` → nested `<section>`, `pause` →
`class="fragment"`, `notes` → `<aside class="notes">`, `code` → `<pre><code>`, math
→ the math plugin's delimiters (XML escaping round-trips through the browser).

Policies settled by the R0 spike (a hand-built reveal.js deck in headless
Chrome, `Slides.Spike.Reveal`):

- **Self-closing tags.** parsnip prints an empty element as `<div/>`, and in
  `text/html` that swallows the following siblings. So the `html` constructor layer
  knows the void elements (`meta link img br hr input`) and pads every other empty
  element with one space (`<script src="…"> </script>`).
- **Doctype** is a constant prefix added in `Slides.Driver`, outside the printer.
- **No inline `<script>` or `<style>`:** text is XML-escaped, which would corrupt
  them. The reveal.js configuration is JSON in `init.js`; stylesheets are files.
- Only the five XML entities (other characters are UTF-8), and ASCII names, which
  cover `data-*` and `aria-*`.

`Slides.Diagram` is a typed AST of vector elements printed as inline SVG with
`Data.SVG` (`Slides.Backend.Diagram`); arrowhead ids derive from the diagram's name,
which must be unique in the deck. `placed x y w h c` uses whole percentages and
`position: fixed`, whose containing block is the transformed reveal.js canvas.

## Diagrams: `Slides.Diagram.*`

One container `DiagramC S = Op S ▷ arity` over a scalar `S`, `Dia S = DiagramC S ⋆ ⊥`,
`Algebra S A = (o : Op S) → (arity o → A) → A`, and `fold`. Interpretations:
`layoutAlgebra` into `Layout S` (the renderer; `compile` then gives a `Diagram`),
`namesAlgebra` into `Usage` (`dangling`), and `sizeAlgebra` (for proofs). The
details, the scalar interface, half units, and the laws proved over a setoid are in
`docs/Authoring.md` ("Laying diagrams out", "Scalars, half units and laws").

Decisions that shaped it:

- **One signature, not three layers.** Primitives, connectives and annotations are
  all operations of `Op S`; `arity` says how many children. Gaps, margins, minimum
  widths and top-alignment are spacers, so they are built from `Beside`, `Above`,
  `Atop` in `Slides.Diagram.Notation`, not operations, and the monoid laws have no
  gap parameter. `LabelAbove`/`LabelBelow` stay operations: their spacer is as tall
  as the caption's laid-out height.
- **Scalar in the syntax.** `Dia S` carries sizes of type `S` (decks use ℕ), so
  `mapDia` changes the scalar (`PairsScalar` checks that ℕ, ℤ and ℚ lay the Pairs
  diagrams out identically). A general naturality theorem is false as stated:
  `intOps` floors percent ports, so ℤ→ℚ is not an `Ops` homomorphism, and ℕ→ℤ breaks
  on monus. A provable form is the fusion lemma for `mapDia` plus a per-operation
  homomorphism check.
- **Half-unit positions** make centring exact in ℤ (`outer - inner`, no division);
  they are halved once, in `toElement`. This is why `Draw S` and the ℕ `Element`
  are different types: they are in different units, and `Showcase` writes `Element`s
  by hand.
- **ℕ is a first-class scalar** that runs the layout but is not covered by the
  ring-law proofs (monus only ever takes a larger minuend).
- **Equality is the scalar's own** (`IsLawful` takes a stdlib `IsCommutativeRing _≈_`
  plus a maximum), not `_≡_`, so a constructive real would be a scalar too.
- **`Names` are scoped per `connect`**: a `connect` resolves against the names declared
  inside its own diagram, which is what makes `NamesSound` true.
- **No escape hatch.** `Raw` (elements in final coordinates) was unused and the one
  operation outside the translation law; it was removed.
- **Stdlib has no ordered ring** (checked at `8326c7475`): no `IsOrderedRing`,
  ordered field or `sqrt` for ℕ. `Nonneg x` is `0# ⊔ x ≈ x`, the join-semilattice order.
- **`Valid` is preserved by every operation** (`Slides.Diagram.Valid`), given an `IsOrdered`
  record on the scalar (sum keeps non-negativity, `fromℕ` is non-negative, `⊔` idempotent;
  ℤ and ℚ have it). A term is valid when its sized leaves are (`WellSized`; a negative
  rectangle is not, so the hypothesis cannot be dropped). The same module proves the
  combinators congruent for `≈ᴸ`, `↔ m ∥ ↔ n ≈ ↔ (m + n)`, the associativity and unit laws
  on `Dia` terms, and `margin 0 0 0 0 d ≈ d`.

## Animations: `Slides.Anim.*`

The same pattern again. `AnimC = Seq | Par` (two children each) is a container and
`Anim S T = AnimC ⋆ T` its free monad, with leaves `Seg S`: a track of a parameter
(`Slides.Anim.Track`, itself the free monad on `Seq` over pieces with easings) and a
diagram as a function of that parameter. `dur`, `footprint` and `timeline` are algebras
(`foldA`); `foldA` is the generic fold (`Slides.Anim.Generic`), and `foldA-bind` is its
fusion with `>>=` (a tween is a bind). Laws are proved at the level they are true at:
the swap law and `merge` on lists of frames (`Timeline`), `footprint` up to permutation,
`atop` commutative up to permutation of draws (`Slides.Diagram.Commute`), laid-out `Par`
associative and padding invisible on valid frames (`Slides.Anim.Laws`), tracks
associative, and reversible, sampled exactly, for `Linear`, `Step` and `StepStart` pieces (`Track`; `Bezier` is approximate). Time is whole ticks;
the backend plays frames on a timer, an act per reveal step, or, for `Play = looping`,
cyclically (`phase n t = t mod n`, periodic and equal to the timeline on its first period:
`Slides.Anim.Loop`; the player's `i ↦ (i+1) mod n` is proved to track it). Looping is a play
mode of a finished timeline, not a term constructor: a loop has no `dur` in `(ℕ, +, max)`.
Steps and loop combine as a product: `both rests p` lays `p` phases of the steps end to end,
frame `i + φ * n` (`index`, in range and recovering the step by `mod n`), and `renderBoth`
checks by computation that every phase has acts of the same lengths. Design and open items:
`plan/Animations.md`.

## Tests and build time

`make check` typechecks every library module in one Agda process
(`_build/Everything.agda`); executables share one compile directory (`_build/ghc`,
`GHCFLAGS=-O1` to optimise), so the translated library is compiled once. `make test`
diffs the rendered decks against `tests/golden`; `make test-browser`,
`make test-playwright` and `node tests/browser/pairs.mjs out pairs` drive them in a
browser; `make test-negative` checks that decks with typos are rejected;
`make showcase pairs talk plain` regenerate the outputs.
