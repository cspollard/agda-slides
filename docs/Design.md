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
| `Container.FreeMonad.Properties.Monadic` | that adjunction is monadic: `⟦C⟧`-algebras (backends) are exactly the Eilenberg–Moore algebras of the free monad |
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
(a `Lowering`; `Slides.Lower` has `stripNotes`, `diagramPlaceholder`,
`animationFinal` and `lowerDeck`) or refuses; refusing needs `supports : Feature → Bool` and
`uses : Deck → List Feature`, not built until a backend lacks a feature.

*Animations across backends.* `renderAnimation` (a flipbook of frames with `data-*`
attributes) is shared by the reveal.js and standalone backends, and both load the
one player, `assets/animation.js` (a few lines of glue each: which slide is shown, when a
fragment appears; it also shows the last step when printing). A backend that cannot play them lowers
the command with `animationFinal`, which replaces an animation by a still of the frame
it rests on once all steps have played (`finalFrame`: the last rest, the first frame for
a loop), or with `diagramPlaceholder`, which drops it to a one-line placeholder.

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
  `mapDia` changes the scalar (`Examples.Pairs.Properties` checks that ℕ, ℤ and ℚ lay the Pairs
  diagrams out identically). A naturality theorem needs the map to be an `Ops`
  homomorphism (`IsOpsHom`): `intOps` floors percent ports, so ℤ→ℚ is not one, and ℕ→ℤ
  breaks on monus. For a homomorphism it is proved, `mapLayout h (layout d) ≡ layout
  (mapDia h d)` (`Slides.Diagram.Layout.Properties`), and the evaluation of the free
  scalar `Slides.Diagram.Expr` into ℕ is one. The earlier provable parts are in `Slides.Diagram.Syntax.Properties.MapFusion`: `mapDia f` is
  translation along a container morphism, so it is functorial (up to equality of programs)
  and folding after it is folding with the pulled-back algebra (`fold-mapDia`), for any
  renderer with congruent handlers. Transporting a *layout* along `f` additionally needs a
  per-operation homomorphism check (`⊔`, centring, percent ports).
- **Half-unit positions** make centring exact in ℤ (`outer - inner`, no division);
  they are halved once, in `toElement`. This is why `Draw S` and the ℕ `Element`
  are different types: they are in different units, and `Showcase` writes `Element`s
  by hand.
- **ℕ is a first-class scalar** that runs the layout but is not covered by the
  ring-law proofs (monus only ever takes a larger minuend).
- **Equality is the scalar's own** (`IsLawful` takes a stdlib `IsCommutativeRing _≈_`
  plus a maximum), not `_≡_`, so a constructive real would be a scalar too.
- **`Names` are scoped per `connect`**: a `connect` resolves against the names declared
  inside its own diagram, which is what makes `Names.Properties.Soundness` true.
- **No escape hatch.** `Raw` (elements in final coordinates) was unused and the one
  operation outside the translation law; it was removed.
- **Stdlib has no ordered ring** (checked at `8326c7475`): no `IsOrderedRing`,
  ordered field or `sqrt` for ℕ. `Nonneg x` is `0# ⊔ x ≈ x`, the join-semilattice order.
- **`Valid` is preserved by every operation** (`Slides.Diagram.Place.Properties.Valid`), given an `IsOrdered`
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
(`foldA`); `foldA` is the generic fold (`Slides.Anim.Syntax.Properties.Generic`), and `foldA-bind` is its
fusion with `>>=` (a tween is a bind). Laws are proved at the level they are true at:
the swap law and `merge` on lists of frames (`Timeline`), `footprint` up to permutation,
`atop` commutative up to permutation of draws (`Slides.Diagram.Place.Properties.Commute`), laid-out `Par`
associative and padding invisible on valid frames (`Slides.Anim.Syntax.Properties.Laws`), tracks
associative, and reversible, sampled exactly, for `Linear`, `Step` and `StepStart` pieces (`Track`; `Bezier` is approximate), and so are whole tracks whose pieces meet (`reverse-sample`: tick `k` reversed is tick `dur - k`, exactly). Time is whole ticks;
the backend plays frames on a timer, an act per reveal step, or, for `Play = looping`,
cyclically (`phase n t = t mod n`, periodic and equal to the timeline on its first period:
`Slides.Anim.Loop`; the player's `i ↦ (i+1) mod n` is proved to track it). Looping is a play
mode of a finished timeline, not a term constructor: a loop has no `dur` in `(ℕ, +, max)`.
Frames are shipped as the first frame and an edit from each frame to the next
(`Slides.Diagram.Delta`: an edit changes nothing, only an element's numbers (as differences from the old ones, trailing zeros dropped), or the element, or
edits a group member by member; `patchL (diffL old new) old ≡ new` and `replay e (deltas e fs) ≡ fs`
are proved, the checking of "only the numbers changed" being done by the diff itself), so the page
holds one SVG and a JSON list of edits; the player rebuilds frame `k` from the first (a frame behind
the current one is rebuilt from the start). The Pairs deck went from 1.47 MB to 0.24 MB. `tests/browser/anim-ref.mjs` checks every frame the page rebuilds against the frame Agda computes (`make test-anim-ref`).
*Templates.* A segment's body is `SegBody S`: a function (`blackBox`, a flipbook) or a
`template`, an open diagram `Dia (Expr ⊤)` whose sizes are formulas in the parameter `t`.
`Expr V` is the free `Ops`-algebra over variables, a free monad on a container (`evalWith`
is its fold, a homomorphism by construction; `bodyAt` evaluates a template in any scalar
`Ops S`). When every segment of an animation is a template, `Slides.Anim.Param` numbers the
segments (one variable each, so segments in `Par` keep independent parameters), lays the
frames out once in `Expr ℕ` and the backend ships a *simulator* (`data-param`): each segment's
track as pieces `[ticks, from, to, easing]`, and phases of ticks sharing a shape, each element's
numbers as formulas (closed subformulas evaluated when exact). The page plays in *continuous
time*: at the real time `τ` (ticks; `requestAnimationFrame`, one tick per `data-ms`) it
evaluates the easings in floats, the formulas in floating point without rounding, and sets
fractional coordinates; its size does not depend on the number of ticks. The specification is
`Slides.Anim.Continuous`: `sampleAt` is the track algebra into `ℕ × (ℚ → A)` (right-continuous
pieces, `Seq` offsets time, `Par` the same `τ`), a template's parameter is a ℚ (`Expr` is
unchanged, evaluated with `evalWith ratOps`; no floor operation), `frameAt` the layout in ℚ.
ℚ differs from the discrete reading: `-` is real subtraction (negative sizes are outside
`Valid`), percentages are exact, the parameter is not floored. `sampleAt-ι` (whole ticks
agree with `Track.sample`), `leaf-tick` (the continuous frame is the discrete one through
`ι` when the template is `Faithful`, `Slides.Diagram.Expr.Properties.Faithful`), and the time laws are proved;
the JavaScript is tested against exact ℚ values (`make test-anim-ref`, tolerance 0.01 for
float easings, 1e-9 at piece boundaries). Layout is natural along an `Ops`-homomorphism, so the
evaluated symbolic layout is the layout of the instance (`layout-natural`, `layout-eval`,
`layout-substWith`, `leaf-agrees`). The assembly over a whole timeline is
proved: `Slides.Anim.Assembly.Leaf` (one generic induction over the language of the template
numbers, `assembly`), instantiated by `Slides.Anim.Param.Properties` (`discrete-assembly`,
`paramOf-assembly`: the shipped
symbolic layout of tick `k`, evaluated at the parameters of the segments running at `k`, is
the layout of the frame `render` shows; the induction reads lists of frames as partial
functions of the tick, `++` and `merge` becoming the algebra of `Continuous`);
`Slides.Anim.Assembly.Continuous` (`frameAt-assembly`: at whole ticks `frameAt` is the discrete
frame through `ι`, given `leaf-tick`'s exactness hypotheses for the segments running there;
`atop` commutes with `ι` with no hypothesis, `Slides.Diagram.Place.Properties.Atop`);
`Slides.Anim.Formula.Properties` and `Slides.Anim.Phases.Properties` (the shipped formulas, with closed
subformulas folded, mean the coordinates in ℚ, and grouping ticks into phases changes no
frame: `pageFrame-sem`, proved once for any reading in `Over` and instantiated at ℚ and ℕ in
`Slides.Anim.DPhases.Properties`). The data and encoders the backend runs (`Formula`, `Phases`,
`DPhases`, `Share`, `SharePhases`) are separate modules from these proofs, so that a
deck executable does not load the proofs. What is only tested: frames between whole ticks, the printing of the
phases as JSON and its reading by the player (attribute order, float arithmetic).
*Layered scalars and discrete templates.* The scalar signature is a sum of containers
(`Slides.Diagram.Signature`, `Expr`): `CoreC` (zero, literal, plus, max, `pct p`) `⊎` `SubC`
(`sub`: monus in ℕ, real subtraction in ℤ/ℚ, so `ι : ℕ → ℚ` preserves the core layer but the
difference only where `b ≤ a`). `Ops = CoreOps + SubOps`, `IsOpsHom = IsCoreHom + IsSubHom`;
`evalWith` is the fold of the copairing of the layers' handlers (`Handler`, `_⊕_`, which is
`Container.Sum.copair`); weakening a layer is translation along `inl`/`inr`, a monad
morphism; `Faithful` is exactly the conjunction of the per-layer side conditions
(`CoreSide`, `SubSide`). A further layer, `Slides.Diagram.Euclid` (`DivBy`, `ModBy`, `Lt`,
`MulLit`), is read in ℕ only (floor division is not exact division) and gives `DExpr`, the
*discrete templates*: `SegBody.discrete` bodies are evaluated in ℕ at the whole tick
(`evalD natD`), have one frame per tick (the frame of `⌊τ⌋` between ticks) and are shipped
as formulas read in ℕ (`"d": 1` in `data-param`; `Formula.encD`, whose folds need no exactness
condition: `encD-semN`, `enc-numN`). Layout never compares or divides, so it is natural along
`evalD` unchanged (`Diagram.Euclid.Properties.Layout`); `Anim.DParam.Properties.discrete-assemblyD` is the assembly
(an instance of `Slides.Anim.Assembly.Leaf`), `Anim.DPhases.Properties.pageFrameD-sem` the shipped phases. A
field layer (exact division by a literal) was not needed. The hero frame is written once over
any scalar with the three layers (`PairsHero.Frame`); `heroT-correct` proves the template is
the flipbook frame, and the Pairs deck's two hero loops are `heroD 26 seed`.
*Compact formulas.* The first discrete hero was unusable (3 pairs shipped 779,366 characters
of formulas, 26 pairs ran over four CPU minutes): each pair sat on a layer of the canvas's
size by margins with a *complement* (`W ∸ (x + 2r)`, not closed in the tick), `atop` centred
a layer against the running maximum of the widths of all later layers, so every coordinate
contained a copy of that chain (about `n³` nodes in all; measured 123 KB for one pair,
340 KB for two, 779 KB for three, 1.08 MB for four, 149 s to lay out 8). Two changes, with
their measurements (26 pairs, phases of `data-param`): *(a) absolute placement*: `Place`
(a child at `(x, y)` of a frame of declared size) and `Overlay` (two children at the corner
of a declared frame) are `Dia` primitives with layout operations in `Place`, naturality along
any `Ops`-hom (`Diagram.Layout.Properties`), names, size and validity laws; the hero frame is an
overlay of placed dots, so a coordinate is the pair's own formula: linear, 247,547 characters
unshared, 7 s. *(b) sharing*: the formulas of a phase are value-numbered into a straight-line
program (`Slides.Anim.Share`: a store of definitions, each over the parameters and the earlier
ones, hash-consed through an AVL memo that is only a hint, checked before use), and the
numbers of the elements are nodes over it (`SharePhases`); the page evaluates the definitions
once per time step, in order, then the numbers. 1,004 definitions for 26 pairs, 18,849
characters of phases (against 42,732 of edits), the Pairs page 240,278 to 188,951 bytes (each loop 16.9 KB of `data-param`, 25 KB with its markup, against 51 KB as edits); the layout and compile of the deck take about 10 s. Mathematically the
program is a Kleisli family and its meaning the evaluation of the tree obtained by
substitution: `Anim.Share.Properties.unfold-sound` (`sem (unfold ds i) ρ ≡ env ρ ds i`, by induction on the
store, the law `evalWith-subst` for the shipped syntax), `share-unfold` (the unfolding of the
shared reference of `g` evaluates equal to `g`, every assignment), and `share-impl`,
`output-realises` (the shared output reads as the formula, for every reading `Reading` with a
`Semantics`: instances at ℚ and ℕ), chained through traversals by stability along store
extensions (`Realises`, `Stable`); `Anim.SharePhases.Properties.pageFrameS-sem` is that sharing changes no
frame the page draws, with `zeroBase-sem` for the base numbers a formula overwrites (shipped as
0 so that equal strings are shipped once). Not adopted: simplifying `a + 0` in the encoder (the
overlay hero has no zero shifts) and inlining single-use definitions (about 16% of the
program). Only tested: the JSON printing and the page's evaluation of the program.
Steps and loop combine as a product: `both rests p` lays `p` phases of the steps end to end,
frame `i + φ * n` (`index`, in range and recovering the step by `mod n`), and `renderBoth`
checks by computation that every phase has acts of the same lengths. Design and open items:
`plan/Animations.md`.

## Module conventions

Proofs about `X` live in `X.Properties` (the standard library's `Data.List.Base` against
`Data.List.Properties`). `X` keeps the types, records, functions and instances, and
everything whose *definition* needs a proof (a field of a record, a retraction behind a
decidable equality, the `True` witnesses the DSL uses); lemmas, theorems and proof-only
definitions (relations used only to state laws) go to `X.Properties`. Where a function
needs a lemma to typecheck, the minimal helper stays private in `X`.

* One `X.Properties` per module `X` (file `X/Properties.agda` next to `X.agda`). A larger or
  separate development about `X` is a topic module `X.Properties.<Topic>` (for example
  `Slides.Diagram.Place.Properties.Laws`, `.Commute`, `.Valid`, `.Atop`;
  `Slides.Anim.Syntax.Properties.Laws`, `.Generic`); topic modules may import `X.Properties`.
  There is no re-exporting umbrella module.
* A proof module that is parametrised (by a scalar, say) cannot also hold scalar-free lemmas,
  so the parametrised one is the topic (`Names.Properties.Soundness`) and `Names.Properties`
  holds the rest.
* Theory modules that define their own vocabulary (`Slides.Anim.Assembly` and its `Leaf` and
  `Continuous` parts, `Anim.Nth`, `Anim.Arith`, `Anim.Loop`, `Diagram.Equality`, the categorical
  `Container.Category`, `Container.Lowering.Category`) keep their names; their headers say so,
  and no executable imports them.
* Rule: no executable (`*Main`) imports a `.Properties` module or a theory module, so a deck
  compiles and typechecks only declarations and functions. `tests/check_closure.py` (part of
  `make test`) walks the import closure of every `*Main` and fails otherwise; `make check`
  still typechecks everything. Theorem statements and names are unchanged by a move; only
  the module changes.
* What could not be separated: the categorical objects of `Container.*` whose definition is
  a proof (`Free₀` and its equivalence, `Alg`: the free algebra, `fold`, `FreeObj`, the
  `Poly` functor and its morphisms) stay with their definitions; the backends fold with them.

## Tests and build time

`make check` typechecks every library module in one Agda process
(`_build/Everything.agda`); executables share one compile directory (`_build/ghc`,
`GHCFLAGS=-O1` to optimise), so the translated library is compiled once. `make test`
diffs the rendered decks against `tests/golden`; `make test-browser`,
`make test-playwright` and `node tests/browser/pairs.mjs out pairs` drive them in a
browser; `make test-negative` checks that decks with typos are rejected;
`make showcase pairs talk plain` regenerate the outputs.
