# Text: one tree for prose and labels; line breaks, styles, nested bullets

Status: approved plan.  Phase 3 of `plan/TODO.md`.

## The problem

Two text languages: slide prose (`Deck.Content.Inline`: `text`, `codeSpan`, `emph`, `strong`,
`inlineMath`, `link`, `cite`, rendered to HTML by `Render.piece`) and diagram labels (a `String`
parsed by `Diagram.Markup` into `Seg`: `flat`, `sub`, `sup`, measured by `TextMetrics`, printed
by the SVG printer).  Every text feature would be added twice.

## The idea

Both are a tree of styled runs over string atoms: the free monad of one small container.  Put it
in one module below both users, `Slides.Text`:

```
data Inline : Set where
  text codeSpan : String → Inline
  emph strong   : List Inline → Inline
  sub sup       : List Inline → Inline
  styled        : TextStyle → List Inline → Inline
  br            : Inline
  inlineMath    : Math → Inline
  link          : String → List Inline → Inline
  cite          : String → Inline
```

Every consumer is a fold: HTML (`Render.piece`), plain text (`plainT`, the existing monoid
homomorphism to lines), SVG `<tspan>`s, and width (`TextMetrics`).  A construct a backend cannot
show degrades through `plain`.  The label markup `"x_{T}"` becomes one parser from `String` to
`List Inline`, applied once where a label is built; `Seg` disappears.

`TextStyle` is a record of optional fields (colour, weight, size in percent): styles compose by
overriding, a monoid; the law `styled s (styled t is) ≡ styled (s <> t) is` holds up to rendering.
`emph` and `strong` stay, as meanings a theme can restyle.  Colours are CSS strings, the ones
`Style.fill` already takes.

Nested bullets are block structure, not text: `data Item = item Text (List Item)` and
`bullets : Bool → List Item → Block`, with the flat call unchanged by a smart constructor.

## Steps

**1. Unify (pure refactor, nothing visible changes).**  Create `Slides.Text` with `Inline`, plain,
and the parser from label markup; the diagram `Text` primitive carries `List Inline`; move
`TextMetrics` and the SVG label printer to folds over it; `Deck.Content` re-exports `Inline`;
delete `Seg`.  Gate: `make check`, and every golden and SVG byte-identical (parse then print must
reproduce today's output exactly).  Proof: the parser agrees with the old `Markup` on its
examples, and `plain` of a parsed label is the label text minus markup.

**2. Add the features, once.**  `br` (HTML `<br>`, plain a line separator; in labels a stack of
lines, line height from `TextMetrics`), `styled` (HTML `<span style>`, SVG `<tspan fill>`),
`sub` and `sup` in prose; nested bullets (HTML nested `<ul>`, plain text indents by depth, flat
lists byte for byte as before).  Laws: `plain` still a homomorphism, `styled` composition,
flattening nested bullets is the identity on depth one (so `lowerBlock-id` and `lowerBlock-fuse`
stay `refl`).  A new example slide exercising each, golden added.

## Budget and rules

Step 1 must not add lines net (two ASTs become one).  Step 2 about 60 lines.  The core
(`Slides.Diagram.*` laws, Scene, Program) keeps its statements; only the `Text` primitive's
payload type changes, in the modules that pattern-match on it.  `make check` clean, no
postulates, `make test` green, `tests/check_closure.py` green.

## Decisions taken

1. `br` is a constructor of the shared tree (so labels get it too); no label-only helpers.
2. `styled` takes a record of optional fields; colours are raw CSS strings (a closed palette type
   waits for a theme record).
3. Nested bullets by rose tree, flat call shape kept.
