# Text: line breaks, colours and styles, nested bullets

Status: proposal, for review before any code.  Phase 3 of `plan/TODO.md`.

## What exists

Two text languages, which is the source of the surprises.

| Where | Type | Has |
|---|---|---|
| Slide prose (`Content`) | `Text = List Inline`; `Inline`: `text`, `codeSpan`, `emph`, `strong`, `inlineMath`, `link`, `cite` | a tree; HTML by `Render.piece`; plain text by `plainT` |
| Diagram labels (`Diagram.Text`) | one `String`, parsed by `Markup` into `Seg`: `flat`, `sub`, `sup` | one line; width by `TextMetrics`; colour only through the primitive's `Style` |

Blocks: `bullets : Bool → List Text → Block` is a flat list.

The semantics we want to preserve: `plain` is a monoid homomorphism to lines (`plain-++`), and HTML
rendering is the other one (`render-glue`).  Each new construct is added so that both stay
homomorphisms and every backend gets a reading (the plain backend ignores what it cannot show).

## Proposal

### 1. Line breaks

- **Prose.**  One new `Inline` constructor, `br`.  HTML `<br>`; plain text a newline.  Law:
  `plainT` sends `br` to a line separator, so `plain` remains a homomorphism.  (Paragraph breaks
  are already `paragraph`; `br` is only a break *inside* a paragraph, a bullet, a heading or a caption.)
- **Diagram labels.**  No new primitive.  A multi-line label is a vertical stack of single-line
  `Text`s through `above`, so its size is derived (the principle in `docs/Objects.md`) and the
  layout laws apply unchanged.  `Convenience.lines : List String → Dia`, with the line height a
  single parameter.  The existing `Markup` segments stay inside each line.  A `\n` in a label
  string is sugar for `lines` at construction time, not a new constructor in the language.

### 2. Native text colours and styles

- **Prose.**  One `Inline` constructor, `styled : TextStyle → List Inline → Inline`, where
  `TextStyle` is a record of optional fields: `colour : Maybe String`, `weight`, `size` as a
  percentage of the surrounding size.  Fields are `Maybe` so that styles compose by overriding,
  which is a monoid (`_<>_` takes the right field when present, `∅` the empty style); the law
  `styled s (styled t is) ≡ styled (s <> t) is` is the one worth proving, as a rendering
  equivalence (`plainT` ignores style).  `emph` and `strong` stay, as shorthand with a
  semantic meaning (so a theme can restyle them), not as styles.
  HTML: `<span style="…">`; colour strings are the same CSS strings `Style.fill` already takes
  in diagrams, so one palette serves both.  A theme's named colours remain CSS classes through
  `classed`; `styled` is for one-off use.
- **Diagram labels.**  Colour already exists per primitive (`Style`).  Mixed colours in one
  label would be `beside` of several `Text`s, which loses the baseline unless the pieces share a
  height; that is fine because `TextMetrics` already gives every piece the same line height.
  So no new label syntax; add `Convenience.coloured : List (String × String) → Dia`, pieces
  with their colours, glued by `beside`.

### 3. Nested bullets

Replace the flat list by the rose tree it is:

```
data Item : Set where  item : Text → List Item → Item
bullets : (incremental : Bool) → List Item → Block
```

- A flat list is `item t []` for each entry; a smart constructor keeps today's
  `bullets xs` source-compatible (examples need no change).
- HTML: `<ul><li>t<ul>…</ul></li></ul>`.  Plain text: indentation by depth (a fold over the tree
  with the depth as an argument; the flat case is the old output byte for byte, so the goldens
  do not move).
- `incremental` applies to the first level only by default; per-item reveal is a later extension.
- Law: flattening (`items`) is a monoid homomorphism and is the identity on trees of depth one,
  which is what the existing lowering and Navigation proofs (`lowerBlock-id`, `lowerBlock-fuse`)
  need; they are `refl` on bullets today and should stay so.

## What changes where

| Module | Change |
|---|---|
| `Deck.Content` | `br`, `styled`, `TextStyle`, `Item`; `plainT`/`plainB` cases |
| `Backend.Render` | `piece`, `renderBlock` cases |
| `Deck.Lower` | `refl` cases for the new constructors (Block unchanged for text; bullets changes shape) |
| `Deck.DSL` | `br`, `styled`/`coloured`, `nest` helpers; `bullets` accepts items |
| `Diagram.Convenience` | `lines`, `coloured` |
| `assets/*.css` | nothing (inline `style` for one-offs) |

Estimated size: 60 to 90 lines, mostly cases, plus the two proofs; no change to `Diagram.*` proper,
the Scene layer or the machine.

## Decisions for review

1. `br` inside prose only, with labels getting `lines` in `Convenience` (rather than a break in
   the `Markup` language).  Recommended.
2. `styled` with a record of optional fields versus separate constructors (`coloured`, `big`, ...).
   Recommended: the record, since styles then form a monoid and one HTML span carries them.
3. Nested bullets by rose tree `Item`, `bullets` keeps its flat call shape.  Recommended.
4. Colours as raw CSS strings (matching `Style`), not a closed palette type.  A palette type is
   safer but would have to be shared with the theme records; defer until a theme record exists.
