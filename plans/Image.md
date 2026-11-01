# 2D images, categorically

The meaning of a picture, and how our `Layout`, `Diagram` and `Plot` relate to it.  Companion to
`plans/FRP.md` (animations are images over time).  Papers are in `lit/` (gitignored).

## 1. The denotation (Elliott, *Functional Images*)

- `Image A = Point → A`, with `Point = ℝ²`: the power `A^Point`.  A region is `Image Bool`; a
  picture is `Image Colour`.
- `Functor` and `Applicative` structure is pointwise, so every algebraic law of `A` holds for
  images (the power model, as for behaviours).
- A geometric transformation `g` acts by reindexing along its inverse: `(g · im) p = im (g⁻¹ p)`.
  Images are contravariant in space, as behaviours are contravariant in words.

`lit/Elliott-2003-Functional-Images.pdf`, `lit/Elliott-2009-Denotational-Design-TCM.pdf`.

## 2. Compositing (Porter and Duff)

- Colours with coverage (premultiplied RGBA) form a monoid under `over`, with the transparent
  colour as unit.  `over` is associative but not commutative.
- Pointwise, `Image Colour` is a monoid under `over` (the power of that monoid), and the action
  of transformations is by monoid homomorphisms: transform-then-overlay equals overlay-then-
  transform.
- So images form a monoid with an action of the affine group by monoid homomorphisms: a module
  over the group, or equivalently a monoid object in its presheaves (`G`-sets).

`lit/Porter-Duff-1984-Compositing.pdf`.

## 3. Diagrams (Yorgey)

A diagram library is the same structure one level up, kept symbolic:
- a diagram is a monoid of primitives under superposition, carrying an envelope (how far it
  extends in each direction) as a monoid annotation;
- transformations act on the diagram, its envelope and its primitives, the action distributing
  over the monoid (a semidirect product);
- rendering is the monoid homomorphism to images, equivariant for the action.

Yorgey, *Monoids: theme and variations* (Haskell 2012; not downloaded).

## 4. Where we sit

What we have:
- `Dia S`, the free algebra of the layout signature (`Slides.Diagram.Syntax`), folded into
  `Layout S`: a frame, the primitives in list order (later on top), named anchors.  This is a
  display list: §3's symbolic level, not §1's images.
- Sizes are folds into envelope semigroups; translation is an `Action` of `(S×S, ⊕)` on
  drawings, anchors and layouts (`Slides.Diagram.Laws`).
- Overlay (`ovl`, `Slides.Diagram.Laws`) joins the frames and concatenates the drawings: a
  semigroup (`layoutOverlay`), not commutative, like `over`.
- `Framed W H` (`Slides.Diagram.Framed`): layouts of frame exactly `W × H`, a monoid under
  overlay.  Plot ⊂ Diagram is `renderF`, landing in it.

What is missing is the map to images:

    ⟦_⟧ : Layout S → Image Colour

with the laws that make it a model:
1. **Overlay**: `⟦ ovl x y ⟧ = ⟦ x ⟧ over ⟦ y ⟧` (a monoid homomorphism, the order kept).
2. **Translation**: `⟦ v · l ⟧ = v · ⟦ l ⟧` (equivariance for the `Action`).
3. **Change of scalar**: for `ι : ℕ → ℚ`, `⟦ mapLayout ι l ⟧` is `⟦ l ⟧` with points read through
   `ι` (naturality in the scalar).
4. **Plot ⊂ Diagram in images**: the image of a rendered plot is transparent outside
   `[0, W] × [0, H]` (its support is in the frame).  Today `size-render` only says the frame is
   `W × H`; drawings may extend past the frame.

Obstacles, and a way round them:
- Primitive meanings need real geometry: strokes (distance to a curve), arcs, Bézier paths,
  glyphs for labels.
- Colours are CSS strings and `cls` defers to a stylesheet, so a style does not determine a
  colour on its own.
- The way round: make `⟦_⟧` a fold over `draws` parameterised by the meaning of one primitive,
  `prim : Draw S → Image A`, for any monoid `A` with a translation-equivariant `prim`.  Laws 1–3
  then hold generically from the list structure.  Concrete `prim`s (regions only,
  `A = Bool` under `∨`; or a colour model) can come later, and the SVG printer is then one more
  interpretation, tested against browsers, not proved.

## 5. Animation

Animations are `Image^T`, Fran's `Behaviour Image` (`plans/FRP.md` §1).  Our animations read a
`Layout` at each time (`Timed` over layouts), so `⟦_⟧` pointwise in time gives the map into
that model.  Diagram ⊂ Animation (`pure` / `firstFrame`) becomes constant images over time.
