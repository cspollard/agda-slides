# Theorems of the previous implementation not yet restated

An audit of tag `legacy` against the rebuild (about 790 legacy names; matching by meaning).  The
high-priority gaps (valid layouts and unit laws, functoriality of scalar maps, duration and
boundary laws of scenes, commutativity of `atop`, the remainder under ι) are restated.  What
remains, most useful first:

1. **Loop law.**  A repeated or looped scene reads `t mod n` ticks (legacy `Laws/loop-period`).  The
   page evaluator and `animateBoth` rely on it.  Medium.
2. **Example-level agreement.**  The generic theorems (`layout-natural-ok`, `soundness`, `digital`,
   `leaf-ok`) have side conditions (`OkDia`, `SidesDia`, `PctDigital`) that no example discharges
   (legacy `Pairs/Properties`, `PairsHero/Properties`), so nothing shows they hold on a real deck.
   Medium; also a cheap test of the conditions.
3. **Coupling exactness at ticks.**  `Hom` gives ι for ticks and scalars but not for `ratio`, `lerp`
   or `move`: when a move's duration divides exactly, its ℚ frame at a whole tick is ι of the ℕ
   one (legacy `Continuous/ratioAt-ι`, `inst-exact`).  Needed to say interpolated frames
   digitise.  Hard (an exactness predicate on easings); `move-start` and `progress-0` are easy.
4. **Scene-level footprint and independence.**  `Names.usage` is per diagram; a scene has no names
   fold, so "independent parts commute under `Par`" and "a scene declares what its leaves declare"
   are unstated (legacy `Footprint/*`).  The swap law `(a⨾b)∥(c⨾d) = (a∥c)⨾(b∥d)` holds only under a
   windowing hypothesis; the legacy never proved it either.  Medium, low priority.
5. **Key-table soundness.**  `clash-free` is checked by computation; nothing says a clash-free
   table decodes each key to the command that binds it, or that rendering a command then reading
   it back is the identity (legacy `Binding/*`, `Supports/*`).  Easy.
6. **Small ones, all easy.**  The rendered forest has one section per slide (legacy
   `renderDeck-length`); `animationFinal` returns the last frame and leaves a looping animation
   alone (legacy `finalFrame-*`); `glue` is a monoid (done: `glueMonoid`, `chunks-isMonoidHomomorphism`).

## Dropped on purpose
- The shipped encodings `Share`, `Formula`, `Param`, `Phases` and their properties (179 names):
  an event list with parametric leaves and a subtree-sharing table replaces them (`Objects.md`).
- Frame-list and delta machinery: a raw frame list is a scene of one-tick frames.
- `Track` and its laws (about 60 lemmas): moving values are Coupling terms.  There is no reversal
  operation; restate `reversal` if one returns.
- `LabelC`, `autoLabel`, `Fresh`: labels are slide data.
- The `Binding` and `Hash` proofs and the `XML` bridge from `Eq` to `_≈ₓ_`: bindings are tables
  with a computed `clash-free`, and render properties use `≡` on forests.
- Ring-and-setoid scaffolding (`IsLawful`, `_≈ᴸ_`, `_≈ᵖ_`, ℤ/ℚ `Ordered` instances, evaluators,
  `⊓`): `Space` is `≡`-based with a Max and Minus signature (see the setoid item in `plans/TODO.md`).
