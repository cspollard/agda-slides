# Diagram laws and a scalar parameter

One piece of work, not two: the laws are the reason to parametrise, and the
parametrisation is what makes the laws provable. Nothing here changes the
surface language (`Slides.Diagram.Notation`) or what a deck says.

## Why together

- With ℕ, `∸` truncates and centring floors, so the laws that matter are false
  or carry side conditions. Nested centring `⌊(3−2)/2⌋ + ⌊(2−1)/2⌋ = 0` against
  `⌊(3−1)/2⌋ = 1` already breaks associativity of `∥` by one unit.
- With an abstract commutative ring the offset arithmetic in every law is a ring
  identity, which `Tactic.RingSolver` closes automatically.
- Laws are stated up to a pointwise equality on `Layout`. If the scalar is a
  stdlib-style bundle with its own `_≈_`, that equality is the natural one, and
  it is the setoid the repo's algebraic fold needs anyway.

## The scalar interface

Stdlib 2.3 has `Algebra.Bundles.CommutativeRing` but no ordered ring, no field
record and no square root (`Data.Nat.Sqrt` does not exist), so we define the
tiers ourselves, each extending the one before:

1. `OrderedCommRing`: `CommutativeRing`, a decidable total order, and the
   compatibility laws (`a ≤ b → a + c ≤ b + c`, `0 ≤ a → 0 ≤ b → 0 ≤ a * b`).
   Enough for `∥ ═ ⊙`, margins, translation.
2. `HalvableRing`: adds `½` with `2 * ½ ≈ 1`. Gives exact centring. Instances:
   the dyadic rationals ℤ[½], and ℚ.
3. `SqrtField`: an ordered field with `√ : 0 ≤ x → S` and `√x * √x ≈ x`. Only
   for circles and other envelopes. No computable instance exists for the
   reals, so this tier is axiomatic: laws are proved for any model, and the
   executable model is an approximation (a rational `√` with an error bound),
   so any law that mentions it carries an explicit tolerance ε.

Sizes are non-negative, offsets are signed. Keep `width height : S` and carry
`0 ≤ width` as an invariant, proved once for each primitive and preserved by
each connective (a lemma per operator), rather than splitting the types.

## Laws to prove, in order

1. **Translation is an action.** `inFrame` with `shift 0 ≈ id` and
   `shift a ∘ shift b ≈ shift (a + b)`; every connective is equivariant;
   `render l x y` is `render l 0 0` translated.
2. **Monoid laws.** `∥`, `═`, `⊙` associative with unit `empty`;
   `↔ m ∥ ↔ n ≈ ↔ (m + n)`. `⊙` is not commutative (z-order). No interchange
   law between `∥` and `═`; the docs already say so.
3. **Annotations are geometry-neutral.** `width`, `height` of `named n d` and
   `connect … d` equal those of `d`; two `connect`s commute up to permutation
   of the rendered list.
4. **Fusion.** If `h : A → B` is an algebra morphism then `h ∘ fold_A ≡ fold_B`.
   Instances: (a) the projection `Layout → S × S` equals the fold of a size-only
   algebra; (b) `Names` soundness, `dangling d ≡ [] →` every `connect` in
   `layout d` finds its anchors, as a logical relation between the `Names` and
   `Layout` algebras.
5. **Contexts.** Identity is a unit for composition of one-hole contexts;
   `margin`, `framed` are equivariant.

`LabelAbove` / `LabelBelow` stay connectives: their spacer height is the child's
laid-out height, so they are not derivable in the free syntax.

## Steps

Each step ends with `make check`, `make test` and the browser run.

1. **Scalar module.** `Slides.Diagram.Scalar` with the three records and
   instances for ℕ (tier 1 only, as a semiring where the ring laws are not
   needed; used only for compatibility), ℤ[½] and ℚ. Literals via
   `Data.Rational.Literals` so `margin 10 0 10 0` still reads the same.
2. **Parametrise.** `{S}` (or a module parameter) through `Syntax`, `Place`,
   `Layout`, `Names`, `Notation`; `Backend.Diagram` prints a scalar with
   `toString` (integers as integers, halves as `.5`). Keep a thin
   `Layout.Nat`-style entry point so decks compile unchanged.
3. **Exact centring.** Use `½` instead of floor division. This changes some
   golden coordinates by half a unit; regenerate them and say so in the commit.
4. **Setoid carrier.** `Layout` with a pointwise `_≈_` and a congruence proof for
   each operator.
5. **Laws 1–2**, using the ring solver.
6. **Laws 3–5**, starting with size fusion (cheap), then `Names` soundness.
7. **Optional, only if a deck needs it:** a `Shape` on anchors (rectangle,
   disc) with ports from the outline, for `SqrtField`. Until then arrows to a
   disc end on its bounding square, under one unit off for a radius-36 disc.

## Risks

- Normalising rational arithmetic in Agda can be slow; check `make check` time
  after step 2 and fall back to ℤ[½] as the default instance if needed.
- Golden output changes in step 3 are expected and small; the browser run is the
  check that diagrams still look right.
- Proof obligations for `0 ≤ width` multiply with the number of connectives;
  keep them in one lemma per operator next to its definition.

## Status

Done (see `Slides.Diagram.{Scalar,Draw,Equality,Place,Layout,Laws,Names,NamesSound}`):

- the scalar interface `Ops`, with ℕ, ℤ and ℚ instances;
- half-unit positions, so centring is exact; `Layout` as plain data;
- layout equality up to the scalar's own equivalence (`Equality`): `IsLawful` takes
  a stdlib `IsCommutativeRing _≈_`, not `_≡_` (ℤ and ℚ instantiate it with `_≡_`);
- translation action, associativity of `∥ ═ ⊙`, unit laws for layouts of
  non-negative size, annotation neutrality, size fusion;
- `Names` scoped to each `connect`'s own diagram, with its soundness proof.

Not done:

- **A scalar whose equality is not `_≡_`.** The proofs are written for any `_≈_`,
  but only `_≡_` instances (ℤ, ℚ) exist. A constructive real, or ℚ as unreduced
  pairs, would be the first real test.
- **`Raw`** ignores positions (its elements are in the final coordinates), so it is
  outside the translation law.
- **Unit law for `Valid` composites:** `Valid` is a hypothesis; that every
  combinator preserves it (needs `+` and `⊔` to respect non-negativity) is not
  proved.
- **Square roots and shapes on anchors** (tier 3 above).
