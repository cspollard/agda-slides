# Scalar models with non-canonical representatives

Goal: the scalar theories (Core, Space, Time, Coupling, Hom, the Nat and Rat models) admit models
whose elements have no canonical form, chiefly unnormalised rationals, which defer the gcd.
Everything stays parametric in the scalar; adding a model changes no existing model or deck.

## Decision record
- **Step 1 measured (Agda 2.7.0.1, `+RTS -A1g`, load 2 to 2.7).**  Typechecking is not slow:
  `Slides.Scalar.Hom` with dependencies 7.6 s, of which 6.8 s is loading; no definition above
  0.4 s.  Running Collider took about 40 s, and GMP (all integer arithmetic, gcd included) was
  3.5% of a sampling profile.  The gcd is not the cost; the run time was elsewhere (see
  `plans/TODO.md`, "Collider run time").
- **Planned (not started):** the setoid generalisation of the scalar theories (laws up to a
  carried equivalence, folds into setoids), so non-canonical models such as unnormalised ℚ are
  first-class.  It is wanted for the mathematics, not for speed (gcd is not the cost); it
  rewrites most of the scalar modules, so it is its own piece of work.
- **Usable as is:** the raw unnormalised arithmetic (`ℚᵘ`, as in `Slides.Three`) can be used
  anywhere a plain computation needs it, with no theory behind it.
- **Meanwhile:** `simplify` (embed after normalise) can be plain arithmetic.
