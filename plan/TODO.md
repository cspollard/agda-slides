- [x] Complete proofs about the Dia type (the remaining laws are in `plan/Plan.md`, item 3)
- [x] Clean up completed items from plans, move information to docs (`docs/Design.md`)
- [x] Add proofs for the base DSL (`Slides.Diagram.Place.Properties.Laws`, `NamesSound`)
- [x] Add DSL for animations, similar to Dia, together with Reveal backend
  (`Slides.Anim.*`, `plan/Animations.md`).
- [ ] auto generate CSS?
- [ ] do we have Content.figure(checked)?
- [ ] duplication of e.g. fragment and Content.fragment
- [ ] slides should support the same primitives as diagrams.
- [ ] reduce compilation time
- [ ] allow line breaks
- [ ] allow native text colors and styles
- [ ] reinstate README documentation
- [ ] allow nested bullet points
- [ ] generalize 3D views and projections (started in Slides.Examples.ATLAS)
- [ ] Add background functionality (e.g. as an SVG or other image)
- [ ] Better inline documentation of commands -- some geometric intuition should be included when one peruses the html docs for each agda file.
- [ ] allow inclusion of pngs and pdfs as primitives -- need to be careful about how to ship these -- copy? symbolic link? Maybe not all backends can handle this.
- [ ] Add a slide number command (show the current slide number, and optionally
  the total, on a slide or in a footer). Reveal.js already has a deck-wide
  `slideNumber` option (`RevealConfig.slideNumber`, off by default), so the
  reveal backend should be nearly trivial; the plain backend needs its own
  counter. Decide whether it is a per-slide command, a deck option, or both, and
  how it interacts with labels and stacks (reveal counts stacks as one slide by
  default).
- [ ] A general 3D module (`Slides.Trig`, views, solids, projection to `Dia`), extracted from `Examples/ATLAS.agda`, with ℚ and polynomial trig of a user-chosen order. Plan in `plan/3D.md`.
