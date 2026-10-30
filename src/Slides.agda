{-# OPTIONS --safe --without-K #-}

-- A map of the library, bottom to top.  A layer depends only on those listed before it.
--
--   Container.*          free monads over containers, handlers, sums, lowering; the algebra shared by all
--   Slides.Scalar.*      theories of space, time and coupling, and their models (ℕ, ℚ)
--   Slides.Text          the one tree of styled text, for prose and for labels
--   Slides.Diagram.*     diagrams: a free monad of layout operations over a scalar; layout, size, laws
--   Slides.Three.*       3D solids and views, compiled to diagrams
--   Slides.Scene.*       time: scenes and their readings (events, samples, frames)
--   Slides.Program.*     a scene that waits for input: the Moore machine, navigation
--   Slides.Deck.*        content, the authoring DSL, the deck as a scene of scenes
--   Slides.Backend.*     HTML rendering, reveal.js and plain pages, the shipped animation format
--   Slides.Examples.*    decks that exercise the above; `docs/Objects.md` says how the objects relate
module Slides where
