# agda-slides

Scientific slide decks, diagrams and animations as small typed languages in Agda
(`--safe --without-K`).  Each language is a free monad over a container and its meaning is an
algebra, so layouts, animations and navigation come with proved laws.  Decks render to reveal.js
and to standalone HTML.

```agda
demo : Body
demo = do
  heading 1 "Slides in Agda"
  paragraph ("a " ∷ emph "free-monad" ∷ " DSL" ∷ [])
  pause
  bullets ("typed decks" ∷ "verified laws" ∷ [])
```

More: `src/Slides/Examples/` (`Intro` is the smallest deck, `Showcase` uses most features).

## Layers

```
Container   free monads, handlers, container sums, lowering      (the algebra everything reuses)
Scalar      the theories of space, time and coupling; models ℕ and ℚ
Diagram     layouts: beside, above, layers, place; size is derived, never stated
Scene       time: Par, Hold, Delay, Drive; read as events or sampled at a tick
Program     a scene that waits: a Moore machine; navigation and labels
Deck        slides and fragments as one scene of scenes; text, blocks, DSL
Backend     reveal.js and plain HTML; animations ship as an event list
```

Start with `docs/Objects.md`, which says what each object is and how they relate.  The Agda
modules carry the detail; `make html` renders them with links to `html/`.

## Use

Needs Agda 2.7, the standard library 2.3, agda-categories, the `parsnip` submodule, and
`npm install reveal.js katex @fontsource/fira-code` for the browser output.

```
make check                  typecheck src/
make example                build out/intro/ (also: talk plain showcase pairs text collider)
make test                   golden outputs, negative cases, closure check (build the decks first)
make test-browser-all       browser tests (needs Playwright)
make html                   rendered module documentation in html/
```

`docs/Contributing.md` has the working rules; `plans/TODO.md` lists what is open;
`docs/Dropped.md` lists the theorems of the previous implementation (git tag `legacy`) not yet
restated.
