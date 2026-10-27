# Navigation inventory

Scope: every place where navigation (next, prev, goto, first, last, step) and stepping
(fragments, `pause`, animation steps) live in the code that existed when Stage 1 began, and who
binds the physical input; plus the risks and surprises found.  The design that replaced it is
`docs/Input.md` (the one source of truth: commands, machines, `Supports`, bindings, the
differences between the backends); the plan is `plan/Unify.md`.  Line numbers are for branch
`stage1-port` at its creation (`c8e4c0b`).  Pinned by `tests/browser/nav.mjs` (`make test-nav`).

## 1. Inventory

### 1.1 Agda: the vocabulary

| where | what | command it implies |
|---|---|---|
| `src/Slides/Core.agda:111-125` | `LayoutShape.fragment style c`, `pause`, `stepped style l` | each is one *step* the audience advances: `next` reveals, `prev` hides. Nothing else says so; the meaning lives in the backends' class names |
| `src/Slides/Core.agda:52-63` | `Play = onSteps rests | looping | both rests period` | `onSteps`: one `next` per entry (one fragment each). `looping`: awaits nothing but needs a clock (`tick`). `both`: steps over a loop (`next` plus `tick`) |
| `src/Slides/Core.agda:127-148` | `DeckShape` (`slide`, `stack`), `Deck = DeckC ⋆ ⊤` | slide order: what `next`/`prev`/`goto` move over; `stack` makes a 2-D index (reveal `h,v`), flattened by plain |
| `src/Slides/DSL.agda:157-165` | `fragment`, `fragmentWith`, `pause` smart constructors | author-facing steps |
| `src/Slides/Steps.agda:36-65` | `go`/`steps`/`stepL`/`after`: `pause` elaboration with a Bool mode | `pause = await next`, written as a pass that wraps later commands in `fragment` (content, l. 36-40) or `stepped` (layout, l. 42-43); `notes` and `script` are not wrapped (l. 38-39) |
| `src/Slides/Steps.agda:67-94` | `bind-assoc`, `go-bind` | proofs about the mode threading (must be re-derived, 4) |
| `src/Slides/Lower.agda:51-70` | `finalFrame`, `animationFinal`: an animation as the still of its last rest | the lowering for a backend that has no steps/clock (not by `Nav`; by content) |
| `src/Slides/Lower.agda:73-113` | `layout`/`block`/`deck` lifting; `lowerDeck`, `stripNotes`, `stripScripts`, `diagramPlaceholder` | content lowerings only. There is no *command* lowering: a deck has no commands in its type yet |
| `src/Slides/Anim/Render.agda:54-56,86-94,111-116` | `restsOf`, `render` (`onSteps`), `renderLoop` (`looping`), `renderBoth` (`both`) | an act is a step; `restsOf` is the frame each step rests on |

### 1.2 Agda: the backends

| where | what |
|---|---|
| `src/Slides/Backend/Common.agda:129-131` | `bullet true` makes `li.fragment`; incremental bullets are steps outside `pause` |
| `Common.agda:208-213` | `renderLayout (fragment ..)` becomes `<div class="fragment [style]">` |
| `Common.agda:231-236` | `renderLayout (stepped ..)` becomes the same `<div class="fragment">` around the layout |
| `Common.agda:226` | `renderLayout pause = []` (the pause itself leaves no trace; only what follows is wrapped by `steps`) |
| `src/Slides/Backend/Diagram.agda:179-246` | `animationWith`: one empty `<span class="fragment anim-step">` per entry of `stepsOf play` (l. 233), `data-rests` (l. 240, 242), `data-loop` (l. 241-242), `data-ms` (l. 230). So animation steps are ordinary fragments to the page; the step count is *in the DOM*, not in the animation script |
| `src/Slides/Backend/Reveal.agda:47,59-61` | `steps` applied per slide body in `deckAlg`; a stack is `<section>` of `<section>`s |
| `Reveal.agda:100-132,174-183` | `options`: `hash: true`, `controls`, `progress`, `slideNumber`, `transition`. `hash:true` is what makes `#/h/v` a goto; arrow-key and overview handling are reveal's defaults, not configured here |
| `Reveal.agda:192-209` | `scriptLoader`: `Reveal.on('ready'|'slidechanged')` (runs slide scripts once) |
| `Reveal.agda:211-224` | `animationSync`: `ready`/`slidechanged` -> `player.syncAll(slide, true)` (jump), `fragmentshown`/`fragmenthidden` -> `player.sync(fragment.closest('.animation'), false)` (play). This is the only place the animation player learns about navigation |
| `Reveal.agda:226-234` | `initScript` = `Reveal.initialize(...)` + the two glue scripts + deck scripts; it is `out/*/init.js` (golden `tests/golden/*.init.js`) |
| `Reveal.agda:156-165` | `page` loads `reveal.js`, plugins (notes, highlight, math), `animation.js`, `init.js` |
| `src/Slides/Backend/Plain.agda:46-57` | `deckAlg`: `steps` per slide; a stack is flattened into consecutive `section.slide`s (l. 51). Reveal's `(h,v)` becomes one index |
| `Plain.agda:86-99` | `page` has `div.deck`, an empty `div.progress`, `animation.js`, `plain.js`. No buttons, no links |
| `src/Slides/Backend/Restyle.agda`, `XML*.agda`, `HTML.agda` | no navigation |
| `src/Slides/Driver.agda:23-31` | writes `index.html` (+ `init.js` for reveal); no navigation |
| `*/Properties.agda` | `Backend/Reveal/Properties`, `Backend/Plain/Properties`, `Lower/Properties`: proofs, not importable from executables (`tests/check_closure.py`) |

### 1.3 JavaScript

**`assets/plain.js`** (golden `tests/golden/plain.js`) is the whole plain navigation:

| lines | what | command |
|---|---|---|
| 5-7 | `slides`, `bar`, `current` | state: current slide index only; fragment state lives in the DOM (`.visible` class) |
| 29-41 | `show(i, revealAll)` | goto (clamped to `[0, n-1]`, l. 30); `revealAll` is true when arriving *backwards* (prev, End) so the slide shows all fragments; false when arriving forwards, Home or load. Also sets `active`, background colour, progress bar, `history.replaceState('#'+(i+1))` (l. 38), runs scripts, `syncAll(.., true)` |
| 43-49 | `next` | step: reveal the first hidden fragment and `syncAll(.., false)`, else `show(current+1, false)` |
| 51-57 | `prev` | step back: hide the last visible fragment, else `show(current-1, true)` |
| 59-66 | `keydown`: ArrowRight/ArrowDown/Space/PageDown = next; ArrowLeft/ArrowUp/PageUp = prev; Home = `show(0,false)`; End = `show(n-1,true)` | **binds the keys**; checks no modifier; `preventDefault` for handled keys |
| 75-76 | initial `#n` (one-based) -> `show(n-1,false)`; bad hash -> first slide | goto on load; no `hashchange` listener, so later hash edits are ignored |
| 26-27 | `SlidesAnimation(a => a.closest('.slide').classList.contains('active'))` | the *shown* predicate is the `active` class that `show` sets |

**`assets/animation.js`** (golden `tests/golden/animation.js`): `SlidesAnimation(shown)` is shared. It
listens to no reveal or plain event itself. Its only navigation-related inputs are the exported
`sync(a, jump)` and `syncAll(slide, jump)` (l. 200-206), called by `animationSync` (reveal) and
`plain.js` (l. 40, 47, 55); `target(a)` (l. 11-16) *reads the step count from the DOM*:
`a.querySelectorAll('.anim-step.visible').length` and maps it through `data-rests`. Direct DOM
listeners: `window` `beforeprint`/`afterprint` (l. 183-199) (print shows every fragment, so the
animation is shown at its last rest). `_show` (l. 180) is a test hook. `spin` (l. 157-178) is a
clock: `setInterval`/`requestAnimationFrame` driven by `data-loop`, gated by `shown(a)`. That is the
future `tick`, implemented by the page, not bound to any input.

**Reveal** has no navigation code of ours. Reveal itself (version 6.0.2 in the tests) binds
(`js/controllers/keyboard.js:258-400`): Right/`l`, Left/`h`, Down/`j`, Up/`k`, PageDown/`n`, PageUp/`p`,
Space (Shift+Space = prev), Home (first), End (last), Escape/`o` (overview), Enter (select in
overview), `f` fullscreen, `b`/`.` pause, `?` help; touch/swipe, mouse-wheel (off), on-screen
`controls` arrows, the progress bar, and the hash (`#/h[/v]`, zero-based unless
`hashOneBasedIndex`). Events emitted: `ready`, `slidechanged`, `fragmentshown`, `fragmenthidden`.

### 1.4 Tests and tools that touch navigation

| where | what |
|---|---|
| `tests/browser/run.mjs:46-52,160-170,175-192` | reveal: ArrowRight/Left through a pause slide, ArrowDown in a stack, hash `#/8/1`; plain: ArrowRight/Space/Left, `Home`/`End`, `#n` + reload |
| `tests/browser/anim.mjs:36-60` | `Reveal.nextFragment()/prevFragment()` drive animation steps (uses the *reveal API*, not keys) |
| `tests/browser/plain-anim.mjs` | plain animations on the arrow keys |
| `tests/browser/pairs.mjs` | the pairs deck (CDN); keys and fragments |
| `tests/browser/nav.mjs` (new) | all of 1.3 end to end, and the backend-agreement walk |
| `tests/check_reveal.py`, `tests/check_plain.py` | load pages headless; check `fragment` classes preserved |
| `tests/check_closure.py` | executables must not import `.Properties`. Constrains where new proofs may live |
| `tests/golden/*` | byte-exact: every `index.html`, `intro.init.js`, `showcase.init.js`, `pairs.init.js`, `plain.js`, `animation.js` |

## 2. Behaviour to keep byte-identical

* All `tests/golden/*` (indexes, `init.js`, `plain.js`, `animation.js`, css) unchanged. The
  port must not change what `Slides.Steps` yields in HTML (`fragment`/`stepped`/`anim-step` classes
  and order), `options`, the two glue scripts, `plain.js`, `animation.js`.
* The step count of every slide (`nav.mjs` `expectedForward`), the traces of reveal and plain
  equal for showcase and talk, the lowered and still decks' fragment counts.

## 3. Risks

* **Goldens**: the generated `init.js` embeds the two glue scripts verbatim; any change to
  `animationSync`/`scriptLoader` text or to option order breaks `intro/showcase/pairs.init.js`.
* **Key tables are not in our code for reveal**: reveal binds keys internally. A `Supports` binding for reveal
  can *describe* but not restrict them (e.g. Space, `n`, `l`, `j` all mean next). The conflict check at binding
  can only cover bindings we emit. Decide whether the check is over our table or over reveal's defaults.
* **Plain asymmetry**: `Shift+Space` is `prev` in reveal and `next` in plain, and plain ignores all modifiers (pinned in `nav.mjs`).
  Aligning them is a behaviour change.
* **`End` semantics**: plain reveals all fragments on the last slide; reveal's `End` is `Reveal.slide(lastH)` and its fragment state is unverified. Showcase's last slide has no
  fragments, so tests cannot see it; add a deck whose last slide has fragments before claiming the semantics are unified.
* **`goto` grammars differ** (reveal zero-based 2-D, plain one-based flat, plain only on load, reveal on hashchange).
* **Step count in the DOM**: animation steps are `span.fragment.anim-step`; the player derives the step from the number of visible
  fragments (`animation.js:11-16`). If `await next` becomes a first-class step, nothing in the HTML may change.
* **Performance**: `make check` memory (~6 GB) and the generic proofs over sum containers; measure after step 2 and 3.
* **Closure**: new elaboration used by executables must live outside `.Properties`.
* **Backwards fragments**: both backends show all fragments of a slide entered backwards, and reveal retains them for a goto backwards (`#/1` from slide 5 shows all, pinned). The machine's `view-next`/`prev-next` replay model must reproduce these states.

## 4. Surprises (implicit reveal assumptions that leak)

1. `animationSync` is the only coupling to navigation, and it assumes reveal's *events*: animation steps are plain `.fragment` spans
   so reveal's fragment machinery (and its keys) drive animations. Any backend that does not emit fragments must call `player.sync` itself (plain does).
2. `anim.mjs` drives animations with `Reveal.nextFragment()`, i.e. the reveal API, not a command binding.
3. Plain is a re-implementation of reveal's semantics with differences: Shift+Space, modifiers, hashchange, `End` fragments,
   no overview, no touch/mouse, one-based hash, hash written with `replaceState`.
4. The `stack` vertical axis exists only in reveal (`ArrowDown` in a stack, `#/h/v`); plain flattens, so `goto` is 2-D in one backend and 1-D in the other. `ArrowDown` on a horizontal slide does nothing in reveal and means next in plain.
5. Going back to a slide by goto: reveal shows all its fragments (`#/1` from slide 5 gave 3 of 3 visible, pinned); plain's Home/`#n` hide them. Plain's prev/End show them.
6. `plain.js`'s progress bar width is `100*(i+1)/n` with browser rounding; tests must compare numerically.
