# Pending negative tests (Stage 1 port)

Drafts of the negative tests that the input/navigation port needs (plan/Unify.md, Stage 1).
They are *not* part of `make test-negative` yet, because they are written against local
stand-ins that mirror `src/Slides/Spike/Input/Backend.agda`, not against the real
`Slides.Input.*` modules (branch `stage1-core`, not merged).

| file | must be rejected because | rejection |
|---|---|---|
| `NoNavBackend.agda` | a backend whose `Supports` lacks `Nav` cannot present a deck (`present` needs `NavTotal`) | type error (`nothing != just _`) |
| `TwoCommandsOneInput.agda` | `next` and `prev` are bound to the same input (the binding table is not injective) | `No instance of type True (conflict? ...)`, same shape as the existing negatives |

`controls/` holds the same stand-ins with a *valid* program; each control MUST typecheck, so
a rejection above cannot come from a typo in the stand-ins.

`make test-negative-pending` checks all of this (negatives rejected, with the expected message;
controls accepted).

## When Slides.Input.Supports exists

1. Replace each stand-in (`Nav`, `Supports`, `NavTotal`, `present`, `bind`, `conflict?`) by the real
   definition; keep `bad` and the controls' `ok` unchanged in intent.
2. Move the two negatives to `tests/negative/`, the controls to a positive check (e.g. a module
   in `src/Slides/Input/Examples` that `make check` loads).
3. `make test-negative` accepts only "No instance of type" as a rejection.  Either make the
   NoNav check an instance-argument (`{{_ : True (navTotal? b)}}`, decidable for finite
   `Supports`), or extend the loop with an explicit expected-message column.
4. Binding of *families* (`goto n`, `gotoLabel s`) goes through a decoder (plan 4b, item 3); add a
   negative test for two decoders that accept the same input once that exists.
