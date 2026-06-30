# Repository structure — the arena reset (handoff I.II)

> **The project changed arenas.** The theory has moved from a **traced symmetric monoidal category +
> operator-representation** foundation to a **quantaloid / allegory in which relations are the primitive
> arrow and `Q` is the value-object**. Relations are no longer represented *inside* an operator algebra or a
> traced category — they are the primitive arrow of the arena itself. Paper one is being **rebuilt from
> scratch** on this foundation.

## The prior edifice is archived, not deleted

The earlier development is **not wrong** — it is the same theory in a representation we outgrew (the seam is
Lawvere either way; conservation is conservation either way). So it was **archived as structural reference**,
with history preserved (`git mv`), and left navigable so we can mine it.

- [`archive/traceable-smt/`](archive/traceable-smt) — the edifice we **just** outgrew: the rotated papers
  (`paper-2/`, `paper-3/`), the shared `theory/` and `foundation/` layers, the `scratch/` frontier, and the
  Agda layer. Catalogued in [`archive/traceable-smt/INDEX.md`](archive/traceable-smt/INDEX.md) — file-by-file,
  with what each depended on, so a result's *shape* can be ported into the new arena.
- [`archive/traceable-smt/prior-archive/`](archive/traceable-smt/prior-archive) — the work we outgrew **earlier** (the
  older deprecated development: functorial semantics, the `Int`/GoI scaffolding, the sparsity capstones).
  Kept distinct from the just-outgrown layer, not flattened into it.

Archived code is **structural reference**: it is **not** on the build path and **not** gated. It is mined and
re-grounded relationally where relevant — never resurrected wholesale.

## What is live

| Path | What | Status |
|---|---|---|
| [`scratch/`](scratch) | *a self arises from the axioms*, on the new relational arena | **live skeleton** — spec stubs + a `Paper1` Lean root; spec II.1 fills it |
| [`lake/`](lake) | the Lean package home + mathlib cache | infrastructure; lakefile stripped to the single `Paper1` library |
| [`scripts/`](scripts) | the gate + environment setup | `gate.sh` reduced to checking `scratch/` (trivial while it is a skeleton); grows back with the new arena |
| [`papers/`](papers) | the final manuscripts (all rights reserved) | unchanged |
| [`archive/`](archive) | the prior edifice (see above) | reference only, not built |

`paper-1/` has been renamed to `scratch/` to reflect its status as the rebuild's working skeleton; the
lakefile (`srcDir`), `gate.sh`, and build targets were updated to point at it. The Lean library is still
named `Paper1`. `lake build` is green with only `Paper1` present; `gate.sh` passes trivially.

## The derive-don't-define through-line carries over

The arena changed; the thesis did not. Paper one still **derives** the self rather than defining it: it
commits to an arena, relations-first, and a codirection process — none naming a self — and shows the self
condenses out as a fixed point. The new arena (relations as the primitive arrow) is meant to make that
derivation *more* direct, not to change its shape. The precise relational statements are spec II.1's job.

## How the rebuild proceeds

Spec II.1 defines paper one on the new arena (domain, signature, axioms), and the build/gate grow back from
the single `Paper1` library as the relational development lands. When a new-arena theorem needs an old proof's
structure, the archive index is the map: find the result, open the file, port the shape, re-ground whatever
the index flags as representation-dependent.
