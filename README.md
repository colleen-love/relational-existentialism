# Relational Existentialism

A philosophy — relation comes first, and the self is what relation produces — together with a mechanized formalization of it.

The repository's thesis: **relation comes first, and the self is what relation produces** — a self **arises**
from axioms that never name it.

> **The arena reset (handoff I.II).** The project has moved to a **new foundation** — a **quantaloid /
> allegory in which relations are the primitive arrow** and `Q` is the value-object — replacing the earlier
> traced-SMC + operator-representation arena. **Paper one is being rebuilt from scratch** on it. The prior
> edifice (the rotated papers, the shared theory/foundation layers, the conservation frontier, the Agda
> layer) is **not deleted** — it is the same theory in a representation we outgrew, **archived as structural
> reference** under [`archive/archived/`](archive/archived) and catalogued in
> [`archive/archived/INDEX.md`](archive/archived/INDEX.md), to be mined and re-grounded relationally.

- **Start here — what paper one is:** [`paper-1/README.md`](paper-1/README.md) and its spec stubs
  ([`paper-1/spec/`](paper-1/spec)). It is a **skeleton**; spec II.1 defines it on the new arena.
- **The turn, and the layout:** [`STRUCTURE.md`](STRUCTURE.md) — the arena change recorded plainly, and what
  is live versus archived.
- **The archived edifice (what was proved, and where):** [`archive/archived/INDEX.md`](archive/archived/INDEX.md)
  — theorem-by-theorem, with what each depended on, so a result's *shape* can be ported into the new arena.

## Layout

The repository is now minimal while paper one is rebuilt:

- [`paper-1/`](paper-1) — *a self arises from the axioms*, on the new relational arena. A **live skeleton**:
  spec stubs + an empty `Paper1` Lean root. Spec II.1 fills it.
- [`archive/archived/`](archive/archived) — the prior edifice, **structural reference** (not built, not
  gated): the rotated papers, the `theory/` and `foundation/` layers, the `scratch/` frontier, and the Agda
  layer; with [`prior-archive/`](archive/archived/prior-archive) holding the work outgrown earlier. Indexed
  in [`INDEX.md`](archive/archived/INDEX.md).
- [`lake/`](lake), [`scripts/`](scripts), [`papers/`](papers) — infrastructure: the Lean package home
  (lakefile stripped to the single `Paper1` library), the gate (reduced to `paper-1/`), and the final
  manuscripts. See [`STRUCTURE.md`](STRUCTURE.md).

## Licensing

This repository is dual-licensed, with a deliberate split between **code** and **writing**. The boundary is drawn explicitly so there is no ambiguity about which file falls under which license.

### Code — Apache License 2.0

All **source code** is licensed under the Apache License, Version 2.0. The full text is in [`LICENSE`](LICENSE) at the repository root.

This covers everything that is software: scripts, proof-assistant developments (Lean / Agda / Rocq), Julia and Python sources, configuration, build tooling, and any other executable or machine-readable code, wherever it sits in the tree (including any code embedded in or shipped under `/docs` or `/writing` — e.g. runnable example files).

### Writing — Creative Commons Attribution 4.0 International (CC BY 4.0)

All **prose, philosophy, and other written/creative material** is licensed under CC BY 4.0. The full text is in [`LICENSE-docs`](LICENSE-docs).

This covers everything in the per-root `spec/` directories (and any `/writing`) — the philosophy itself, explanatory essays, notes, diagrams-as-exposition, and the formalization write-up — plus any prose documentation elsewhere in the repository (such as this `README.md`).

Under CC BY 4.0 you are free to share and adapt this material for any purpose, including commercially, provided you give appropriate credit, link to the license, and indicate if changes were made.

### Where the line falls

| Material | License | File |
| --- | --- | --- |
| Source code (anywhere in the tree) | Apache 2.0 | [`LICENSE`](LICENSE) |
| Prose / philosophy / docs in per-root `spec/` and `/writing` | CC BY 4.0 | [`LICENSE-docs`](LICENSE-docs) |
| This README and other prose docs | CC BY 4.0 | [`LICENSE-docs`](LICENSE-docs) |
| Final manuscripts in `/papers` | All rights reserved | [`papers/README.md`](papers/README.md) |

**Exception — `/papers` (all rights reserved).** The `/papers` directory is expressly excluded from the CC BY 4.0 grant. Its contents are © 2026 Colleen Love, all rights reserved; no license is granted. The "prose elsewhere in the repository is CC BY 4.0" rule does **not** reach into `/papers`, so copyright in the final manuscripts stays free to assign at submission.

The governing rule when a directory or file contains both kinds of material: **code is Apache 2.0; the surrounding prose is CC BY 4.0.** When in doubt, the nature of the file decides — a `.lean`, `.jl`, `.py`, or other source file is code (Apache 2.0); a `.md` or other prose document is writing (CC BY 4.0). The one exception is `/papers`, above, which is all rights reserved.

© 2026 Colleen Love. Code under Apache-2.0; written material under CC BY 4.0.
