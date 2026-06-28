# Relational Existentialism

A philosophy — relation comes first, and the self is what relation produces — together with a mechanized formalization of it.

The repository proves, and shows its work for, **one result**:

> *The arrow of time is the orientation active self-relating cannot escape; and the conserved remainder of self-relating — what never becomes known — is exactly energy.*

- **Start here — the result:** [`docs/spec/paper-one.md`](docs/spec/paper-one.md), a single linear walk through it, each step status-tagged and named by its Lean theorem.
- **The view, in plain language:** [`docs/relational-existentialism.md`](docs/relational-existentialism.md)
- **One step toward the formalization (plain words, structures named):** [`docs/relational-existentialism-toward-formalization.md`](docs/relational-existentialism-toward-formalization.md)
- **The formal spec (doctrine, signature, axioms, theorems):** [`docs/spec/`](docs/spec/) — foundation (`00`/`01`/`02`), the theorems `3.1 … 3.9` one page each, and the provenance ledger; see [`docs/spec/README.md`](docs/spec/README.md) for the reading order.
- **The mechanized development (Lean 4):** [`formal/`](formal/) — machine-checked and `sorry`-free, in two libraries: `RelExist` (the dependency-free core) and `Scratch` (the mathlib-backed half). Both build clean; the headline footprints sit at the corpus norm, with the seam depending on no axioms.
- **The coinductive ν-layer (Agda):** [`agda/`](agda/) — a parallel `--safe --guardedness` mechanization of the identity/`ν` material (lived identity `≈`, theorem 3.2, with native coinduction); not part of paper one.

The supporting development — the conservation law and cosmos readings (paper two), the sparsity of selfhood (paper three), the functorial-semantics layer, and the route-1 scaffolding — is **kept, not foregrounded**, under [`docs/archive/`](docs/archive) and [`formal/Archive/`](formal/Archive), referenced as future work rather than as the headline.

## Licensing

This repository is dual-licensed, with a deliberate split between **code** and **writing**. The boundary is drawn explicitly so there is no ambiguity about which file falls under which license.

### Code — Apache License 2.0

All **source code** is licensed under the Apache License, Version 2.0. The full text is in [`LICENSE`](LICENSE) at the repository root.

This covers everything that is software: scripts, proof-assistant developments (Lean / Agda / Rocq), Julia and Python sources, configuration, build tooling, and any other executable or machine-readable code, wherever it sits in the tree (including any code embedded in or shipped under `/docs` or `/writing` — e.g. runnable example files).

### Writing — Creative Commons Attribution 4.0 International (CC BY 4.0)

All **prose, philosophy, and other written/creative material** is licensed under CC BY 4.0. The full text is in [`LICENSE-docs`](LICENSE-docs).

This covers everything in the [`/docs`](docs) and `/writing` directories — the philosophy itself, explanatory essays, notes, diagrams-as-exposition, and the formalization write-up — plus any prose documentation elsewhere in the repository (such as this `README.md`).

Under CC BY 4.0 you are free to share and adapt this material for any purpose, including commercially, provided you give appropriate credit, link to the license, and indicate if changes were made.

### Where the line falls

| Material | License | File |
| --- | --- | --- |
| Source code (anywhere in the tree) | Apache 2.0 | [`LICENSE`](LICENSE) |
| Prose / philosophy / docs in `/docs` and `/writing` | CC BY 4.0 | [`LICENSE-docs`](LICENSE-docs) |
| This README and other prose docs | CC BY 4.0 | [`LICENSE-docs`](LICENSE-docs) |
| Final manuscripts in `/papers` | All rights reserved | [`papers/README.md`](papers/README.md) |

**Exception — `/papers` (all rights reserved).** The `/papers` directory is expressly excluded from the CC BY 4.0 grant. Its contents are © 2026 Colleen Love, all rights reserved; no license is granted. The "prose elsewhere in the repository is CC BY 4.0" rule does **not** reach into `/papers`, so copyright in the final manuscripts stays free to assign at submission.

The governing rule when a directory or file contains both kinds of material: **code is Apache 2.0; the surrounding prose is CC BY 4.0.** When in doubt, the nature of the file decides — a `.lean`, `.jl`, `.py`, or other source file is code (Apache 2.0); a `.md` or other prose document is writing (CC BY 4.0). The one exception is `/papers`, above, which is all rights reserved.

© 2026 Colleen Love. Code under Apache-2.0; written material under CC BY 4.0.
