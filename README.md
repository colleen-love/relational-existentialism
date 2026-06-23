# Relational Existentialism

A philosophy — relation comes first, and the self is what relation produces — together with a program for formalizing it as a presented theory with functorial semantics across domains.

- **The view, in plain language:** [`docs/relational-existentialism.md`](docs/relational-existentialism.md)
- **The four-layer formalization program:** [`docs/formalization-plan.md`](docs/formalization-plan.md)
- **The formal spec (doctrine, signature, axioms):** [`docs/spec/`](docs/spec/)
- **The mechanized development (Lean 4):** [`formal/`](formal/) — machine-checked and `sorry`-free, now spanning all four layers: the sparsity dichotomy (Lemmas 3.1 & 3.2), the Lawvere mirror and the cartesian firewall, a **traced symmetric monoidal category** typeclass with its **monoidal-coherence** refinement, the **free traced SMC `Cl(𝕋)`** (bare and coherent) with universal functors, a **literal matrix model** (trace = the quantum partial trace), and all **five Layer-4 domain functors** (physics, chemistry, biology, AI, and the firewall).

Code implementing the formalization (proof-assistant developments, `Catlab.jl` / `AlgebraicJulia` schemas, `DisCoPy` string-diagram functors, and so on) lives alongside these documents as the work develops.

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

The governing rule when a directory or file contains both kinds of material: **code is Apache 2.0; the surrounding prose is CC BY 4.0.** When in doubt, the nature of the file decides — a `.lean`, `.jl`, `.py`, or other source file is code (Apache 2.0); a `.md` or other prose document is writing (CC BY 4.0).

© 2026 Colleen Love. Code under Apache-2.0; written material under CC BY 4.0.
