# scratch — the living frontier (paper three)

The living frontier (handoff XXI: `theory/` became stable, so the *living* work moved here). Imports
`foundation/` + `theory/`; **nothing imports from here**. Promote stable, shared material to `theory/`
(`T.x`, the day a second paper imports it) or `foundation/` per [`../STRUCTURE.md`](../STRUCTURE.md); once a
result is paper-bound and frozen, it moves to a paper root.

- **Paper three seed:** [`formal/Conservation.lean`](formal/Conservation.lean) — *decoherence conserves
  coherence; it only relocates it into what you traced out.* Not yet gated. **Recorded hoist-item (not a
  violation):** because `scratch/` is a free workbench (XXII), its import of paper one's `Scratch.Decoherence`
  is **fine now**. It resolves at the **promotion event** — when this becomes paper three — by either citing
  paper one's decoherence in prose or hoisting the needed lemma to `theory/`. The gate enforces cite-don't-
  import *only at promotion*, not on the workbench.
