# scratch — the living frontier (paper three)

The living frontier (handoff XXI: `theory/` became stable, so the *living* work moved here). Imports
`foundation/` + `theory/`; **nothing imports from here**. Promote stable, shared material to `theory/`
(`T.x`, the day a second paper imports it) or `foundation/` per [`../STRUCTURE.md`](../STRUCTURE.md); once a
result is paper-bound and frozen, it moves to a paper root.

- **Paper three seed:** [`formal/Conservation.lean`](formal/Conservation.lean) — *decoherence conserves
  coherence; it only relocates it into what you traced out.* Not yet gated. **Coupling to resolve:** it
  currently *imports* paper one's `Scratch.Decoherence`; under cite-vs-import that must become a prose
  citation (or the needed lemma promotes to `theory/`) before paper three joins the gated build.
