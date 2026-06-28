# paper-2 — the modular self-relation paper

Frozen, self-contained. Manuscript: [`spec/paper-two.md`](spec/paper-two.md); provenance:
[`spec/AXIOM-PROVENANCE.md`](spec/AXIOM-PROVENANCE.md). `formal/` (library `Paper2`) is the **modular slice**
forked frozen from `theory/` at `fca792d` (handoff XVII, `Theory.* → Paper2.*`): six modules —
`Paper2.{ModularFlow, RotatingSpectrum, BandCoincidence, BandFromAxioms, OneGenerator, Einselection}` — the
modular reading of A1, the conserved band, the equilibrium one generator, and the einselection principle +
presence. Not forked: the A2-priority / A3-generative work (`We`, `Priority`, `MutualCoupling`), which serves
the conservation and sparsity papers. Imports only `Paper2.*` + mathlib (the modular slice is mathlib-direct,
**no** `foundation/`, **no** `paper-1/`); cites paper one's arrow result in prose rather than importing it.
See [`../STRUCTURE.md`](../STRUCTURE.md).
