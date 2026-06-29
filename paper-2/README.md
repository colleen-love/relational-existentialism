# paper-2 — the modular self-relation paper

**Thin layer** (handoff XXI). Manuscript: [`spec/paper-two.md`](spec/paper-two.md); provenance:
[`spec/AXIOM-PROVENANCE.md`](spec/AXIOM-PROVENANCE.md). `formal/` (library `Paper2`) is now a thin layer that
**imports** the modular slice from the stable `theory/` rather than forking it: `Theory.{ModularFlow,
RotatingSpectrum, BandCoincidence, BandFromAxioms, OneGenerator, Einselection}` — the modular reading of A1,
the conserved band, the equilibrium one generator, and the einselection principle + presence. Paper two has
**no `P2.x` Lean nodes of its own**; its headline theorems live at their canonical `Theory.*` addresses (see
[`../theory/spec/NODES.md`](../theory/spec/NODES.md)) and the manuscript cites them there. It imports only
`theory/` (+ mathlib) — **no** `paper-1/`; paper one's arrow is a **prose citation**. Pins the `theory/`
commit in its provenance. See [`../STRUCTURE.md`](../STRUCTURE.md).

*(Historical: handoff XVII materialized this as six `Paper2.*` modules forked frozen from `theory/` at
`fca792d`; XXI un-forked them — they were byte-identical — into imports.)*
