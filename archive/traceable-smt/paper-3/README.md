# paper-3 — the modular self-relation paper

A **thin layer** over the stable `theory/`. Manuscript: [`spec/paper-three.md`](spec/paper-three.md); provenance +
pin: [`spec/04-provenance.md`](spec/04-provenance.md); node docs: [`spec/T3.01-one-generator.md`](spec/T3.01-one-generator.md),
[`spec/T3.02-einselection-presence.md`](spec/T3.02-einselection-presence.md).

`formal/` (library `Paper3`) **imports** the shared `T0.x` it uses and proves its **own** `T3.x`:

- **Imported (from `theory/`):** `Theory.ModularFlow` (the modular reading of A1) and the band layer
  `Theory.{RotatingSpectrum, BandCoincidence, BandFromAxioms}` — the conserved band and the `genReal` arrow it
  cites quantitatively.
- **Its own (`T3.x`):** `Paper3.OneGenerator` (**T3.01** — `combinedFlow_add`, the two faces of one generator
  at equilibrium) and `Paper3.Einselection` (**T3.02** — `presence_conserved`, `pythagorean`,
  `arrow_is_loss_not_relocation`).

It imports only `theory/` (+ mathlib) — **no** `paper-2/`; paper two's arrow is a **prose citation**. Pins the
`theory/` commit in its provenance. The node inventory is [`../theory/spec/NODES.md`](../theory/spec/NODES.md);
the layout discipline is [`../STRUCTURE.md`](../STRUCTURE.md).
