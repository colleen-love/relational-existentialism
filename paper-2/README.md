# paper-2 — the modular self-relation paper

A **thin layer** over the stable `theory/`. Manuscript: [`spec/paper-two.md`](spec/paper-two.md); provenance +
pin: [`spec/04-provenance.md`](spec/04-provenance.md); node docs: [`spec/P2.01-one-generator.md`](spec/P2.01-one-generator.md),
[`spec/P2.02-einselection-presence.md`](spec/P2.02-einselection-presence.md).

`formal/` (library `Paper2`) **imports** the shared `T.x` it uses and proves its **own** `P2.x`:

- **Imported (from `theory/`):** `Theory.ModularFlow` (the modular reading of A1) and the band layer
  `Theory.{RotatingSpectrum, BandCoincidence, BandFromAxioms}` — the conserved band and the `genReal` arrow it
  cites quantitatively.
- **Its own (`P2.x`):** `Paper2.OneGenerator` (**P2.01** — `combinedFlow_add`, the two faces of one generator
  at equilibrium) and `Paper2.Einselection` (**P2.02** — `presence_conserved`, `pythagorean`,
  `arrow_is_loss_not_relocation`).

It imports only `theory/` (+ mathlib) — **no** `paper-1/`; paper one's arrow is a **prose citation**. Pins the
`theory/` commit in its provenance. The node inventory is [`../theory/spec/NODES.md`](../theory/spec/NODES.md);
the layout discipline is [`../STRUCTURE.md`](../STRUCTURE.md).
