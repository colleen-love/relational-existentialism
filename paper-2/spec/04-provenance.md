# 04 — Provenance (paper two)

> *The honest accounting.* Paper two is the **modular self-relation** paper. This page records what it owns,
> what it imports, its provenance tier, and its version pin.

## What paper two is

A **thin layer** over the stable `theory/`. It **imports** the shared `Theory.*` nodes it uses and proves its
**own** two nodes:

- **Imported (`T.x`, from `theory/`):** `Theory.ModularFlow` (the modular reading of A1) and the band layer
  `Theory.{RotatingSpectrum, BandCoincidence, BandFromAxioms}` (`T.01`–`T.04`) — the conserved band and the
  `genReal` arrow it cites quantitatively.
- **Its own (`P2.x`):** [`P2.01-one-generator.md`](P2.01-one-generator.md) — `Paper2.OneGenerator`
  (`combinedFlow_add`, the two faces of one generator at equilibrium); and
  [`P2.02-einselection-presence.md`](P2.02-einselection-presence.md) — `Paper2.Einselection`
  (`presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`, `stationary_eq_diagonal_real`).

Paper one's seam→arrow result is a **prose citation** in the manuscript ([`paper-two.md`](paper-two.md)),
never a Lean import; `paper-2/formal/` imports no `paper-1/` path.

## Provenance tier

**R / S** — rederivation of standard pieces (Tomita–Takesaki modular flow, the finite-dimensional KMS
identity, GKLS/Lindblad form, Schur-multiplier commutation, einselection / pointer states) with the synthesis
being the equilibrium identification *modular clock = dissipative arrow as two faces of one generator*
(`combinedFlow_add`), and the **presence** reading: the conserved band's Hilbert–Schmidt weight is conserved
and Pythagorean-split into knowing ⊕ energy, with the arrow shown to be **loss, not relocation**
(`arrow_is_loss_not_relocation`) — a precisely-located negative handed to paper three.

**Footprints.** The headline theorems depend only on `[propext, Classical.choice, Quot.sound]` — no `sorryAx`
(verified via `#print axioms` on `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`,
`combinedFlow_add`, `stationary_eq_diagonal_real`).

## Version pin — the canonical axiom layer

Paper two's **modular self** is a *derived* reading of the canonical A3-process: the modular flow of a
diagonal state is a modulus-one Schur multiplier, so it maps the conserved band (the self) into itself,
sustains it edge-for-edge (the rotating sub-band carrying the modular energies as phases), and commutes with
the co-direction channel (`Theory.Axioms.modular_preserves_self` / `modular_sustains_self` /
`modular_is_symmetry`). The canonical axioms `{A1, A2, A3, D1}` are
[`theory/spec/AXIOMS.md`](../../theory/spec/AXIOMS.md), mechanized in `Theory.Axioms`.

- **Pin.** Paper two is proved against the **canonical axiom layer** `Theory.Axioms` at the `theory/` state on
  this branch. The layer changes **only backward-compatibly** (generalization, never redefinition), so the
  pin keeps meaning what it meant.
- **Deliberate divergence:** none. Paper two's shared `T.*` nodes are the canonical copies (imported); its own
  `P2.*` nodes derive the modular reading the canonical axioms also carry.
