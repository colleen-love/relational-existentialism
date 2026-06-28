# paper-2 — axiom & lemma provenance

**Status: frozen fork of the modular slice.** Under the lazy fork-and-freeze discipline (handoff XIII), paper
two materializes when it is built (handoff XVII): the six modular modules are forked frozen from `theory/`,
namespace and module path `Theory.* → Paper2.*`, content otherwise byte-identical. The fork is the value — a
paper must mean exactly what it meant at review.

- **Forked from `theory/` at `fca792d`** (the six-module modular closure, verified by imports):
  `Paper2.{ModularFlow, RotatingSpectrum, BandCoincidence, BandFromAxioms, OneGenerator, Einselection}`.
  Frozen copies of `theory/`'s `Theory.{…}` at the fork hash, identical except their `import`/`namespace`
  lines (`Theory.* → Paper2.*`). The slice: the modular reading of A1 (`ModularFlow`), the rotating/conserved
  band (`RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms` — the forked arrow-band layer), the
  equilibrium one generator (`OneGenerator`), and the einselection principle + presence definition
  (`Einselection`).

- **Deliberately divergent:** **none yet.** Paper two's modular reading and `theory/`'s currently coincide;
  when `theory/`'s reading moves ahead, this file records the split per affected module. Intended identical
  today: all six.

- **Imported from `foundation/`:** **none.** The modular slice is mathlib-direct — every forked module imports
  only `Paper2.*` + mathlib. (Confirmed: no `Foundation.*` import anywhere in `paper-2/formal/`.)

- **Not forked** (deliberately): `We`, `Priority`, `MutualCoupling` — the A2-priority / A3-generative work,
  which serves the conservation and sparsity papers, not the modular slice. The fork is enforced by closure
  (`scripts/gate.sh`: `Paper2` imports only `Paper2.*` + mathlib), not by judgement.

## Cross-paper dependency: cite, don't import

Paper two's **quantitative** dependence on paper one's arrow is the **forked band layer**
(`Paper2.RotatingSpectrum` / `Paper2.BandFromAxioms` — `genReal`, the conserved band): the minimal interface,
already factored out by the original hoist into `theory/`. Paper two's **conceptual** dependence — that the
lossy self-relating projection *orders* the arrow, the seam as the un-decohereable floor (paper one's
`SeamForcing.self_cannot_fully_decohere`) — is **cited in prose** in the manuscript ("by the arrow result of
paper one"), **never forked**. So `paper-2/` imports no `paper-1/` path; the citation carries the meaning.
Confirmed: no `Scratch.*` / `RelExist.*` (paper-one) import exists in `paper-2/formal/`.

**Drift check:** diff `paper-2/formal/Paper2/*` against the corresponding `theory/formal/Theory/*` (modulo the
`Theory.→Paper2.` rename); any *accidental* difference in an "intended identical" module is a bug to
reconcile, any *deliberate* one is this paper's divergence and belongs in the list above.

**Footprints.** The headline theorems depend only on `[propext, Classical.choice, Quot.sound]` — no `sorryAx`
(verified via `#print axioms` on `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`,
`combinedFlow_add`, `stationary_eq_diagonal_real`).
