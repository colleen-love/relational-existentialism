# paper-2 — axiom & lemma provenance

**Status (handoff XXI): thin layer importing `theory/`.** The proof-DAG reorg **un-forked** paper two. Its
six `Paper2.*` modules — confirmed byte-identical to `theory/`'s, so unifying shifted no meaning — were
deleted; `paper-2/formal/Paper2.lean` now **imports** the clean `Theory.{ModularFlow, RotatingSpectrum,
BandCoincidence, BandFromAxioms, OneGenerator, Einselection}`. Paper two has **no `P2.x` Lean nodes of its
own**; its headline theorems (`presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation`,
`combinedFlow_add`, `stationary_eq_diagonal_real`) live at their canonical `T` addresses (`Theory.Einselection.*`,
`Theory.OneGenerator.*`), which the manuscript cites. The freeze is now a **version-pin** on the `theory/`
commit (below), not a duplicated copy. The historical fork description below is retained for provenance.

---

**Historical (handoff XVII): frozen fork of the modular slice.** Under the lazy fork-and-freeze discipline
(handoff XIII), paper two materialized when it was built (handoff XVII): the six modular modules were forked
frozen from `theory/`, namespace and module path `Theory.* → Paper2.*`, content otherwise byte-identical.

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

## Canonical axiom layer — pin (handoff XX)

Handoff XX reframed A3 as a **process** and derived the per-paper readings of the self as theorems of that one
process, in the **canonical axiom layer** [`Theory.Axioms`](../../theory/formal/Theory/Axioms.lean) (prose:
[`theory/spec/AXIOMS.md`](../../theory/spec/AXIOMS.md)). Paper two's **modular self** is one of the derived
readings: the modular flow of a diagonal state is a modulus-one Schur multiplier, so it **maps the conserved
band (the self) into itself**, **sustains** it edge-for-edge (the rotating sub-band carrying the modular
energies as phases), and **commutes** with the co-direction channel — the *same* fixed point, read under the
modular flow (`Theory.Axioms.modular_preserves_self` / `modular_sustains_self` / `modular_is_symmetry`,
distilled from this paper's own `OneGenerator`).

- **Pin.** Paper two is proved against the **canonical axiom layer** `Theory.Axioms` as of **handoff XX**
  (branch `claude/normalize-canonical-axioms-wyg8xq`). The layer changes **only backward-compatibly**
  (generalization, never redefinition), so this pin keeps meaning what it meant.

- **Consumed by citation + pin, not import.** Paper two's forks are `Paper2.*` (a *distinct* namespace, so —
  unlike paper one — a literal `import Theory.Axioms` would not collide). Today paper two nonetheless stays
  mathlib-direct and self-contained (no `Theory.*`/`Foundation.*` import), consuming the canonical reading by
  citation + this pin; the `scripts/gate.sh` allowance for `Theory.Axioms` makes a future direct import
  available should the modular slice be re-based onto the shared layer.

- **Reversal of the freeze (handoff XX, Part C).** Spec XIII protected a per-paper A3 *divergence* by frozen
  duplication; that divergence is gone (the readings are one process's consequences). The freeze shifts from
  *duplication* to **version-pinning**: paper two keeps its byte-identical `Paper2.*` fork as the pinned copy
  and pins the canonical layer here.
