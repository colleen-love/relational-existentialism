# theory — fork provenance

**Status (handoff XXI): `theory/` is now the STABLE shared layer (not the frontier).** The proof-DAG reorg
flipped theory's role (reversing spec XIII): because papers are thin layers that import it, `theory/` changes
**only backward-compatibly** (generalization, never redefinition); the living frontier moved to `scratch/`
(paper three). Two structural changes landed:
- **Namespaces normalized** `RelExist.* → Theory.*` — `theory/` is uniformly `Theory.*`, so papers import the
  shared `T.x` with clean names and no collision (the spec-XX block is gone).
- **The forks were unified into theory and the papers un-forked them**: the band layer is one canonical copy
  imported by both papers; paper two's six `Paper2.*` forks are gone. Drift-checked byte-identical first, so
  no meaning shifted; paper one's headline footprints diffed identical at the checkpoint.

The node inventory (the proof DAG as `A/F/T/P`-numbered nodes) is [`NODES.md`](NODES.md). The historical
fork-provenance below is retained.

---

`theory/` imports only `theory/` + `foundation/` (closure gate) and references no paper.

- **New here (no fork):** `Theory.ModularFlow` (modular A1), `Theory.MutualCoupling` (generative A3),
  `Theory.Priority` (A2-priority / no-bare-carrier), `Theory.OneGenerator` (handoff XV — the open-system
  capstone: assembles the GKLS generator `𝓛 = -i[(1/β)K,·] + 𝒟` from the modular `K` (state) and paper one's
  dissipator `𝒟` (arrow), and proves they are **one generator at equilibrium** via the KMS bridge and the
  preferred-basis Schur-commutation; consumes `Theory.ModularFlow` and `Theory.RotatingSpectrum`),
  `Theory.Einselection` (handoff XVI — *derives* spec XV's basis alignment from stationarity
  `𝒟(ρ) = 0` ("the clock-state is the rest-state"), identifies the einselected conserved band `Peri = fixed ⊕
  rotating`, and defines **presence** as its HS weight: conserved and Pythagorean-split into knowing ⊕ energy,
  but with the arrow shown to be *loss, not relocation* — a precisely-located negative for paper three;
  consumes `Theory.OneGenerator` and `Theory.BandFromAxioms`). These are already *not* paper one.
- **Forked from `paper-1/` on demand at `fe935a6`** (genuine second consumer = the frontier modules above):
  `Theory.We` (for `Priority`), and `Theory.{RotatingSpectrum,BandCoincidence,BandFromAxioms}` (for
  `MutualCoupling`). Frozen copies of paper-1's `Scratch.{We,RotatingSpectrum,BandCoincidence,BandFromAxioms}`,
  byte-identical at the fork hash except their import lines (re-pointed to `Theory.*`). **Intended identical**
  to paper-1's copies until a `theory` axiom reading deliberately diverges them.
- **Imported (not forked):** `foundation/` (`Foundation.Traced`).

**Lazy-hoist rule:** the canonical home of a shared module is wherever it currently lives; hoisting to
`theory/` happens *per-lemma, at first second-consumer*, not eagerly. The other ~14 paper-one modules have
no `theory` consumer and remain paper-1-only — not duplicated here.

## The canonical axiom layer (handoff XX)

`Theory.Axioms` is the **canonical axiomatization** `{A1, A2, A3-process, D1}` the three papers share. It
reframes **A3 as a process** — *relations co-direct attention asymmetrically in the relata*, with per-relatum
capacity `α` (the `MutualCoupling.jointStep` co-direction step) — and **derives**, as theorems, the per-paper
*readings* that were previously posited separately:

- **Existence** (`self_exists`, `self_exists_stable`) — the process has fixed points, and a stable one is
  reached generatively.
- **The eigenform / `Peri`** (paper one) — `eigenform_of_fixed`, `self_is_periBand`, `energy_in_self`.
- **The generative engine** (paper three) — `generative_law` (`orbit_engine2`), `generative_bounded`.
- **The phase-bearing / modular self** (paper two) — `modular_preserves_self`, `modular_sustains_self`,
  `modular_is_symmetry` (the modular flow is a modulus-one Schur multiplier that maps the self into itself,
  sustains it, and commutes with the co-direction channel).

Plus the supporting normalizations: `A1_dimension_generic` (finite vs infinite is the same A1 instantiated),
`A2_priority` (`Priority.priority_universal`), `D1_trace_is_modular_limit`
(`ModularFlow.modularFlow_maximally_mixed`). All carry the corpus-norm footprint
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. Prose for an outside reader:
[`AXIOMS.md`](AXIOMS.md).

**Reversal of the freeze (Part C).** With the A3 divergence collapsed, the freeze that spec XIII protected by
*duplication* shifts to **version-pinning**: `Theory.Axioms` is a *stable shared layer* (like `foundation/`,
changing only backward-compatibly), papers **import or cite + pin** it rather than fork it, and the four
`theory/` forks (`We`, `RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`) are now *confirmed*
non-divergent — the byte-identity with paper one is no accident but the content of the collapse. `Theory.Axioms`
itself adds **no** name to the shared `RelExist.*` namespace (it is namespaced `Theory.Axioms`), so it names
the existing objects without redeclaring them.
