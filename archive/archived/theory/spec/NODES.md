# The proof DAG — node inventory (handoff XXI)

> *The file-dependency graph **is** the proof DAG **is** the argument.* Each Lean file is one **node** (a
> result); the `import` edges between files are the "uses" edges. Walk imports back from a headline and you
> read its proof. This file is the index: every node, its **layer-prefixed number**, and its address.

**Layers.** `F` = foundation substrate · `A` = the canonical axioms · `T0` = theory theorems (the stable
shared layer, imported by ≥1 paper or load-bearing for `A`) · `T1/T2/T3` = each paper's own nodes (paper one,
two, three), `T4` reserved for the paper-four frontier. A manuscript step reads e.g. *"by `A3`, `T0.03`
(eigenform), `T0.03` (band coincidence) we obtain `T2.13` (the arrow)"* — the prefix names the layer, the
number orders by position in that layer's argument. *(Handoff I.O rotated the papers back one slot: the
former `P1/P2/P3` per-paper prefixes are now `T2/T3` for the two content papers, with a new foundational
paper one — `T1`, a skeleton — at the front; module names were unchanged where the content did not move.)*

**Granularity (the split, confirmed).** The rule is *one file per node, unless that forces an import cycle*
(an SCC is one node). Lean import graphs are **acyclic by construction**, so the file granularity already
**is** the condensation of the proof DAG: there is no SCC to merge, and each current module is a single
coherent result-cluster (no bundle to split). The reorg therefore *confirms* the existing module boundaries
as the nodes — it does not refragment them.

---

## F — foundation (substrate; dimension-agnostic, mathlib-bound)

| # | Node | Module / namespace | Imports |
|---|---|---|---|
| F.1 | Traced-SMC typeclass + JSV axioms | `Foundation.Traced` | mathlib |
| F.2 | Partial-trace *operation* | `Foundation.PartialTrace` | mathlib |
| F.3 | Matrix arena / traced-SMC instance | `Foundation.MatrixModel` | F.1, F.2 |

## A — the canonical axioms (`theory/`, stable)

`Theory.Axioms` states `{A1, A2, A3, D1}` canonically and **derives** the per-paper readings of the self as
theorems (handoff XX). It is the A-layer plus the canonical `T`-derivations (eigenform, generative, modular).

| # | Axiom / derivation | Address |
|---|---|---|
| A1 | the arena, dimension-generic | `Theory.Axioms.A1_dimension_generic` |
| A2 | priority (no bare carrier), universal | `Theory.Axioms.A2_priority` |
| A3 | the co-direction **process**; self = its fixed point | `Theory.Axioms.IsSelf`, `self_exists` |
| D1 | self-relation = trace ⇝ modular flow | `Theory.Axioms.D1_trace_is_modular_limit` |
| — | eigenform (paper two) derived | `Theory.Axioms.eigenform_of_fixed` |
| — | modular self (paper three) derived | `Theory.Axioms.modular_preserves_self` |

*(The **generative** reading is **not** derived in the axioms — it is paper-four frontier, derived from the
canonical process in `scratch/` (`GenerativeEngine.generative_law`); see the `T4` section.)*

## T — theory theorems (the stable shared layer, `Theory.*`)

In topological order, grouped by sub-argument. **Double-imported** (paper-2 *and* paper-3): T0.01–T0.03 (the
band layer) — the mechanical reason they are `T0`, not `T2`. T0.04 (`ModularFlow`) is **axiom-supporting** (the
canonical axioms derive the modular self from its `modPow_diagonal`) and also imported by paper three; T0.05–T0.06
support `A`; T0.07 is the **A3 co-direction process** that defines the self (`IsSelf := JointFixed`), imported
by `A`. *(The growth-*analysis* of the process — the ignition/spend-down engine — is **not** here: it is
unused by any shipped paper, so it is paper-four frontier in `scratch/` — see the `T4` section.)*

| # | Node | Module | Imports | Headline it carries |
|---|---|---|---|---|
| T0.01 | energy = the rotating band | `Theory.RotatingSpectrum` | — | the `schur` channel, `genReal` arrow |
| T0.02 | the band lattice; seam = rotating | `Theory.BandCoincidence` | T0.01 | `band_coincidence` |
| T0.03 | eigenform `Peri`; band coincidence from axioms | `Theory.BandFromAxioms` | T0.02 | **paper one's energy**: `band_coincidence_from_axioms`, `undifferentiated_two_term_from_axioms` |
| T0.04 | modular self-relation (D1's modular form); spectral machinery | `Theory.ModularFlow` | — | `modularFlow`, `modularFlow_maximally_mixed`, `modPow_diagonal` |
| T0.05 | lived-identity coinduction `≈ := νΘ` | `Theory.We` | — | (theory's copy, supporting T0.06) |
| T0.06 | A2 priority / no-bare-carrier | `Theory.Priority` | T0.05 | `priority_universal` |
| T0.07 | the A3 co-direction process (self-definition) | `Theory.MutualCoupling` | T0.03 | `jointStep`, `JointFixed` (`= Axioms.IsSelf`) |

## T1 — paper one's own nodes (`paper-1/`, the new foundational skeleton)

**Skeleton (handoff I.O).** Paper one (*a self arises from the axioms*) is a **skeleton**: an empty `Paper1`
Lean root + spec stubs, **no nodes yet**. Its `T1.<n>` theorems are deferred to the formalization pass.

## T2 — paper two's own nodes (`paper-2/`, `Scratch.*` / `RelExist.*`)

Single-importer today, so they stay `T2` (promote the day a second paper's Lean imports them). The seam spine,
lived identity, the knowing-is-lossy passage, and **the arrow**.

**Narrative:** each surviving T2 node has **one narrative doc** in
[`../../paper-2/spec/`](../../paper-2/spec/), named `T2.<n>-<descriptive>.md` to match this table (e.g.
`T2.13-the-arrow.md`); the consolidated walk is [`paper-two.md`](../../paper-2/spec/paper-two.md). The stale
`02-axioms.md` was removed — the canonical axioms are [`AXIOMS.md`](AXIOMS.md). Drive any further rename from
this table so files and DAG cannot drift.

| # | Node | Module | Imports |
|---|---|---|---|
| T2.01 | the mirror | `RelExist.Mirror` | — |
| T2.02 | relating | `RelExist.Relating` | T2.01 |
| T2.03 | the seam | `RelExist.Seam` | T2.02 |
| T2.04 | seam bridge | `RelExist.SeamBridge` | T2.03 |
| T2.05 | lived identity `≈ := νΘ` (3.2) | `Scratch.We` | — |
| T2.06 | knowing is the lossy σ-move (3.3) | `Scratch.KnowingFeeling` | T2.05, T2.01 |
| T2.07 | `σ = Tr` as gfp (D1 realization) | `Scratch.Trace` | — |
| T2.08 | decoherence in the matrix model | `Scratch.Decoherence` | F.3 |
| T2.09 | directed attention | `Scratch.Attending` | T2.08 |
| T2.10 | the quantum seam | `Scratch.QuantumSeam` | T2.08 |
| T2.11 | the knower→known orientation | `Scratch.Orientation` | T2.10 |
| T2.12 | seam protection (forcing / conserved / ℂ) | `Scratch.SeamForcing` · `SeamConserved` · `SeamForcingC` | T2.09 |
| T2.13 | **the arrow** = time (3.8) | `Scratch.TimeFlow` | T2.11 | **paper two's arrow**: `coh_orbit_antitone` |
| T2.14 | the instance converse (3.10) | `Scratch.KnowingFromArrow` | T2.13, T2.12 |
| T2.15 | A3 at the strength of its text (3.9) | `Scratch.PhaseBearing` | T0.03, T2.12 |

*Note (former T2.16).* `Scratch.CanonicalEigenform` (the spec-XX collision workaround) was **deleted in
handoff XXII** — XXI dissolved the collision, making it redundant with `Theory.Axioms.eigenform_of_fixed`,
which paper two now cites directly. The deletion was footprint-gated: paper two's headline footprints are
unchanged. The T2 series therefore ends at **T2.15**.

## T3 — paper three's own nodes (`paper-3/`)

Paper three imports the band layer + `ModularFlow` (T0.01–T0.04) from `theory/` and proves its **own** `T3.x`
(only paper three imports them, so by the promotion rule they are `T3.x`, not `T0.x`). Paper two's arrow is a
**prose citation**, never imported.

| # | Node | Module | Imports | Headline it carries |
|---|---|---|---|---|
| T3.01 | two faces of one generator (equilibrium) | `Paper3.OneGenerator` | T0.04, T0.01 | `combinedFlow_add` |
| T3.02 | einselection; presence | `Paper3.Einselection` | T3.01, T0.03 | **paper three's headline**: `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation` |

## T4 — paper four's own nodes (`scratch/`, the living frontier)

Unnumbered until promotion (scratch convention); listed here for the inventory.

| Node | Module | Status |
|---|---|---|
| decoherence conserves coherence (it relocates it) | `scratch/formal/Conservation.lean` | **frontier seed**, not gated |
| the generative engine (ignition / spend-down analysis of the A3 process) | `scratch/formal/GenerativeEngine.lean` | **frontier**, not gated; derived on `Theory.MutualCoupling` (T0.07). Doc: [`../../scratch/spec/generative-engine.md`](../../scratch/spec/generative-engine.md) |

*Recorded hoist-item, not a violation.* `Conservation` *imports* paper two's `Scratch.Decoherence`
(T2.08). Because `scratch/` is a **free workbench** (XXII), this is **fine now** — the gate exempts scratch and
enforces cite-don't-import only at the **promotion event** (when scratch becomes paper four). At promotion,
resolve it by citing T2.08 in prose or hoisting the needed lemma to `theory/`.

---

## Boundary = node — audit

**Split done.** `Theory.MutualCoupling` was two nodes under one name. It is split at the clean DAG seam
(`JointFixed`): the **self-definition** stays in `theory/` (T0.07, load-bearing for the axioms — `IsSelf :=
JointFixed`); the **growth-analysis** (the `Engine`/ignition/spend-down verdict) — *unused by any shipped
paper* — moved to `scratch/formal/GenerativeEngine.lean` (the paper-four / `T4` frontier). Footprint-gated:
paper two's headline footprints are identical. *(The named "character" lemmas — `frozen_no_growth`, `asymmetry_emerges`,
`capacity_rate_limits` — are stated over the `Engine2` abstraction, so they moved to scratch with it; keeping
them in `theory/` would have forced a `theory→scratch` import. The self stays generative **by definition**
either way.)*

**Reported, not split (axiom-touching — needs a second look before a footprint-affecting change):**
`Theory.ModularFlow` arguably holds two clusters at a one-way edge — the modular-flow automorphism group +
D1-limit + thermal time, and the **spectral machinery** (`specFun_diagonal`/`modPow_diagonal`, which depends
on `modPow`). Both are theory/load-bearing (the axioms import `modPow_diagonal`), so a split is two theory
files, not a relocation; deferred as a cosmetic within-theory refinement, reported here rather than forced.

**One node (left as-is).** The remaining large files are single coherent result-clusters with rich support,
not separable bundles (`RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`, `TimeFlow`, `Decoherence`,
`OneGenerator`, `Orientation`). `T2.12` deliberately groups three tightly-coupled modules
(`SeamForcing`/`SeamConserved`/`SeamForcingC`) as one node. `Paper3.Einselection` (einselection → presence)
is a single chain, kept as `T3.02`.

## On physical file numbering

The numbering above is the **authoritative ordering**; the modules keep their **descriptive** names
(`Theory.BandFromAxioms`, not `Theory.T03`) because after Phase 2 the import graph *already* realizes the
proof DAG with legible names — the descriptive name carries the meaning, this index carries the order. A
manuscript cites *"`T0.03` (eigenform / band coincidence, `Theory.BandFromAxioms`)"*: number for position, name
for content. (A future pass may prefix the files `T03_BandFromAxioms.lean` for a self-ordering listing; the
DAG and the addresses are unchanged by such a rename, so it is deferred as cosmetic ordering, not structure.)
