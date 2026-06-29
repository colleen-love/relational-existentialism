# The proof DAG — node inventory (handoff XXI)

> *The file-dependency graph **is** the proof DAG **is** the argument.* Each Lean file is one **node** (a
> result); the `import` edges between files are the "uses" edges. Walk imports back from a headline and you
> read its proof. This file is the index: every node, its **layer-prefixed number**, and its address.

**Layers.** `F` = foundation substrate · `A` = the canonical axioms · `T` = theory theorems (the stable
shared layer, imported by ≥1 paper or load-bearing for `A`) · `P1/P2/P3` = each paper's own nodes. A
manuscript step reads e.g. *"by `A3`, `T.3` (eigenform), `T.3` (band coincidence) we obtain `P1.13` (the
arrow)"* — the prefix names the layer, the number orders by position in that layer's argument.

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
| — | eigenform (paper one) derived | `Theory.Axioms.eigenform_of_fixed` |
| — | generative engine (paper three) derived | `Theory.Axioms.generative_law` |
| — | modular self (paper two) derived | `Theory.Axioms.modular_preserves_self` |

## T — theory theorems (the stable shared layer, `Theory.*`)

In topological order, grouped by sub-argument. **Double-imported** (paper-1 *and* paper-2): T.1–T.3 (the
band layer) — the mechanical reason they are `T`, not `P1`. T.4–T.6, T.9 are theory-native, imported by
paper two; T.7–T.8 support `A`.

| # | Node | Module | Imports | Headline it carries |
|---|---|---|---|---|
| T.1 | energy = the rotating band | `Theory.RotatingSpectrum` | — | the `schur` channel, `genReal` arrow |
| T.2 | the band lattice; seam = rotating | `Theory.BandCoincidence` | T.1 | `band_coincidence` |
| T.3 | eigenform `Peri`; band coincidence from axioms | `Theory.BandFromAxioms` | T.2 | **paper one's energy**: `band_coincidence_from_axioms`, `undifferentiated_two_term_from_axioms` |
| T.4 | modular self-relation (D1's modular form) | `Theory.ModularFlow` | — | `modularFlow`, `modularFlow_maximally_mixed` |
| T.5 | two faces of one generator | `Theory.OneGenerator` | T.4, T.1 | `combinedFlow_add` |
| T.6 | einselection; presence | `Theory.Einselection` | T.5, T.3 | **paper two's** `presence_conserved`, `pythagorean`, `arrow_is_loss_not_relocation` |
| T.7 | lived-identity coinduction `≈ := νΘ` | `Theory.We` | — | (theory's copy, supporting T.8) |
| T.8 | A2 priority / no-bare-carrier | `Theory.Priority` | T.7 | `priority_universal` |
| T.9 | the generative A3 engine | `Theory.MutualCoupling` | T.3 | `engine_ignition`, `orbit_engine2` |

## P1 — paper one's own nodes (`paper-1/`, `Scratch.*` / `RelExist.*`)

Single-importer today, so they stay `P1` (promote the day a second paper's Lean imports them). The seam spine,
lived identity, the knowing-is-lossy passage, and **the arrow**.

| # | Node | Module | Imports |
|---|---|---|---|
| P1.1 | the mirror | `RelExist.Mirror` | — |
| P1.2 | relating | `RelExist.Relating` | P1.1 |
| P1.3 | the seam | `RelExist.Seam` | P1.2 |
| P1.4 | seam bridge | `RelExist.SeamBridge` | P1.3 |
| P1.5 | lived identity `≈ := νΘ` (3.2) | `Scratch.We` | — |
| P1.6 | knowing is the lossy σ-move (3.3) | `Scratch.KnowingFeeling` | P1.5, P1.1 |
| P1.7 | `σ = Tr` as gfp (D1 realization) | `Scratch.Trace` | — |
| P1.8 | decoherence in the matrix model | `Scratch.Decoherence` | F.3 |
| P1.9 | directed attention | `Scratch.Attending` | P1.8 |
| P1.10 | the quantum seam | `Scratch.QuantumSeam` | P1.8 |
| P1.11 | the knower→known orientation | `Scratch.Orientation` | P1.10 |
| P1.12 | seam protection (forcing / conserved / ℂ) | `Scratch.SeamForcing` · `SeamConserved` · `SeamForcingC` | P1.9 |
| P1.13 | **the arrow** = time (3.8) | `Scratch.TimeFlow` | P1.11 | **paper one's arrow**: `coh_orbit_antitone` |
| P1.14 | the instance converse (3.10) | `Scratch.KnowingFromArrow` | P1.13, P1.12 |
| P1.15 | A3 at the strength of its text (3.9) | `Scratch.PhaseBearing` | T.3, P1.12 |

*Note (former P1.16).* `Scratch.CanonicalEigenform` (the spec-XX collision workaround) was **deleted in
handoff XXII** — XXI dissolved the collision, making it redundant with `Theory.Axioms.eigenform_of_fixed`,
which paper one now cites directly. The deletion was footprint-gated: paper one's headline footprints are
unchanged. P1 therefore ends at **P1.15**.

## P2 — paper two's own nodes (`paper-2/`)

**None.** Paper two is now a **thin layer** (handoff XXI): it imports the modular slice `T.4, T.5, T.6` (+
the band layer `T.1–T.3`) from `theory/` and proves nothing of its own in Lean. Its headline theorems live at
their canonical `T` addresses (T.6 `Theory.Einselection.*`, T.5 `Theory.OneGenerator.combinedFlow_add`); the
manuscript cites them there. Paper one's arrow is a **prose citation**, never imported.

## P3 — paper three's own nodes (`scratch/`, the living frontier)

| # | Node | Module | Status |
|---|---|---|---|
| P3.1 | decoherence conserves coherence (it relocates it) | `scratch/formal/Conservation.lean` | **frontier seed**, not gated |

*Recorded hoist-item (P3.1), not a violation.* `Conservation` *imports* paper one's `Scratch.Decoherence`
(P1.8). Because `scratch/` is a **free workbench** (XXII), this is **fine now** — the gate exempts scratch and
enforces cite-don't-import only at the **promotion event** (when scratch becomes paper three). At promotion,
resolve it by citing P1.8 in prose or hoisting the needed lemma to `theory/`.

---

## On physical file numbering

The numbering above is the **authoritative ordering**; the modules keep their **descriptive** names
(`Theory.BandFromAxioms`, not `Theory.T03`) because after Phase 2 the import graph *already* realizes the
proof DAG with legible names — the descriptive name carries the meaning, this index carries the order. A
manuscript cites *"`T.3` (eigenform / band coincidence, `Theory.BandFromAxioms`)"*: number for position, name
for content. (A future pass may prefix the files `T03_BandFromAxioms.lean` for a self-ordering listing; the
DAG and the addresses are unchanged by such a rename, so it is deferred as cosmetic ordering, not structure.)
