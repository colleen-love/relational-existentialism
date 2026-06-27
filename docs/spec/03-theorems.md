# 03 — Theorems: the catalog

> *Given the axioms **A1–A3** and the definition **D1** ([02](02-axioms.md)), what actually
> follows?* This page is the **index and categorized catalog** of Chapter 3. Every result the
> theory proves is numbered here, sorted into its category, tagged with its proof status, and —
> where it is a re-proof of established mathematics — cited as such. The detailed per-result
> ledger is [05 — Provenance](05-provenance.md); this page is the map.

---

## The numbering scheme

Chapter 3 is organized so that **every result is numbered like every other** — there are no longer
"named" theorems (the old `T1`/`T2`/`T3`) standing apart from the rest by accident of history.

- **`3.x`** — the **capstone** theorem or conjecture of section `x`, each on its own page.
- **`3.x.y`** — a **lemma**, sub-conjecture, or property *within* section `x`.

| § | Capstone | Page |
| --- | --- | --- |
| **3.1** | To relate is to create | [`03.1-to-relate-is-to-create.md`](03.1-to-relate-is-to-create.md) |
| **3.2** | Lived identity and the "we" | [`03.2-lived-identity.md`](03.2-lived-identity.md) |
| **3.3** | Knowing vs feeling | [`03.3-knowing-vs-feeling.md`](03.3-knowing-vs-feeling.md) |
| **3.4** | The limits of knowing | [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md) |
| **3.5** | Decoherence and the trace | [`03.5-decoherence.md`](03.5-decoherence.md) |
| **3.6** | The self quantified | [`03.6-the-self-quantified.md`](03.6-the-self-quantified.md) |
| **3.7** | Sparsity (the quantitative capstone) | [`03.7-sparsity.md`](03.7-sparsity.md) |

The dependency is one-way: **A1, A2, A3, D1 ⟹ 3.1, 3.2, 3.3 ⟹ 3.4–3.7.**

The **derivation sequels** (`3.8+`) carry the time/space/energy/cosmos developments, each numbered like
the rest and backed by its own Lean module:

| § | Capstone | Page |
| --- | --- | --- |
| **3.8** | Time as flow | [`03.8-time-flow.md`](03.8-time-flow.md) |
| **3.9** | Space and energy (one generator, three aspects) | [`03.9-space-energy.md`](03.9-space-energy.md) |
| **3.10** | From the arrow back to the knowing (the converse) | [`03.10-knowing-from-arrow.md`](03.10-knowing-from-arrow.md) |
| **3.11** | Seam permanence (the knowing never completes) | [`03.11-seam-permanence.md`](03.11-seam-permanence.md) |
| **3.12** | Universe and cosmos (the genesis of time) | [`03.12-universe-and-cosmos.md`](03.12-universe-and-cosmos.md) |
| **3.13** | The distributed self | [`03.13-distributed-self.md`](03.13-distributed-self.md) |
| **3.14** | The cosmos has been knowing itself | [`03.14-cosmos-knowing-itself.md`](03.14-cosmos-knowing-itself.md) |

## Two legends every row carries

**Proof status** — *can a machine check it?*

| Tag | Meaning |
| --- | --- |
| `[proved]` | mechanized in Lean/Agda (name given); footprint by `#print axioms` |
| `[follows]` | forced by the structure, but not (yet) mechanized |
| `[reading]` | an interpretation the structure invites but does not compel |
| `[open]` | a genuine target the prose has claimed but the formalization has **not** established |

**Provenance tier** — *is the mathematics new?* (full ledger in [05](05-provenance.md))

| Tier | Meaning |
| --- | --- |
| **R** | **Rederivation** — established mathematics, re-proved here to have it inside the corpus with an audited axiom footprint. Novelty ≈ 0; value is the machine-checked artifact. |
| **R / S** | Rederivation in content, **synthesis** in framing: the theorem is old, the recognition that it *is* this phenomenon is the contribution. |
| **S** | **Synthesis** — a non-obvious identification or transport across domains the literature keeps apart. |
| **N? (reading)** | a philosophical **reading** mounted on a theorem; honest only as a lens, never as proof. |

> **The one-sentence honest claim.** The mathematical content of this development is, almost
> entirely, **rederivation** (bisimulation, Lawvere, traced monoidal categories, the partial
> trace, Banach/Neumann series, Perron–Frobenius, the GoI/`Int` construction). The contribution is
> a **synthesis** — one typed identification across decoherence, fixed-point logic, and relational
> dynamics — plus the **mechanization artifact**. The single *structurally new* theorem the
> framework's commitments promised, **orientation-from-the-seam** ([3.5](03.5-decoherence.md)), is
> proved at its structural core. None of it is new mathematics. See [05](05-provenance.md).

---

## Category I — the foundational theorems (3.1–3.3)

The three results the basis forces directly. Each is now a standalone page with parity to the rest.

| # | Result | Status | Tier | Prior art (rederivation) | Lean / Agda |
| --- | --- | --- | --- | --- | --- |
| **3.1** | To relate is to create — self-relation `σ = Tr` has a fixed point (the eigenform) | `[proved]` | **R** | Knaster–Tarski; Hasegawa/Hyland (trace ↔ Conway operator) | `Trace.{selfTrace, selfTrace_fixed, Tr_fixed, le_Tr, Tr_mono}` |
| **3.2** | Lived identity `≈ := νΘ`, the shared world `𝔼 := D/≈`, the irreducible seam | `[proved]` | **R / S** | Park, Milner (bisimulation); Aczel; Rutten (coalgebra) | `We.{bisim, bisim_coind, World}`; Agda `Coinductive._≈_` |
| **3.2** | `≈ ⊊ ≅` — lived identity strictly exceeds observation (soundness + strictness) | `[proved]` | **R / S** | van Glabbeek (branching-time spectrum); Hennessy–Milner | `Identity.{ObsEq, bisim_le_obsEq, bisim_ne_obsEq}` |
| **3.2.1** | full naturality of the no-master-section beyond point-surjectivity | `[open]` | — | — | — |
| **3.3** | Knowing vs feeling — the σ-move is Lawvere-obstructed; feeling is type-level exempt | `[proved, 0 ax]` | **R / S** | Lawvere (1969); Yanofsky (survey) | `Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}`; `KnowingFeeling.*` |

## Category II — the limits of knowing, and the seam (3.4)

What can and cannot be known once relating creates shared constitution. The Lawvere obstruction,
generalized to the *other* and the *collection*. Full page: [03.4](03.4-limits-of-knowing.md).

| Result | Status | Tier | Prior art | Lean |
| --- | --- | --- | --- | --- |
| One knowable case (disjoint), three unknowable (other / self / collection) | `[proved, 0 ax]` | **R / S** | Lawvere specialized | `Relating.{disjoint_modelable, related_other_unmodelable, self_inclusive_unmodelable, no_complete_view}` |
| `reg` derived from the dynamics — registration *is* absorption | `[proved]` | **S** | — (recognition) | `Registration.{Registering, reg_absorbs, no_complete_view_of_registering}` |
| completeness ⟺ disjointness — the relational floor dominates the branching surplus | `[proved, 0 ax]` | **R / S** | Lawvere/Cantor duality | `Knowing.{knowing_complete_iff_disjoint, witness_disjoint_vs_related}` |

## Category III — decoherence, the trace, and orientation (3.5)

What knowing *does* to a relation: it decoheres it, and the coherence is only relocated. The one
structurally new theorem of the corpus lives here. Full page: [03.5](03.5-decoherence.md).

| Result | Status | Tier | Prior art | Lean |
| --- | --- | --- | --- | --- |
| Knowing decoheres — `dephase` is a conditional expectation `E`; the copy-defect | `[proved]` | **R / S** | Joos–Zeh, Zurek (einselection) | `Decoherence.{dephase, copyDefect, classical_comm}` |
| Decoherence **is** the partial trace — coherence conserved, relocated | `[proved]` | **R / S** | reduced density matrix | `Conservation.{decoherence_is_partial_trace, trace_conserved}` |
| The seam — the one trace a self cannot take on itself | `[proved, 0 ax]` | **R / S** | Lawvere at `Env = Self` | `Seam.{self_cannot_trace_relation, self_cannot_view_relation}` |
| **Orientation from the seam** — the lossy idempotent `E` generates the knower→known arrow | `[proved]` | **R / S** (*the new theorem*) | Tomiyama, Umegaki (conditional expectations) | `Orientation.{Knowing, knows_antisymm, arrow_strictAnti, no_recovery}` |
| One forgetting, three residues — identity-collapse = dephasing = partial trace | `[proved]` | **S** | — (recognition) | `Forgetting.{Coarsening, not_injective_of_residue, forgettings_have_residue}` |
| Nondeterminism is a consequence of relation; the missing cause is the other | `[proved, 0 ax]` | **R / S** | open-system / causal factorization | `Marginal.*`, `RelationalMarginal.*`, `Causation.*` |
| Feeling, *modeled* as a relational decoherence differential | `[proved]` (model) | **N? (reading)** | — | `Feeling.{feel, feel_unshared, feel_le_between, betrayal_feel}` |

## Category IV — the self quantified (3.6)

How much of a self ends up in others, and the spectral reconciliation of *sparse* with *multiple*.
Full page: [03.6](03.6-the-self-quantified.md).

| Result | Status | Tier | Prior art | Lean |
| --- | --- | --- | --- | --- |
| Self-in-other bounded iff `‖x‖ < 1`; the quantitative eigenform is unique | `[proved]` | **R / S** | Neumann series; Banach fixed point | `Distribution.{distributed, distributed_bound, total_feedback, sustained_unique}` |
| Both selves (order-theoretic, quantitative) realize the ν-modality | `[proved]` | **S** | — (recognition) | `Feedback.{CoDirectedSelf, self_iterate, latticeSelf, banachSelf}` |
| Controlled multiplicity — selves `> 1` (contingency) yet `o(N)` (sparse) | `[proved]` | **R / S** | nonlinear Perron–Frobenius; covering numbers | `SpectralMultiplicity.{attracting_isolated, attractors_separated, two_attracting_selves, selves_density_tendsto_zero}` |

## Category V — the quantitative capstone: sparsity (3.7)

The one place the spec reaches for a quantitative headline. Full page: [03.7](03.7-sparsity.md).

| # | Result | Status | Tier | Prior art | Lean / Agda |
| --- | --- | --- | --- | --- | --- |
| **Lemma 3.7.1** | sparsity from a budget — `\|Stab_R\| ≤ β/(d·λ)`, density → 0 | `[proved]` | **R / S** | pigeonhole | `Sparsity.stab_card_bound`; `Real.stab_density_tendsto_zero` |
| **Lemma 3.7.2** | collapse without a bound — `β = ⊤ ⇒ Stab = Φ`, density 1 | `[proved]` | **R** | — | `Sparsity.unbounded_without_budget` |
| **Conjecture 3.7** | under a finite attention budget, selves are rare (sparse) | — | — | — | — |
| **Conjecture 3.7.3** | cost-graded form — sparsity for all of `Cl(𝕋)` | `[proved]` (exclusivity-conditioned) | **R / S** | cylinder topology; inclusion–exclusion | `SparsityCapstone.conjecture_3_7`; Agda `selves-nowhereDense` |
| **Conjecture 3.7.4** | spectral / closure form — few modes self-sustain; controlled multiplicity | `[proved]` (finite dim) | **R / S** | spectral gap; Perron–Frobenius | `Peripheral.*`, `SpectralDecay.*`, `PerronFrobenius.*`, `SpectralMultiplicity.*` |

---

## Derived notions

- **Self / eigenform** — a member of `Stab_R` ([A3](02-axioms.md)); a fixed point of funded, deep
  self-relation.
- **Distributed self** `[reading]` — for `e ∈ Stab_R`, its `≈`-image in `𝔼`; it persists in
  `≈`-neighbours on the timescale of their returning, even after `e`'s own loop opens. Quantified in
  [03.6](03.6-the-self-quantified.md).
- **Birth / death** `[follows]` — a fresh fixed point forced into being already coupled
  ([3.1](03.1-to-relate-is-to-create.md) + A3) / the loop `loop_R(e) = e` ceasing to hold as
  funding withdraws (A3 negated).

---

→ Back to [02 — The Axioms](02-axioms.md) · the foundational theorems
[03.1](03.1-to-relate-is-to-create.md) · [03.2](03.2-lived-identity.md) ·
[03.3](03.3-knowing-vs-feeling.md) · the structural results
[03.4](03.4-limits-of-knowing.md) · [03.5](03.5-decoherence.md) ·
[03.6](03.6-the-self-quantified.md) · [03.7](03.7-sparsity.md) · the functorial semantics are
[04](04-functorial-semantics.md) · the full provenance ledger is [05](05-provenance.md).
