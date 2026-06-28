# `formal/` — mechanized development

Lean 4 formalization of Relational Existentialism, tracking [`docs/spec/`](../docs/spec/).

The development is split in two, matching the doctrine's split:

- **`RelExist`** — the dependency-free core (no mathlib): the Lawvere/seam results, **0 axioms**, builds in
  seconds.
- **`Scratch`** — the mathlib-backed half: the bisimulation `gfp`, the matrix/decoherence model, the
  arrow, and the energy band. Footprints sit at the corpus norm `[propext, Classical.choice, Quot.sound]`.

Everything **not** load-bearing for [paper one](../docs/spec/paper-one.md) — the cosmos/conservation
development (paper two), the sparsity development (paper three), the functorial-semantics layer, and the
route-1 reflexive-object scaffolding — lives under [`Archive/`](Archive) and is **not** built by default.
Its status ledger is the **[Archived — later papers](#archived--later-papers-formalarchive)** section
below, and it links [`docs/archive/`](../docs/archive/), not the active spec.

---

## Status — paper one, the kept closure

The active development is exactly the import-closure of paper one's headline theorems
([`Scratch.lean`](Scratch.lean)): 5 `RelExist` core modules + 16 `Scratch` modules. Each row links the
spec page it carries. Footprints verified via `#print axioms` (see [Build](#build)).

### Core — `RelExist` (no mathlib, audited 0 axioms)

| Result | Lean name (`RelExist.*`) | Spec | State |
| --- | --- | --- | --- |
| **3.3 σ-side** — Lawvere; the mirror can't close, with a remainder | `Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}` | [03.3](../docs/spec/03.3-knowing-vs-feeling.md), [00 §0.4.2](../docs/spec/00-doctrine.md) | ✅ **0 axioms** |
| **Limits of knowing** — one knowable case, three unknowable | `Relating.{disjoint_modelable, related_other_unmodelable, self_inclusive_unmodelable, no_complete_view}` | [03.4](../docs/spec/03.4-limits-of-knowing.md) | ✅ **0 axioms** |
| **The seam** — the one trace a self cannot take on itself | `Seam.{disjoint_trace_exists, self_cannot_trace_relation, self_cannot_view_relation}` | [03.5](../docs/spec/03.5-decoherence.md) | ✅ **0 axioms** |
| **Seam bridge A** — the abstract Lawvere agent is a *supplied* map (set-level forgetting, no longer posited). *Not new math* (Lawvere at `Env = Self` + trivial projection lossiness) | `SeamBridge.{forget, forget_lossy, no_faithful_self_trace, seam_on_forgetting}` | [03.5](../docs/spec/03.5-decoherence.md) | ✅ **0 axioms** |
| **Traced SMC typeclass** — the doctrine's ambient structure (full JSV axiom set), a typeclass mathlib lacks | `Traced.TracedSMC` | [00](../docs/spec/00-doctrine.md), [01](../docs/spec/01-signature.md) | ✅ defined, axiom-free |

Lawvere's theorem (`RelExist.Mirror.lawvere`) and its consequences depend on **no axioms whatsoever** —
fitting, since the mirror's incompleteness is the contrapositive of a one-line diagonal, not an assumption.

### The arrow and the energy band — `Scratch` (mathlib-backed)

| Result | Lean name (`RelExist.*`) | Spec | State |
| --- | --- | --- | --- |
| **D1 / 3.1** — self-relation is feedback; to relate is to create (`νP`, Knaster–Tarski) | `Trace.{selfTrace, selfTrace_fixed, Tr, Tr_fixed, le_Tr, Tr_mono}` | [D1](../docs/spec/02-axioms.md), [03.1](../docs/spec/03.1-to-relate-is-to-create.md) | ✅ proved |
| **3.2** — lived identity `≈ := νΘ`, coinduction, equivalence, shared world `𝔼 := D/≈` | `We.{bisim, bisim_unfold, bisim_coind, bisim_refl, bisim_symm, bisim_trans, World}` | [03.2](../docs/spec/03.2-lived-identity.md) | ✅ proved |
| **3.3 contrast** — knowing obstructed; feeling reflexive (the type-level asymmetry) | `KnowingFeeling.{knowing_can_fail_to_close, no_complete_boolModel, feeling_is_reflexive}` | [03.3](../docs/spec/03.3-knowing-vs-feeling.md) | ✅ proved |
| **The matrix instance** — finite matrices, `⊗` = Kronecker, trace = partial trace | `MatrixModel.matTracedSMC`, `PartialTrace.ptrace` | [03.4](../docs/spec/03.4-limits-of-knowing.md)–[03.5](../docs/spec/03.5-decoherence.md) | ✅ proved |
| **Knowing decoheres** — the σ-move retracts onto the classical shadow; the copy-defect | `Decoherence.{dephase, copyDefect, copyDefect_eq_zero_iff, defectSq, classical_comm}` | [03.5](../docs/spec/03.5-decoherence.md) | ✅ proved |
| **Directed attention** — selective decoherence; the defect only drops | `Decoherence.{attend, defectSq_attend_le, defectSq_attend_mono, defectSq_attend_plus_lt, defectSq_attend_shared_pos}` | [03.5](../docs/spec/03.5-decoherence.md) | ✅ proved |
| **The seam forces the subalgebra** — the un-attendable block survives every available knowing (operational seam, over ℝ) | `SeamForcing.{attend_fixes_seam, knowSeam, self_cannot_fully_decohere, seam_forces_subalgebra, direction_uniform_in_seam, target_depends_on_seam}` | [03.5](../docs/spec/03.5-decoherence.md), [03.6](../docs/spec/03.6-time-flow.md) | ✅ proved |
| **The spine in one ℂ field** — operational seam, arrow, flow, and energy band all over ℂ (with the `‖·‖²` coherence `defectSqC`); the ℝ shadow's missing rotating band is now a remark, not a model boundary | `Decoherence.{defectSqC, defectSqC_eq_zero_iff}`, `SeamForcing.self_cannot_fully_decohereC` | [03.8](../docs/spec/03.8-space-energy.md) | ✅ proved |
| **The quantum seam (route 2, first cut)** — the seam on the actual `dephase`: lossy, irreversible, via no-broadcasting | `QuantumSeam.{dephase_not_injective, no_dephase_recovery, dephase_fixes_iff_copyable}` | [03.5](../docs/spec/03.5-decoherence.md) | ✅ proved |
| **Orientation from the seam** — the lossy idempotent `E` generates the directed, temporal, irreversible knower→known arrow (ℝ *and* ℂ) | `Orientation.{Knowing, knows_antisymm, arrow_strictAnti, no_recovery, dephaseKnowing, dephaseKnowingC, dephaseC_arrow_plusC_strictAnti, dephaseC_no_recovery}` | [03.5](../docs/spec/03.5-decoherence.md), [03.6](../docs/spec/03.6-time-flow.md) | ✅ proved |
| **Time as flow** — the graded monovariant: coherence antitone, strictly dropping, geometric decay to the fixed set (ℝ *and* ℂ) | `TimeFlow.{Flow, Flow.coh_orbit_antitone, Flow.coh_orbit_strictAnti, GeometricFlow.coh_orbit_tendsto_zero, dephaseFlow, dephaseFlowC, defectSqC_iterate, defectSqC_plusC_tendsto_zero}` | [03.6](../docs/spec/03.6-time-flow.md) | ✅ proved |
| **An arrow's limit is a knowing** (instance converse) | `KnowingFromArrow.{arrow_limit_is_knowing, limit_idempotent, limit_is_seam_CE, limit_annihilates_potential}` | [03.7](../docs/spec/03.7-knowing-from-arrow.md) | ✅ proved |
| **Energy = the rotating band** — the phase-damping channel splits into fixed / rotating / transient; one generator `L = log μ`, energy its imaginary spectrum | `RotatingSpectrum.{schur, schur_fixed, schur_sustained, schur_transient_tendsto, phaseChannel_eigen, schur_iterate_norm_exp, genReal, genImag, energy}` | [03.8](../docs/spec/03.8-space-energy.md) | ✅ proved |
| **Band coincidence (spectral)** — on one carrier, the conserved-band predicate = rotating (energy) band; the witness and the counter-witness | `BandCoincidence.{seamBand, rotatingBand, band_coincidence, coincidence_witness, three_term_without_alignment}` | [03.9](../docs/spec/03.9-band-coincidence.md) | ✅ proved (under the C1 reading) |
| **…from A1–A3** — A3's `Peri(Φ_c)` *is* the conserved band; alignment follows from contractivity + nondegeneracy once the spectral band is read as C1 | `BandFromAxioms.{Peri, peri_iff_mem_conservedBand, conservedOffdiag, conservedOffdiag_iff_offdiag_conserved, align_of_contractive, band_coincidence_from_axioms, seam_energy_sustained}` | [03.9](../docs/spec/03.9-band-coincidence.md) | ✅ proved (C1 a disclosed reading) |
| **Step two — the bridge test** — operational seam *is* the operationally-conserved band, **exactly & structurally** (seam pinned from attention, no `‖μ‖`); `= energy` stays open, obstruction named (the 0/1 attention channel has no rotating spectrum, so its conserved edges are *fixed*, not energy) | `SeamConserved.{offdiag_conserved_iff_seam, seam_edge_exact, attend_fixes_are_identity}` | [03.9](../docs/spec/03.9-band-coincidence.md) | ✅ proved (theorem + named obstruction) |

`Scratch.We` formalizes **theorem 3.2** as `νΘ = OrderHom.gfp Θ`, with coinduction, the equivalence
proof, and the shared world `𝔼 := D/≈`. This lattice-theoretic reading has a second, independent
mechanization in the [`agda/`](../agda/) layer (native coinduction / copatterns), agreeing on the
doctrine's lived identity.

**What the kept tags do — and do not — claim** (see [paper one](../docs/spec/paper-one.md) honest scope):
the proved skeleton is `[proved]`; that the conserved band *is* energy, and that the flow *is* physical
time, are `[reading]`s. The seam↔energy joint was *tested* in step two (`SeamConserved`): **proved** that
the operational seam *is* the operationally-conserved band, exactly and structurally
(`offdiag_conserved_iff_seam`, seam pinned from attention with no `‖μ‖`); **still `[open]`** that this is
the *rotating energy* band, with a named obstruction — the attention channel is 0/1, so its conserved
edges are *fixed*, never rotating, and linking it to the phase channel `schur μ` is a single cross-channel
posit (`Align`). **C1** (self = `Peri(Φ_c)`, beyond A3's formalized `νΦ_c`) is a disclosed posit/reading,
not a derivation.

---

## Build

```sh
cd formal
lake build            # the dependency-free core (RelExist) — fast, no mathlib
lake build Scratch    # the mathlib-backed target — compiles mathlib on first run
```

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.15.0`). Audit any proof's axiom footprint with:

```sh
lake env lean -e '#print axioms RelExist.Seam.self_cannot_trace_relation'   # → no axioms
lake env lean -e '#print axioms RelExist.BandFromAxioms.band_coincidence_from_axioms'  # → corpus norm
```

### One-command setup — `scripts/bootstrap.sh`

[`scripts/bootstrap.sh`](scripts/bootstrap.sh) installs everything idempotently:
`elan`, the Lean toolchain, the core build, and (unless `SKIP_MATHLIB=1`) the
mathlib-backed target.

```sh
formal/scripts/bootstrap.sh                  # toolchain + core + mathlib
SKIP_MATHLIB=1 formal/scripts/bootstrap.sh   # toolchain + core only (seconds)
```

It is written for the network policy in our remote sessions — `github.com` +
`pypi.org` allowed, but `release.lean-lang.org` / `api.github.com` and the mathlib
cache blob blocked. So it installs the toolchain by **direct GitHub download**
(decompressing the `.tar.zst` via the `zstandard` PyPI module, since there is no
`zstd` binary) and **compiles mathlib from source** (no cache). With a permissive
policy none of these workarounds are needed — `elan` and `lake exe cache get` do it
automatically.

### Reusable container (Claude Code on the web)

A `SessionStart` hook ([`.claude/hooks/session-start.sh`](../.claude/hooks/session-start.sh),
registered in [`.claude/settings.json`](../.claude/settings.json)) runs
`bootstrap.sh` at the start of every **remote** session and persists the toolchain
on `PATH`. The first remote session compiles the mathlib slice once (≈4 min for the
current imports); the platform then caches the container state, so later sessions
start with Lean + mathlib already built. The hook no-ops in local (non-remote)
sessions. Once merged to the default branch, all future sessions pick it up.

---

## Archived — later papers (`formal/Archive/`)

The supporting development is **kept, not foregrounded**: mechanized and `sorry`-free, but not
load-bearing for paper one. It lives under [`Archive/`](Archive) (quarantined, not built by default) and
tracks [`docs/archive/`](../docs/archive/). Grouped by the paper it belongs to.

### Paper two — conservation, the cosmos, identity residue, causation

| Area | Lean (`RelExist.*`, under `Archive/`) | Archive spec |
| --- | --- | --- |
| Decoherence **is** the partial trace; coherence conserved, relocated | `Conservation.{entangle, decoherence_is_partial_trace, copyDefect_entangle_ne, trace_conserved}` | [03-theorems](../docs/archive/03-theorems.md) |
| The seam on the genuine `ptrace` (compact face; route 1 firewall-obstructed) | `QuantumSeamTrace.{ptrace_collapses_entanglement, no_ptrace_recovery, unresolved_fiber_is_coherence, route1_needs_copy_blocked}` | [03-theorems](../docs/archive/03-theorems.md) |
| Inside ⊊ outside — `≈ ⊊ ≅`; soundness; the first-person surplus; one-forgetting | `Identity.{ObsEq, bisim_le_obsEq, bisim_ne_obsEq, livedToObserved_not_injective, deterministic_bisim_iff_obsEq}`, `Forgetting.{Coarsening, forgettings_have_residue}` | [03-theorems](../docs/archive/03-theorems.md) |
| The relational/disjoint bridge; relativized appearance `≅ₒ` | `Knowing.{knowing_complete_iff_disjoint, witness_disjoint_vs_related}`, `RelationalAppearance.{bisim_le_obsEqVia, deterministic_relational_surplus}` | [03-theorems](../docs/archive/03-theorems.md) |
| Nondeterminism is a consequence of relation; robustly; the missing cause is the other; knowing decoheres | `Marginal.*`, `RelationalMarginal.*`, `Causation.{condStep_deterministic, indeterminism_is_unviewed_cause, knowing_decoheres}` | [03-theorems](../docs/archive/03-theorems.md) |
| Feeling **modeled** as a decoherence differential (`[reading]`, not identification) | `Feeling.{feel, feel_unshared, feel_shared, feel_le_between, betrayal_feel}` | [03-theorems](../docs/archive/03-theorems.md) |
| `reg` derived from the dynamics (registration is absorption) | `Registration.{Registering, reg_absorbs, no_complete_view_of_registering}` | [03-theorems](../docs/archive/03-theorems.md) |
| The self quantified; distributed self; cosmos readings | `Distribution.{distributed, distributed_bound, total_feedback, sustained_unique}`, `Feedback.{CoDirectedSelf, latticeSelf, banachSelf}` | [03.6-the-self-quantified](../docs/archive/03.6-the-self-quantified.md), [03.12–03.14](../docs/archive/) |
| Attention as co-directed eigenstructure (registration, accumulation) | `Attention.{couplingOp, couplingOp_mono, sustainedField, orbit_ascending, relating_absorbs, closed_loop_registers}` | [03-theorems](../docs/archive/03-theorems.md) |

### Paper three — sparsity of selfhood

| Area | Lean (`RelExist.*`, under `Archive/`) | Archive spec |
| --- | --- | --- |
| Discrete counting bound; sparsity from a budget; collapse without one | `stab_card_bound`, `stab_card_le_div`, `stab_card_le_half`, `unbounded_without_budget` | [03.7-sparsity](../docs/archive/03.7-sparsity.md) |
| The loop bridge (threshold ⟺ fixed point); the two residue posits discharged | `Loop.{loopR_isEigen_iff, …}`, `Convergence.*`, `Stabilization.*`, `SparsityPosits.*` | [03.7-sparsity](../docs/archive/03.7-sparsity.md) |
| ℝ-valued density → 0; cost-graded dichotomy; nowhere-dense (Agda) | `SparsityReal.stab_density_tendsto_zero`, `SparsityCapstone.{conjecture_3_7, cost_graded_density_tendsto_zero}` | [03.7-sparsity](../docs/archive/03.7-sparsity.md) |
| Spectral lift — decay dynamics, Perron–Frobenius existence, peripheral standard form | `SpectralDecay.spectral_decay`, `PerronFrobenius.{exists_invariant_vector, exists_invariant_state}`, `PeripheralAlgebra.{fix_comm, dephaseStandardForm}` | [03.7-sparsity](../docs/archive/03.7-sparsity.md) |

### The functorial-semantics layer (Layer 4) and the `Int`/reflexive-object scaffolding

| Area | Lean (`RelExist.*`, under `Archive/`) | Archive spec |
| --- | --- | --- |
| Domain functors — chemistry, biology, AI | `Chemistry.*`, `Biology.*`, `Recurrence.{feedback_eq_trace, sustained}` | [04-functorial-semantics](../docs/archive/04-functorial-semantics.md) |
| The firewall — compact-closed + cartesian ⇒ thin; no-cloning | `Compact.{collapse, no_cloning}`, `NoCloning.no_linear_clone`, `Firewall.joint_factors` | [04-functorial-semantics](../docs/archive/04-functorial-semantics.md) |
| The free `Cl(𝕋)`, universal functor, coherence refinement | `Free.{clTracedSMC, functor, functor_unique, clCoherentTracedSMC}`, `RelModel.*` | [04-functorial-semantics](../docs/archive/04-functorial-semantics.md) |
| Conway fixpoint-trace on domains (Hasegawa "only-if") | `DomainFixpoint.domainFixpointTracedSMC`, `ConwayTrace.*` | [04-functorial-semantics](../docs/archive/04-functorial-semantics.md) |
| The `Int`/GoI construction; `Rel` compact closed; reflexive objects (`Pω`, `ℕ`) | `IntConstruction.{IntCompose}`, `RelCompact.*`, `GraphModel.*`, `SelfApplication.*`, `ReflexiveSeam.*`, `ReflexiveModel.*`, `ReflexiveCompact.*` | [04-functorial-semantics](../docs/archive/04-functorial-semantics.md) |

For the full provenance accounting of the archived results — tier (rederivation / synthesis), prior art,
and the named residues — see [`docs/spec/04-provenance.md`](../docs/spec/04-provenance.md) and the
[`docs/archive/`](../docs/archive/) pages. The archive's own cross-links are unmaintained by design.
