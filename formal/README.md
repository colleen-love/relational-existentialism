# `formal/` — mechanized development

Lean 4 formalization of Relational Existentialism, tracking [`docs/spec/`](../docs/spec/).

## Status

| Result | Lean name (`RelExist.*`) | Spec source | State |
| --- | --- | --- | --- |
| Core counting bound | `min_mul_length_le_totalSpend` | [03 §3.2](../docs/spec/03.1-sparsity.md) | ✅ proved |
| **Lemma 3.1** (sparsity from a budget), division-free | `stab_card_bound` | [03 Lemma 3.1](../docs/spec/03.1-sparsity.md) | ✅ proved |
| Lemma 3.1, divided form `≤ β/m` | `stab_card_le_div` | [03 Lemma 3.1](../docs/spec/03.1-sparsity.md) | ✅ proved |
| Sparsity at depth `d ≥ 2` (`≤ β/2`) | `stab_card_le_half` | [03 §3.2](../docs/spec/03.1-sparsity.md) + [A3](../docs/spec/02-axioms.md) | ✅ proved |
| **Lemma 3.2** (collapse without a bound) | `unbounded_without_budget` | [03 Lemma 3.2](../docs/spec/03.1-sparsity.md) | ✅ proved |

All five are `sorry`-free; their only axiom dependency is `propext` (verified via
`#print axioms`). This is the **discrete (ℕ-valued) core** of the sparsity
dichotomy: a finite attention budget, divided among selves each costing at least a
positive floor, bounds the number of selves independently of how many couplings
exist — and remove the budget and that bound collapses.

The core (`RelExist`) is deliberately **dependency-free (no mathlib)** so it builds
in seconds even where mathlib's cache is unreachable.

### The loop bridge — step 3 (core, no mathlib)

This **partly** addresses the gap the spec flagged ([03 §3.3](../docs/spec/03.1-sparsity.md)):
the sparsity lemmas count with a *threshold*, but [A3](../docs/spec/02-axioms.md) defines a self as
a **fixed point** of self-relation. The bridge ([`RelExist/Loop.lean`](RelExist/Loop.lean)) connects
them — but for an *abstract* endomap `σ` (not the relational `Φ_c`), with the eigenform-`⟺`-`N≥d`
step definitional and the rest one arithmetic lemma. It does **not** force the depth floor `d ≥ 2`.

| Result | Lean name (`RelExist.*`) | Meaning | State |
| --- | --- | --- | --- |
| `loop_R(e) = e ⟺ N(e) ≥ d(e)` | `loopR_isEigen_iff_le_fundedReturns` | budgeted loop is an eigenform iff budget funds depth-many returns | ✅ proved |
| `loop_R(e) = e ⟺ d·λ ≤ β` | `loopR_isEigen_iff` / `loopR_isEigen_iff_selfCost` | …iff the budget covers the self's cost (the resource threshold) | ✅ proved |
| cost floor `2 ≤ d·λ` (relocated) | `two_le_selfCost` | depth `≥ 2` (A3) ⇒ cost `≥ 2`: trivial arithmetic; the posit is the **depth** `d ≥ 2`, not derived | ✅ proved |
| witness model is non-vacuous | `matarN_stabilizesAt` | a concrete maturation dynamics `StabilizesAt` depth `d` — but builds `d` in by its cap | ✅ proved |
| capstone | `stab_card_le_half_of_depths` | selves with depths `≥ 2`, total cost `≤ β`, number `≤ β/2`; floor **relocated to the depth posit**, not discharged | ✅ proved |

So A3's *abstract* fixed point and the counted threshold are provably interchangeable, and the
sparsity bound's cost floor is shown to follow from the **depth posit `d ≥ 2`**.

**The abstract `σ`, now discharged for the depth** ([`Scratch/Convergence.lean`](Scratch/Convergence.lean)).
The same open seam recurs across all four pages — nearly every result runs over an *abstract proxy* for
`Φ_c`, and the identification with the genuine operator is the standing reading. `Convergence.lean`
takes that bridge at the node where it pays off most: it derives `Loop`'s depth structure from the
**convergence behaviour of `Φ_c`'s orbit directly**. `iter_eq_iterate` (Loop's `iter` *is* `Φ^[n]`),
`ConvergesAt` (the intrinsic convergence depth), and `convergesAt_imp_stabilizesAt` `[0 axioms]`
*derive* `StabilizesAt` from convergence; `couplingOp_loopR_isEigen_iff` then runs Loop's whole
threshold↔fixed-point bridge over the **genuine `Φ_c = couplingOp c`**, with `d` its orbit's
convergence depth (`convergedValue_le_sustained` ties the converged value to `νΦ_c`). And
`selfCost_le_valuationGain` reads the per-return cost `λ` off the orbit's standing increment, given a
valuation.

**Does the orbit converge? Two honest answers** ([`Scratch/Stabilization.lean`](Scratch/Stabilization.lean)).
The frontier `Convergence.lean` left — *does `Φ_c`'s orbit actually reach a fixed point?* — is now
answered in the two regimes it splits into. **ω-convergence (always, under continuity):**
`iSup_orbit_isFixed` — the orbit's supremum `⨆ Φ^[n] a` is a fixed point whenever `Φ` commutes with
that sup, a genuine self in `[a, νΦ_c]` (`iSup_orbit_le_sustained`); the self *is* the limit of
relating, no finiteness needed (Kleene). **Finite-depth convergence (iff ACC):**
`convergesAt_of_stabilizes` `[0 axioms]` (stabilizing ⇒ a least convergence depth) and
`orbit_stabilizes` (under `WellFoundedGT (Field V α)` — no infinite ascending chains of standing — the
monotone orbit *must* stabilize, via `WellFounded.monotone_chain_condition`) combine in
`couplingOp_selfForms`: under ACC the genuine `Φ_c` orbit forms a self at a finite depth and satisfies
`Loop`'s `StabilizesAt`. So the cost model's depth posit is **discharged for the real operator**, and
the only residue is a single standard order condition — **ACC on standing** ("a self forms in finitely
many returns"), automatic for finite standing-lattices. The structural rarity is still carried
independently by the Agda nowhere-dense result.

### Doctrine commitments — D1, T1, T3

The three previously prose-only axioms, mechanized via their essential mathematical
content. (The abstract *traced symmetric monoidal category* typeclass is deliberately
not reproduced — large categorical infrastructure; what the axioms invoke is here.)

| Result | Lean name | Spec | Target | State |
| --- | --- | --- | --- | --- |
| **T3 σ-side** — Lawvere; the mirror can't close | `RelExist.Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}` | [T3](../docs/spec/03-theorems.md), [00 §0.4.2](../docs/spec/00-doctrine.md) | core (no mathlib) | ✅ **0 axioms** |
| **D1** — self-relation is feedback (`νP`) | `RelExist.Trace.{selfTrace, selfTrace_fixed}` | [D1](../docs/spec/02-axioms.md) | Scratch | ✅ proved |
| **T1** — to relate is to create (Conway `Tr`) | `RelExist.Trace.{Tr, Tr_fixed, le_Tr, Tr_mono}` | [T1](../docs/spec/03-theorems.md) | Scratch | ✅ proved |
| **T3 contrast** — knowing obstructed; feeling is reflexive (type-level asymmetry) | `RelExist.KnowingFeeling.{knowing_can_fail_to_close, no_complete_boolModel, feeling_is_reflexive}` | [T3](../docs/spec/03-theorems.md) | Scratch | ✅ proved |

### The limits of knowing, decoherence, and the seam

The relational consequences of the Lawvere obstruction — what can and cannot be known, what
knowing *does* to a relation, and the one trace a self cannot take on itself.

| Result | Lean name | Spec | Target | State |
| --- | --- | --- | --- | --- |
| **Limits of knowing** — one knowable case, three unknowable | `RelExist.Relating.{disjoint_modelable, related_other_unmodelable, self_inclusive_unmodelable, no_complete_view}` | [03.2](../docs/spec/03.2-limits-of-knowing.md) | core (no mathlib) | ✅ **0 axioms** |
| **The seam** — the trace a self cannot take | `RelExist.Seam.{disjoint_trace_exists, self_cannot_trace_relation, self_cannot_view_relation}` | [03.3](../docs/spec/03.3-decoherence.md) | core (no mathlib) | ✅ **0 axioms** |
| **`reg` derived from the dynamics** — registration *is* absorption; the obstruction with `reg` grounded in `Φ_c` (not posited) | `RelExist.Registration.{Registering, reg_absorbs, no_complete_view_of_registering}` | [03.2](../docs/spec/03.2-limits-of-knowing.md) | Scratch | ✅ proved (`no_complete_view_of_registering` **0 axioms**) |
| **Inside ⊊ outside** — identity `≈` exceeds observation `≅` (A2 restated) | `RelExist.Identity.{ObsEq, bisim_le_obsEq, bisim_ne_obsEq, livedToObserved_not_injective}` | [02 A2](../docs/spec/02-axioms.md), [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **The surplus is exactly nondeterminism** — `Deterministic ⟹ ≈ ⟺ ≅`; the witness branches | `RelExist.Identity.{Deterministic, deterministic_bisim_iff_obsEq, deterministic_obsEq_imp_bisim, not_deterministic_stepW}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **The requirements for the surplus** — nondeterminism ∧ a relating; exact boundary `surplus ⟺ ≅ not a bisimulation`; both necessary, jointly insufficient | `RelExist.Identity.{IsBisimulation, surplus_iff_obsEq_not_isBisimulation, surplus_imp_not_deterministic, surplus_imp_relating, nondeterminism_and_selves_insufficient}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **The bridge** — the gap is governed by relation; `≅` is the *disjoint* observer; completeness ⟺ disjointness, so the necessary Lawvere floor dominates the contingent branching surplus | `RelExist.Knowing.{traceView, obsEq_iff_traceView_eq, knowing_complete_iff_disjoint, witness_disjoint_vs_related}` | [03.2](../docs/spec/03.2-limits-of-knowing.md), [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved (`knowing_complete_iff_disjoint` **0 axioms**) |
| **Nondeterminism is a consequence of relation** — deterministic whole, related across a between ⟹ nondeterministic marginal; local determinism ⟺ no relation; the seam forces the marginal view | `RelExist.Marginal.{jointStep_deterministic, marginal_deterministic_iff_disentangled, marginal_nondeterministic_iff_entangled, relation_makes_marginal_nondeterministic}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved (`marginal_deterministic_iff_disentangled` **0 axioms**) |
| **…robustly, for any global law** — relation manufactures openness whatever the physics of the whole; deterministic-whole conservation is the priced corollary; survives a nondeterministic universe | `RelExist.RelationalMarginal.{entangledRel_imp_marginal_nondeterministic, deterministic_whole_marginal_open, marginalRel_graph, robust_survives_nondeterministic_whole}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved (**all 0 axioms**) |
| **One forgetting** — identity-collapse, dephasing, partial trace are one shape | `RelExist.Forgetting.{Coarsening, not_injective_of_residue, forgettings_have_residue}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **Knowing decoheres** — dephasing onto the classical fragment | `RelExist.Decoherence.{dephase, copyDefect, copyDefect_eq_zero_iff, classical_comm}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **Directed attention** — selective decoherence; the defect drops | `RelExist.Decoherence.{attend, defectSq_attend_le, defectSq_attend_mono, defectSq_attend_plus_lt, defectSq_attend_shared_pos}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **Decoherence is the partial trace** — coherence conserved, relocated | `RelExist.Conservation.{entangle, decoherence_is_partial_trace, copyDefect_entangle_ne, trace_conserved}` | [03.3](../docs/spec/03.3-decoherence.md) | Scratch | ✅ proved |
| **Self-in-other quantified** — the Banach-algebra bound and eigenform | `RelExist.Distribution.{distributed, distributed_bound, total_feedback, sustained_unique}` | [03.4](../docs/spec/03.4-the-self-quantified.md) | Scratch | ✅ proved |
| **Unifying the two selves** — both realize the ν-modality | `RelExist.Feedback.{CoDirectedSelf, self_iterate, latticeSelf, banachSelf}` | [03.4](../docs/spec/03.4-the-self-quantified.md) | Scratch | ✅ proved |

Lawvere's theorem (`RelExist.Mirror.lawvere`) and its consequences are **fully
constructive** — they depend on *no axioms whatsoever*, which is fitting: the mirror's
incompleteness is not an assumption but the contrapositive of a one-line diagonal.

### Layer 4 — functorial semantics (domains)

The domain functors — chemistry, physics, biology, AI — and the firewall (all five domains;
[spec 04](../docs/spec/04-functorial-semantics.md)).

| Result | Lean name | Meaning | State |
| --- | --- | --- | --- |
| autocatalytic core = eigenform `νΦ` | `RelExist.Chemistry.{autocatalyticCore, autocatalyticCore_selfSustaining, autocatalytic_greatest}` | a self-sustaining reaction set is a fixed point | ✅ proved |
| **the chemistry functor, witnessed** | `RelExist.Chemistry.selfTrace_eq_autocatalyticCore` | the theory's `νP` *is* the autocatalytic core (definitional) | ✅ proved |
| **biology: (M,R)-systems** | `RelExist.Biology.{organism, mr_cycle_closes, closed_to_efficient_causation, selfTrace_eq_organism}` | closure to efficient causation = the organism `ν(repair ∘ metabolize)`; the functor is definitional | ✅ proved |
| firewall, `Type`-level (cartesian joints factor) | `RelExist.Firewall.{copy, joint_factors}` | cartesian joints factor ⇒ no entanglement | ✅ proved |
| **firewall, categorical (the collapse)** | `RelExist.Compact.collapse` | compact-closed + cartesian copying ⇒ **thin** | ✅ proved |
| **no-cloning, categorical** | `RelExist.Compact.no_cloning` | a non-trivial compact-closed structure admits no copying | ✅ proved |
| **no-cloning, concrete (physics)** | `RelExist.NoCloning.no_linear_clone` | cloning `x ↦ x²` (`≅ x ↦ x⊗x`) is nonlinear | ✅ proved |
| **physics: the literal traced SMC** | `RelExist.MatrixModel.matTracedSMC` | matrices, `⊗` = Kronecker, **trace = partial trace**; full JSV — the physics functor made literal | ✅ proved |
| **decoherence: the quantum→classical retraction** | `RelExist.Decoherence.{dephase, copyDefect, defectSq, classical_comm}` | dephasing retracts onto the diagonal (classical) fragment; copy-defect is the continuous knob (`0` ⟺ classical), copyable ⟺ commuting, fragment proper (`defectSq_plus_pos`) | ✅ proved |
| **decoherence, abstractly** + dagger | `RelExist.Classical.{DaggerCategory, Decoherence, matDagger, matDecoherence}` | dagger category (`† = transpose`) and the operative decoherence retraction as a definable structure; the matrix model is an instance (abstract decoherence *is* dephasing) | ✅ proved |
| **AI: feedback = the trace** | `RelExist.Recurrence.{feedback, feedback_eq_trace, feedback_iff}` | a recurrent system's behaviour *is* the trace over its hidden wire (GoI execution formula) | ✅ proved |
| **AI: sustained recurrence = `νΦ`** | `RelExist.Recurrence.{sustained, selfConsistent_sustained, feedback_witnessed_by_sustained}` | persistent recurrence is the eigenform; a self-consistent hidden state is sustained | ✅ proved |

The doctrine's ambient structure ([spec 00](../docs/spec/00-doctrine.md)), as a typeclass
mathlib lacks — [`RelExist/Traced.lean`](RelExist/Traced.lean), axiom-free.

| Result | Lean name | Meaning | State |
| --- | --- | --- | --- |
| **traced SMC typeclass** | `RelExist.Traced.TracedSMC` | trace + the **full JSV axiom set** (naturality, sliding, yanking, vanishing-I/II, superposing) via associator/unitor isos | ✅ defined |
| consistency + **validation** | `trivialTracedSMC`, `scalarTracedSMC` | a comm. monoid is a model; **sliding ⟺ commutativity** | ✅ proved |
| **`Rel` — a genuine multi-object model** | `RelExist.RelModel.relTracedSMC` | sets & relations, `⊗ = ×`, relational trace; full JSV validated non-trivially | ✅ proved |
| **literal functors** | `TracedFunctor.{id, toTrivial, comp}` | structure-preserving models; they **compose** | ✅ proved |
| **functor out of a free object** | `TracedFunctor.fromFreeScalar` | `ℕ` is the free comm. monoid (the scalar fragment of the free traced SMC on one object); its **universal property** (`natCMon.lift`, `natCMon.lift_unique`, axiom-free) yields a literal functor fixed by where the generator goes | ✅ proved |
| **functor out of the free object on `k` generators** | `TracedFunctor.fromFreeCMon` | `ℕᵏ` is free on `k` generators (the scalar fragment on `k` colors); full universal property `freeCMon.lift` / `freeCMon.lift_unique` (both **axiom-free**), a model fixed by where the `k` generators go | ✅ proved |
| **the literal matrix instance** | `RelExist.MatrixModel.matTracedSMC` | finite types & matrices, `⊗` = Kronecker, **trace = quantum partial trace**, associators as permutation matrices; the full JSV axiom set — makes the **physics functor literal** | ✅ proved |
| **the free traced SMC `Cl(𝕋)`** | `RelExist.Free.clTracedSMC` | terms over a signature modulo *exactly* the `TracedSMC` equations is itself a traced SMC (`Quot.sound`-only) | ✅ proved |
| **the universal (literal) functor** | `RelExist.Free.functor` / `RelExist.Free.functor_unique` | a model `(ιC, ιG)` of the signature extends to a **unique** traced functor `Cl(𝕋) ⟶ 𝒟` — the genuine universal property | ✅ proved |
| **the coherence refinement** | `RelExist.Traced.CoherentTracedSMC` | `TracedSMC` + the 8 symmetric-monoidal coherence laws (pentagon, triangle, hexagon, naturalities, symmetry) | ✅ defined |
| **coherence validated** | `trivialCoherentTracedSMC`, `scalarCoherentTracedSMC`, `RelExist.RelModel.relCoherentTracedSMC`, `RelExist.MatrixModel.matCoherentTracedSMC` | trivial (axiom-free), scalar (= comm-monoid identities), **`Rel`** and the **literal matrix model** all coherent | ✅ proved |
| **the free *coherent* traced SMC** | `RelExist.Free.clCoherentTracedSMC` / `RelExist.Free.functorC` | `Cl_coh(𝕋) := Quot CohRel` is a coherent traced SMC, with the universal functor into any coherent model (`Quot.sound`-only) | ✅ proved |

Monoidal coherence is also layered on as a refinement (`CoherentTracedSMC`), validated in the
trivial, scalar, **multi-object `Rel`**, and **literal matrix** models, and the **free coherent
traced SMC `Cl_coh(𝕋)` with its universal functor** is built too
([spec 04 §4.6](../docs/spec/04-functorial-semantics.md)). Everything the doctrine references —
and its full coherent refinement — is now mechanized: the typeclass, the coherence refinement,
concrete models (`Rel`, the matrix instance, both coherent), the free scalar objects, and the
**free traced SMC `Cl(𝕋)` (bare and coherent) with universal functors**.

Chemistry is the plan's "best non-quantum fit"; the functor is *definitional* because an
autocatalytic set just **is** an eigenform. The **firewall is now a categorical theorem**
(`Compact.collapse`): compact-closed + cartesian ⇒ thin, so entanglement and free copying
cannot coexist — with `no_cloning` (categorical) and `no_linear_clone` (the concrete
physics fact: cloning is nonlinear) on the quantum side. The **literal matrix traced SMC**
(`matTracedSMC`: trace = partial trace) and — the capstone — the **full free traced SMC
`Cl(𝕋)`** (`clTracedSMC`) with its **universal functor** (`Free.functor` / `functor_unique`,
`Quot.sound`-only) are now both down. See
[spec 04 §4.6](../docs/spec/04-functorial-semantics.md).

### mathlib-backed results (target `Scratch`)

| Result | Lean name | Spec source | State |
| --- | --- | --- | --- |
| `≈ := νΘ` as the greatest bisimulation | `RelExist.We.bisim` | [T2](../docs/spec/03-theorems.md) | ✅ defined (`OrderHom.gfp`) |
| `Θ ≈ = ≈` (fixed point) | `RelExist.We.bisim_unfold` | [T2](../docs/spec/03-theorems.md) | ✅ proved |
| **coinduction** — every bisimulation `≤ ≈` | `RelExist.We.bisim_coind` / `bisim_of_bisimulation` | [T2](../docs/spec/03-theorems.md) | ✅ proved |
| `≈` is an equivalence (refl/symm/trans) | `RelExist.We.bisim_{refl,symm,trans}` | [T2](../docs/spec/03-theorems.md) | ✅ proved |
| **shared world** `𝔼 := D/≈` | `RelExist.We.World` | [T2](../docs/spec/03-theorems.md) | ✅ defined (quotient) |
| co-directed attention operator (induced by coupling) | `RelExist.Attention.couplingOp` | [§1.3](../docs/spec/01-signature.md) | ✅ defined |
| "receiving raises giving" (monotone) | `RelExist.Attention.couplingOp_mono` | [§1.3.2](../docs/spec/01-signature.md) | ✅ proved |
| **self = eigenform** `νΦ` (fixed point, maximal) | `RelExist.Attention.sustainedField{,_fixed,_greatest}` | [§1.3.3](../docs/spec/01-signature.md), [A3](../docs/spec/02-axioms.md) | ✅ proved |
| generativity — relating **accumulates** attention | `RelExist.Attention.orbit_{ascending,le_gfp}` | [§1.3.3](../docs/spec/01-signature.md) | ✅ proved |
| **registration** — a closed loop absorbs the knower into the known | `RelExist.Attention.{relating_absorbs, closed_loop_registers}` | [03-theorems.md](../docs/spec/03-theorems.md) | ✅ proved |
| **self-in-other, quantified** — bounded iff `‖x‖<1` | `RelExist.Distribution.{distributed, distributed_bound, distributed_zero}` | [03 §3.4](../docs/spec/03.1-sparsity.md), [03-theorems.md](../docs/spec/03-theorems.md) | ✅ proved |
| **quantitative eigenform** — `total x = 1 + x·total x` | `RelExist.Distribution.{total, total_feedback, total_bound}` | [03-theorems.md](../docs/spec/03-theorems.md) | ✅ proved |
| **quantitative coinduction** — sustained self is *unique* (any seed) | `RelExist.Distribution.{sustained, sustained_fixed, sustained_unique, sustained_bound}` | [03-theorems.md](../docs/spec/03-theorems.md) | ✅ proved |
| **unification** — both selves realize the ν-modality | `RelExist.Feedback.{CoDirectedSelf, self_iterate, latticeSelf, banachSelf}` | [03-theorems.md](../docs/spec/03-theorems.md) | ✅ proved |
| Lemma 3.1 over `ℝ` (`\|Stab\| ≤ β/m`) | `RelExist.Real.stab_card_le_div` | [03 Lemma 3.1](../docs/spec/03.1-sparsity.md) | ✅ proved |
| **density → 0** (`\|Stab N\|/N → 0`) | `RelExist.Real.stab_density_tendsto_zero` | [03 §3.1, Lemma 3.1](../docs/spec/03.1-sparsity.md) | ✅ proved (`Filter.Tendsto`) |

`Scratch.We` formalizes **theorem T2**: the lived identity (greatest bisimulation) as `νΘ = OrderHom.gfp Θ`,
with coinduction, the proof that `≈` is an equivalence, and the shared world `𝔼 := D/≈`.
`Scratch.Attention` recasts **attention as a consequence of structure** (§1.3): a
co-directed, asymmetric operator `Φ_c` induced by the coupling, with the self an
*eigenform* `νΦ_c`, finiteness *constitutive* (the bounded capacity `α`, no budget), and
"receiving raises giving" as monotone accumulation — the budget model of
`RelExist/Loop.lean` becomes its uniform-depleting special case. `Scratch.SparsityReal`
lifts the sparsity dichotomy to `ℝ` with the genuine **density-→-0** limit. See
*One-command setup* below.

This lattice-theoretic `νΘ` reading of T2 now has a second, independent mechanization:
the [`agda/`](../agda/) layer (Layer 5) rebuilds `≈`, its coinduction principle, and the
shared world with **native coinduction** (final coalgebra, copatterns) rather than
`OrderHom.gfp` — the two developments agree on the doctrine's lived identity (and on observational equality `≅`).

## Build

```sh
cd formal
lake build            # the dependency-free core (RelExist) — fast, no mathlib
lake build Scratch    # the mathlib-backed target — compiles mathlib on first run
```

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.15.0`). Audit the proofs' axiom footprint with:

```sh
lake env lean -e '#print axioms RelExist.stab_card_bound'
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

## Roadmap

The discrete core is step 1 of [the spec's proof strategy](../docs/spec/03.1-sparsity.md#35-proof-strategy-for-mechanization).
Next, in rough order:

1. **mathlib upgrade.** Re-cast costs in `ℝ_{≥0}`, prove the density-→-0 statement
   (`Filter.Tendsto`) and the "nowhere dense" form (topology). mathlib is now
   installed (target `Scratch`), so this proceeds there — no cache required, just the
   one-time source compile the bootstrap already does. (The density-→-0 statement is
   done in `Scratch.SparsityReal`; the **nowhere-dense / topological** form is now
   mechanized on the Agda side — [`agda/RelExist/Sparsity.agda`](../agda/RelExist/Sparsity.agda),
   `selves-nowhereDense` — over the final coalgebra, where it is most natural.)
2. **Sharing.** Replace the `List` of costs by a graded poset with sub-additive cost
   (lax `c`), re-deriving the bound up to the sharing defect ([03 §3.3](../docs/spec/03.1-sparsity.md)).
3. **Threshold ⇔ fixed point.** The categorical crux: in the traced fragment,
   `loop_R(e) = e ⟺ N(e) ≥ d(e)` ([01 §1.3.3](../docs/spec/01-signature.md)).
4. **Doctrine + Layer 4.** Symmetric monoidal / cartesian fragment structures and
   the functorial-semantics firewall.
