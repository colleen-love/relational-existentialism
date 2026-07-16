# WS5 Triage and Design (rev. 3)

> **Revision note (rev. 3, post-charter-audit).** This revision addresses the charter-binding defects found in audit of rev. 2, and closes both *provable* halves of the workstream to full discharge while keeping the one genuinely open half honestly open. Changes:
> 1. **C2 incompleteness reproved to be genuinely `(F,κ)`-robust** (charter §8.1's load-bearing claim). Rev. 2's proof routed through `mk_carrier_ge : κ ≤ mk (νPk κ).X`, a functor-dependent fact — which *contradicted* the robustness the charter rests on. Rev. 3 states incompleteness as the support's non-surjection onto **its own** description space and proves it by a pure Lawvere/Cantor diagonal that consumes **no** carrier-cardinality fact and **no** functor-specific branching. C2 is now Impossibility-proved and functor-agnostic, as §8.1 asserts.
> 2. **The discrete-step substitution for §3.6's ODE is now declared openly** (§2.1a), per §8.2 discipline, rather than left as a silent modeling convenience.
> 3. **Convergence stays Partial-conditional** — this is forced by the charter, not a shortfall. The charter names non-convergence a live standing risk; no upstream artifact supplies a contraction, and convergence is not impossible, so it can be neither Discharged nor Impossibility-proved. It is routed as the WS5 residual with its obstruction typed.
> 4. Carried forward from rev. 2 and retained: `IsReplicatorMutator` defined so the open obligation elaborates; `ws5_attention_converges`/`converges_if` signatures reconciled; `ws5_no_delta` sourced from `ws2_nondegenerate`, not the downstream WS7; `Attn.supp_lt` derived from `HasSum`, not asserted.
>
> **Terminal status of the workstream: Partial (split), as the charter §8.1 pre-registers.** Both provable obligations — incompleteness and the plurality floor — are **fully Discharged** (incompleteness as an Impossibility-proved). The convergence obligation is **Partial-conditional** with a precise typed obstruction. There is no honest reading of criterion (v) on which WS5 is *fully* Discharged or *fully* Impossibility-proved, because (v)'s dynamics half is exactly the charter's open "attention need not converge" risk. Naming the bundle `ws5_resolved` would be the §2.4(d) laundering failure and is refused.

## Part 1 — Paper-decidable triage

Each candidate is scored on criteria adjudicated without running Lean, using only the charter's outcome vocabulary and the established upstream artifacts (ws1–ws4). The decisive axis is which obligations are *actually dischargeable now* versus *irreducibly conditional*, and whether the candidate honors the split-status requirement that is WS5's characteristic hazard.

**Triage predicates (each Yes/No/Partial, decidable by inspection):**

- **T1 — Dischargeable on paper?** Completable with existing Mathlib + upstream lemmas, no unproved analytic input?
- **T2 — `(F,κ)`-robust?** Independent of the observation-functor/bound choice (survives WS4's `W_Q` enrichment and WS7's collector)?
- **T3 — On-target?** Binds to the actual carrier `νP_κ`, not a disconnected abstract type?
- **T4 — Upstream-grounded?** Consumes a load-bearing upstream fact, rather than floating free?
- **T5 — Honest status?** Stated form prevents a conditional claim from reading as discharged?
- **T6 — Cost/risk in Lean.** Low / Medium / High.
- **Outcome class** (per §5): Discharged / Impossibility-proved / Partial-conditional / Assembly.

| | T1 dischargeable | T2 (F,κ)-robust | T3 on-target | T4 grounded | T5 honest-status | T6 cost | Class |
|---|---|---|---|---|---|---|---|
| **C1** abstract Lawvere | Yes | Yes | **No** | No | n/a | Low | Impossibility (off-target) |
| **C2** self-description incompleteness | Yes | **Yes (rev. 3: pure diagonal, no carrier-card. fact)** | **Yes** | **Yes** (`<κ` support bound only) | Yes | Low | **Impossibility-proved** |
| **C3** plurality floor (discrete) | Yes | Yes | Yes | Partial (support + ws2 branching) | Yes | Low–Med | **Discharged** |
| **C4** Banach convergence | **No** (needs contraction) | Yes | Partial | No | **only if quarantined** | Low | Partial-conditional |
| **C5** Lyapunov/KL descent | **No** | Yes | Partial | No | only if quarantined | **High** | Partial-conditional |
| **C6** split assembly | Yes (assembly) | mixed | Yes | Yes | **Yes (structural)** | Low | Assembly |

**Reading the table.** C1 fails T3 — it proves impossibility about an abstract `A → B`, not the groundless object; lemma-only. C4/C5 fail T1: the contraction/descent input is exactly the standing risk "attention need not converge," and no upstream artifact supplies it. C5 is dominated by C4 (High cost, no compensating certainty); dropped. C2 and C3 pass everything paper-decidable at Low cost — the discharge core. C6 passes T5 *structurally*.

> **Rev. 3 correction to C2's T2 and T4 cells (the charter-binding fix).** Rev. 2 marked C2 `(F,κ)`-robust while proving it through `κ ≤ mk (νPk κ).X` — a fact about the *specific* functor's branching, which would need re-proof for WS4's `W_Q` and thus was **not** robust. That silently contradicted charter §8.1, whose entire "cleanest candidate for outright success" verdict rests on incompleteness being functor-agnostic. Rev. 3 removes the dependency entirely: C2 is now the support's non-surjection onto **its own** description space `support → Prop`, proved by the raw diagonal, consuming only the `<κ` support bound (which every bounded `F` supplies by construction). No carrier cardinality, no branching count, no `mk_carrier_ge`. C2 is therefore genuinely `(F,κ)`-robust — and cheaper. See §2.3.

**Collapsed decision.** A *composite dictated by the triage*: **C2 + C3 as the proved core, C4 as an explicitly quarantined conditional, all assembled under C6**, with C1 demoted to an internal lemma. Forced, not chosen.

**Selected object for full design: the C6 assembly `WS5FiniteAttention`**, fields C2 (incompleteness), C3 (plurality floor), C4 (conditional convergence + named open obstruction).

---

## Part 2 — Full mathematical design

### 2.0 Ambient theory and imports

Carrier: `U := νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra, `F = P_κ`, AFA modeled coalgebraically. No monad `T` or law `λ` is needed — attention is a *second* structure over the carrier, not a bialgebra. Axiom budget `[propext, Classical.choice, Quot.sound]`; the incompleteness core is `Classical`-only via `Not`.

Imported, cited as established and axiom-free:

- from **ws1**: `PkObj`, `PkMap`, `PkMap_id/_comp`, `mk_singleton_lt`, `mk_empty_lt`, `Coalg`, `IsTerminalCoalg`, `exists_terminal_coalg`. **The `<κ` support bound `(mk ↥((νPk κ).str u).1 < κ)` is the definitional content of `PkObj` and is the single load-bearing upstream fact for C2** — and, crucially (rev. 3), the *only* one.
- from **ws2**: `νPk`, `νPk_terminal`, `ws2_bisim_eq`, `ws2_nondegenerate`, `ws2_bisim_behavioural`. **Rev. 3 scope change:** `ws2_nondegenerate` is load-bearing for **C3's** `ws5_no_delta` (≥2 branching) **only**. It is *no longer* used by C2 — this is what makes C2 functor-robust.
- from **ws3**: nothing required for C2/C3/C4.
- from **Mathlib**: `Function.cantor_surjective`, `Cardinal.mk_le_mk_of_subset`, `ContractingWith.exists_fixedPoint` (Banach), `Finset`/`tsum`/`HasSum` for the simplex. (Note rev. 3 **drops** `Cardinal.cantor` and `Cardinal.mk_le_of_surjective` from C2's dependency set — the diagonal route needs neither.)

### 2.1 Proof architecture (dependency graph)

```
   Function.cantor_surjective (Mathlib)      <κ support bound (ws1 PkObj)
                   │                                    │
                   └──────────────┬─────────────────────┘
                                  ▼
              ws5_carrier_incomplete   ← C2, IMPOSSIBILITY-PROVED, (F,κ)-ROBUST
                                  │      (self-description space; no carrier card.)
                                  │
   μ>0 floor        ws2_nondegen  │            Banach (Mathlib ContractingWith)
        │            (≥2 branch)  │                        │
        ▼                 │       │                        ▼
  ws5_plurality_floor ────┘       │            ws5_attention_converges  ← C4
   DISCHARGED  ── ws5_no_delta     │            PARTIAL-CONDITIONAL (hcontr)
        │                         │                        │
        │                         │            IsReplicatorMutator (defined §2.2)
        │                         │                        │
        │                         │            replicator_mutator_contracts
        │                         │              := TYPED OPEN OBLIGATION (empty)
        └──────────┬──────────────┴────────────────────────┘
                   ▼
         WS5FiniteAttention   ← C6 assembly, named ws5_incompleteness_and_floor
                              (NOT ws5_resolved — convergence field carries its
                               hypothesis; contraction_open has no inhabitant)
```

Three independent spines converge on one bundle. Left and center are complete on paper; the right spine terminates in a deliberately uninhabited obligation. **Rev. 3: the C2 spine no longer touches the ws2 branching input** — its only upstream edge is the `<κ` support bound.

### 2.1a [REV — §8.2 discipline] Declared substitution: discrete floored step for §3.6's ODE

Charter §3.6 frames feed/starve as the continuous replicator-with-mutation `ẋᵢ = xᵢ(fᵢ − f̄) + μ(uᵢ − xᵢ)`. **This design does not formalize that ODE.** It represents the dynamics by a discrete `step : Attn κ u → Attn κ u` carrying a mutation-floor hypothesis `μ * unif r ≤ (step a).w r`. This is a declared substitution, surfaced openly per §8.2, not a silent convenience:

- *What is recovered in the surrogate:* the anti-collapse content criterion (v)/§3.8 actually needs — a plurality floor keeping every reachable weight off the simplex vertices — is fully expressible and provable on the discrete step (C3). The floor `μ` plays exactly the role of §3.6's mutation term `μ(uᵢ − xᵢ)`.
- *What is not recovered, and where it lands:* the continuous-time trajectory, its `deriv`, and Lyapunov/KL descent are **not** modeled (this is the C5 drop; Mathlib continuous-ODE support is thin and buys no certainty the discrete floor lacks). The convergence *of* the dynamics to a fixed point is the C4 obligation, and it is conditional regardless of discrete/continuous framing.
- *Residual routing:* whether the discrete floored step is a faithful surrogate for the ODE's long-run behaviour is a WS7 dynamical-non-collapse question, already inside WS7's `(F, κ, μ, #Q)` collector duty. WS5 does not claim the ODE realization; it claims the floor.

This note exists so no importer reads C3 as a theorem about the §3.6 differential equation. It is a theorem about its discrete floored surrogate, and that surrogate is what (v)'s non-collapse content requires.

### 2.2 Definitions needed

**Self-description space and incompleteness (C2) — rev. 3, functor-robust form.** The description space is over the **support itself**, not the carrier `X`. For a state `u`, write `S u := ↥((νPk κ).str u).1` for its attention support (the `<κ`-sized set of attended relations). A *self-description* is a predicate on that support, i.e. an element of `S u → Prop`. Incompleteness is the non-existence of a point-surjection `S u → (S u → Prop)`. This is a pure Lawvere/Cantor diagonal on `S u`; it references neither `(νPk κ).X` nor any branching count, so it holds for **every** observation functor whose supports are sets — the robustness charter §8.1 requires.

```lean
/-- The attention support of u: the <κ-sized set of relations u attends to. -/
abbrev SelfSupport (κ) (u : (νPk κ).X) : Type u := ↥((νPk κ).str u).1
```

**Attention state (C3).**

```lean
structure Attn (κ : Cardinal.{u}) (u : (νPk κ).X) where
  w        : SelfSupport κ u → ℝ
  nonneg   : ∀ r, 0 ≤ w r
  total    : HasSum w 1                              -- simplex constraint
  -- supp_lt is NOT a field: for infinite κ it follows from `total` (a summable
  -- family has countable support), re-derived as Attn.supp_lt below.
```

```lean
/-- Support smallness is a consequence of summability, not an axiom, and not
    (contra rev. 1) an inheritance from PkObj. -/
lemma Attn.supp_lt (hinf : ℵ₀ ≤ κ) (a : Attn κ u) :
    Cardinal.mk (↥{r | a.w r ≠ 0}) ≤ Cardinal.aleph0
```

One feed/starve step is `step : Attn κ u → Attn κ u` constrained by the **mutation-floor hypothesis** `hfloor : ∀ a r, μ * unif r ≤ (step a).w r`, `unif` the uniform reference weight. Per §2.1a this is the declared discrete surrogate for §3.6.

**Metric realization and the replicator predicate (C4).** An abstract `[MetricSpace M] [CompleteSpace M]` standing for the America–Rutten realization of `νP_κ`; the design takes completeness as given and proves only the Banach step. The operator class named in the open obligation is defined, so the obligation elaborates as a real uninhabited `Prop`:

```lean
/-- Abstract characterization of a replicator-with-mutation update on a metric
    realization of the attention simplex: continuous, simplex-preserving, μ-floored.
    Its DEFINITION is here; its inhabitation BY A CONTRACTION is the open obligation. -/
structure IsReplicatorMutator {M : Type u} [MetricSpace M]
    (Tatt : M → M) (μ : ℝ) : Prop where
  cont      : Continuous Tatt
  floored   : 0 < μ
  -- (simplex-preservation fields elided; opaque for the obligation)
```

### 2.3 Lemmas and theorems

**C2 — self-description incompleteness (Impossibility-proved, `(F,κ)`-robust).**

```lean
theorem ws5_carrier_incomplete (u : (νPk κ).X) :
    ¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e
```

Proof (pure diagonal, one line of mathematical content): `Function.cantor_surjective` with `B := Prop` and `neg := Not`; `Classical` gives `Not p ≠ p`, so no `e` is surjective. **This consumes no cardinality fact at all** — not the `<κ` bound, not any lower bound on `mk X`. It is the Lawvere fixed-point impossibility in its sharpest form, on the object §3.6 actually names ("a point-surjection from an object onto its own space of self-descriptions").

*Why this is the right target, and robust.* Charter §3.6/§8.1 define incompleteness as the impossibility of an object surjecting onto **its own** self-descriptions — not onto the whole carrier's power-object. Rev. 2 over-reached by aiming at `X → Prop`, which dragged in a functor-dependent carrier-cardinality premise and broke robustness. Rev. 3's target is both *closer to the charter's wording* and *functor-agnostic*: it survives WS4's `W_Q` and any WS7 `(F,κ)` unchanged, because it never mentions `F` beyond "supports are sets."

*Role of the `<κ` bound (T4 grounding, now a corollary not a premise).* The support being `<κ`-sized is not needed for the impossibility, but it is what makes incompleteness *substantive* rather than vacuous: attention is genuinely bounded, so the self-description space strictly out-sizes any enumeration the finite attention could carry. Recorded as:

```lean
/-- The gap is non-vacuous: bounded attention cannot even enumerate its own
    self-descriptions, since |S u → Prop| = 2^|S u| > |S u|. Consumes the <κ bound
    only to certify non-vacuity, NOT to prove the impossibility. -/
lemma ws5_incomplete_nonvacuous (u : (νPk κ).X) :
    Cardinal.mk (SelfSupport κ u) < Cardinal.mk (SelfSupport κ u → Prop)
```

*Non-triviality guard (remark, not theorem):* the analogous statement with description space `= (νPk κ).str u` (the relations *themselves*, not predicates over them) is **false** — a state enumerates its own immediate relations. Incompleteness bites at the predicate/power level, where self-description out-sizes the support. Recorded so the theorem is not read as forbidding self-reference per se.

**C3 — plurality floor (Discharged).**

```lean
theorem ws5_plurality_floor {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ)
    (unif : SelfSupport κ u → ℝ) (hunif : ∀ r, 0 < unif r)
    (step : Attn κ u → Attn κ u)
    (hfloor : ∀ (a : Attn κ u) r, μ * unif r ≤ (step a).w r)
    (a : Attn κ u) (r : SelfSupport κ u) : 0 < (step a).w r
```

Proof: `0 < μ * unif r ≤ (step a).w r` by `mul_pos hμ (hunif r)` then `hfloor`. Pure order algebra, no analysis.

**Corollary `ws5_no_delta` (Discharged; sourced from ws2, not WS7).**

```lean
theorem ws5_no_delta {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ) (unif …) (hunif …)
    (step …) (hfloor …)
    (hbranch : 2 ≤ Cardinal.mk (SelfSupport κ u))    -- from ws2_nondegenerate
    (a : Attn κ u) :
    ¬ ∃ r₀, ∀ r, (step a).w r = if r = r₀ then 1 else 0
```

Full support `∀ r, 0 < (step a).w r` comes from `ws5_plurality_floor`; the ≥2-branching `hbranch` is discharged from `ws2_nondegenerate`, **not** the downstream WS7 (rev. 1's forward/circular dependency). `μ = 0` makes the floor `0` and is exactly where collapse re-enters; `hμ` is load-bearing and stated.

**C4 — conditional convergence (Partial-conditional). Canonical signature reused verbatim by C6.**

```lean
theorem ws5_attention_converges
    {M : Type u} [MetricSpace M] [CompleteSpace M]
    (Tatt : M → M) (K : ℝ≥0) (hK : K < 1)
    (hcontr : ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) :
    ∃! p, Tatt p = p
```

Proof: package `hK`, `hcontr` into `ContractingWith Tatt`; apply `ContractingWith.exists_fixedPoint`. Trivial *given* `hcontr`. The scientific content is quarantined:

```lean
/-- The replicator-with-mutation operator is a contraction on the metric
    realization. NOT PROVED — the WS5 open obstruction (charter standing risk
    "attention need not converge"). Registered as a typed hole; no inhabitant. -/
def replicator_mutator_contracts (μ : ℝ) : Prop :=
  ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] (Tatt : M → M),
    IsReplicatorMutator Tatt μ →
      ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y
```

`ws5_attention_converges` never instantiates this; `hcontr` stays exposed at every call site. There is deliberately **no** `theorem … : replicator_mutator_contracts μ` — the symbol exists, the inhabitant does not. This is the charter's "state the contraction/μ conditions explicitly as hypotheses," executed at the type level.

**C6 — the honest assembly.**

```lean
def PluralityFloor (μ : ℝ) (u : (νPk κ).X) : Prop :=
  0 < μ → ∀ (unif : SelfSupport κ u → ℝ), (∀ r, 0 < unif r) →
    ∀ (step : Attn κ u → Attn κ u),
      (∀ a r, μ * unif r ≤ (step a).w r) → ∀ a r, 0 < (step a).w r

structure WS5FiniteAttention (κ : Cardinal.{u}) where
  incomplete   : ∀ u : (νPk κ).X,
                   ¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop),
                       Function.Surjective e
  no_delta     : ∀ {u} (μ : ℝ), PluralityFloor μ u
  -- field type is character-for-character ws5_attention_converges' conclusion
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M]
                   (Tatt : M → M) (K : ℝ≥0), K < 1 →
                   (∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) →
                   ∃! p, Tatt p = p

theorem ws5_incompleteness_and_floor :
    Nonempty (WS5FiniteAttention κ) :=
  ⟨{ incomplete   := fun u => ws5_carrier_incomplete u,
     no_delta     := fun μ => by
                       intro hμ unif hunif step hfloor a r
                       exact ws5_plurality_floor μ hμ unif hunif step hfloor a r,
     converges_if := fun Tatt K hK hc => ws5_attention_converges Tatt K hK hc }⟩
```

Deliberately named `ws5_incompleteness_and_floor`, **not** `ws5_resolved`: convergence lives only as the *conditional* field `converges_if`, and `replicator_mutator_contracts` sits outside the structure with no inhabitant. This is the WS4 discipline (`ws4_graded_coherence_Luk`, not `ws4_resolved`) transplanted — structurally preventing the (now `(F,κ)`-robust) incompleteness theorem from laundering the open convergence.

**Rev. 3 note on `hinf`/`IsRegular`.** C2 no longer needs `ℵ₀ ≤ κ` at all (the diagonal is cardinality-free), so `WS5FiniteAttention` drops the `hinf` field. `hinf` survives only inside `Attn.supp_lt` and `ws5_incomplete_nonvacuous`, where it is genuinely used. `κ.IsRegular` remains non-load-bearing for every WS5 result; if threaded at a call site for charter fidelity it is marked `_hreg`, mirroring the WS2 honesty note and satisfying §6.1's retro-validation obligation trivially (nothing to retro-validate).

### 2.4 Status, hypotheses, and failure conditions

**Outcome class: Partial (split), matching charter §8.1.**
- Incompleteness is **Impossibility-proved** — a sharp negative the program wants; `(F,κ)`-robust (rev. 3 fix), axiom-free (`Classical` only), on the object §3.6 names. Fully discharged; nothing conditional remains.
- Plurality floor is **Discharged**, conditional on the stated load-bearing `μ > 0`; `ws5_no_delta` excludes dynamical collapse, sourced from ws2.
- Convergence is **Partial-conditional**: the Banach step is proved, the contraction premise is a typed open obligation routed as the WS5 residual. **This cannot be upgraded to Discharged or to Impossibility-proved without misreporting the charter** — see below.

**Why the workstream is not, and cannot honestly be, "fully" Discharged or Impossibility-proved.** Criterion (v) conjoins incompleteness *and* well-behaved dynamics. The dynamics half reduces to whether the replicator-mutator contracts, which charter §8 lists as a live standing risk ("attention need not converge… a phenomenon to characterize, not assume away"). No upstream artifact supplies a contraction proof, so it cannot be Discharged; and convergence is not false (contractive regimes plainly exist), so it cannot be Impossibility-proved. The only faithful terminal status is Partial-conditional. Forcing either total label would be exactly the §2.4(d)/§8.2 laundering the design is built to prevent. WS5 therefore closes *both provable halves fully* and names the third precisely — the honest maximum.

**Hypothesis accounting (rev. 3, corrected).**
- **C2 consumes nothing but `Classical`** for the impossibility; the `<κ` support bound is consumed only by `ws5_incomplete_nonvacuous` to certify non-vacuity. No `hinf`, no `mk_carrier_ge`, no branching. This is what secures `(F,κ)`-robustness.
- `hinf : ℵ₀ ≤ κ` is consumed by `Attn.supp_lt` and `ws5_incomplete_nonvacuous` only.
- `hbranch : 2 ≤ mk (SelfSupport κ u)` is load-bearing for `ws5_no_delta`, discharged from `ws2_nondegenerate`.
- `μ > 0` is load-bearing for C3.
- `κ.IsRegular` is not load-bearing for any WS5 result.
- The contraction premise / `replicator_mutator_contracts` is load-bearing for C4 and is exactly what is **not** discharged.

**What counts as failure.**
(a) *False incompleteness* — collapsing the description space to `(νPk κ).str u`, trivializing C2 into a false statement; guarded by the §2.3 non-triviality remark.
(b) *Non-robust incompleteness (rev. 3's fixed defect)* — proving C2 via a functor-dependent carrier-cardinality premise, silently breaking the §8.1 robustness claim. Fixed: C2's proof is cardinality-free and mentions no functor.
(c) *Dynamical collapse* — a reachable state is a Dirac delta; excluded by C3/`ws5_no_delta` when `μ > 0` and branching ≥ 2, re-entering at `μ = 0`.
(d) *Non-convergence* — the replicator-mutator is expansive/chaotic for the relevant `μ`, so `replicator_mutator_contracts` is false; a *legitimate open outcome*, not a defect. The fatal error would be reporting C4 as Discharged.
(e) *Laundering* — naming the bundle `ws5_resolved`, or relabeling the split status as full discharge/impossibility; structurally prevented and explicitly refused in §2.4.
(f) *Undeclared ODE substitution* — presenting C3 as a theorem about §3.6's differential equation; guarded by the §2.1a declared-substitution note.

**Charter-binding summary.** WS5 binds to Commitment 5 and criterion (v). Its incompleteness signature discharges (v)'s "no object fully knows itself" as an `(F,κ)`-robust Impossibility; its plurality floor discharges (v)'s non-collapse contribution and criterion (vii)'s dynamical-singularity exclusion (for `μ>0`); its convergence signature honestly leaves (v)'s "well-behaved feed/starve dynamics" Partial with a typed obstruction routed to the WS7 collector. No signature discharges or invalidates more than it proves, and the bundle's name prevents drift.
