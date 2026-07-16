# WS5 Triage and Design

## Part 1 — Paper-decidable triage

Each candidate is scored on criteria that can be adjudicated without running Lean, using only the charter's outcome vocabulary and the established upstream artifacts (ws1–ws4). The decisive axis is not "which framing is nicest" but which obligations are *actually dischargeable now* versus *irreducibly conditional*, and whether the candidate honors the split-status requirement that is WS5's characteristic hazard.

**Triage predicates (each Yes/No/Partial, decidable by inspection):**

- **T1 — Dischargeable on paper?** Can the proof be completed with existing Mathlib + upstream lemmas, no unproved analytic input?
- **T2 — `(F,κ)`-robust?** Is the result independent of the observation-functor/bound choice (so it survives WS4's enrichment and WS7's collector)?
- **T3 — On-target?** Does it bind to the actual carrier `νP_κ`, not a disconnected abstract type?
- **T4 — Upstream-grounded?** Does it consume a load-bearing upstream fact (the `< κ` support bound, terminality, Lambek), rather than floating free?
- **T5 — Honest status?** Does its stated form prevent a conditional claim from reading as discharged?
- **T6 — Cost/risk in Lean.** Low / Medium / High (real-analysis and ODE content drives this up).
- **Outcome class** (per §5 vocabulary): Discharged / Impossibility-proved / Partial-conditional / Assembly.

| | T1 dischargeable | T2 (F,κ)-robust | T3 on-target | T4 grounded | T5 honest-status | T6 cost | Class |
|---|---|---|---|---|---|---|---|
| **C1** abstract Lawvere | Yes | Yes | **No** | No | n/a | Low | Impossibility (off-target) |
| **C2** carrier incompleteness | Yes | Yes | **Yes** | **Yes** (`<κ` bound) | Yes | Low | **Discharged** |
| **C3** plurality floor (discrete) | Yes | Yes | Yes | Partial (support only) | Yes | Low–Med | **Discharged** |
| **C4** Banach convergence | **No** (needs contraction lemma) | Yes | Partial | No | **only if quarantined** | Low | Partial-conditional |
| **C5** Lyapunov/KL descent | **No** | Yes | Partial | No | only if quarantined | **High** | Partial-conditional |
| **C6** split assembly | Yes (assembly) | mixed | Yes | Yes | **Yes (structural)** | Low | Assembly |

**Reading the table.** C1 fails T3 decisively — it proves a true impossibility about an abstract `A → B`, not about the groundless object, so it can only serve as a lemma, never a deliverable. C4 and C5 fail T1: convergence is not dischargeable on paper because the contractivity/Lyapunov-descent input is exactly the standing risk "attention need not converge," and no upstream artifact supplies it. C5 additionally carries High Lean cost (continuous-time `deriv`, thin Mathlib support) with no compensating certainty — dominated by C4 on every axis, so it is dropped. C2 and C3 pass everything paper-decidable and are Low cost; they are the discharge core. C6 is the only candidate that passes T5 *structurally* rather than by discipline-of-the-author.

**Collapsed decision.** The framing is not a single candidate but a *composite dictated by the triage*: **C2 + C3 as the proved core, C4 as an explicitly quarantined conditional, all assembled under C6**, with C1 demoted to an internal lemma. This is forced, not chosen — C2/C3 are the only Discharged-class results available, C4 is the only convergence content that is honest without being false, and C6 is the only shape that stops C2 from laundering C4. Selecting C2 alone would under-deliver (no anti-collapse); selecting C4 alone would misreport an open problem as settled.

**Selected object for full design: the C6 assembly `WS5FiniteAttention`**, whose fields are C2 (incompleteness), C3 (plurality floor), and C4 (conditional convergence + named open obstruction).

---

## Part 2 — Full mathematical design

### 2.0 Ambient theory and imports

Carrier: `U := νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra, `F = P_κ`, AFA modeled coalgebraically. No monad `T` or distributive law `λ` is needed — attention is a *second* structure over the carrier, not a bialgebra. Axiom budget `[propext, Classical.choice, Quot.sound]`; the incompleteness core is even `Classical`-only via `Not`.

Imported, cited as established and axiom-free:

- from **ws1**: `PkObj`, `PkMap`, `PkMap_id/_comp`, `mk_singleton_lt`, `mk_empty_lt`, `Coalg`, `IsTerminalCoalg`, `exists_terminal_coalg`.
- from **ws2**: `νPk`, `νPk_terminal`, `ws2_bisim_eq`, `ws2_nondegenerate`, `ws2_bisim_behavioural`. The support bound `(mk ↥((νPk κ).str u).1 < κ)` is the definitional content of `PkObj` and is the single load-bearing upstream fact for C2.
- from **ws3**: nothing required for C2/C3/C4; `alg`/`pkJoin` imported only if a later revision couples attention to composition (not in this design).
- from **Mathlib**: `Cardinal.cantor`, `Cardinal.mk_le_mk_of_subset`, `Function.cantor_surjective`, `ContractingWith.exists_fixedPoint` (Banach), `Finset`/`tsum` for the simplex.

### 2.1 Proof architecture (dependency graph)

```
        Cantor / diagonal (Mathlib)          <κ support bound (ws1 PkObj)
                   │                                    │
                   └──────────────┬─────────────────────┘
                                  ▼
                        ws5_carrier_incomplete   ← C2, DISCHARGED, (F,κ)-robust
                                  │
   μ>0 floor algebra             │            Banach (Mathlib ContractingWith)
        │                        │                        │
        ▼                        │                        ▼
  ws5_plurality_floor  ← C3      │            ws5_attention_converges  ← C4
   DISCHARGED                    │            CONDITIONAL (contraction premise)
        │                        │                        │
        │                        │                replicator_mutator_contracts
        │                        │                   := TYPED OPEN OBLIGATION
        │                        │                        │
        └──────────┬─────────────┴────────────────────────┘
                   ▼
         WS5FiniteAttention   ← C6 assembly, named ws5_incompleteness_and_floor
                              (NOT ws5_resolved — convergence field carries its
                               hypothesis; contraction_open has no inhabitant)
```

Three independent proof spines converge on one bundle. The left and center spines are complete on paper; the right spine terminates in a deliberately uninhabited obligation.

### 2.2 Definitions needed

**Self-description space and incompleteness (C2).** No new structure; the description space is `(νPk κ).X → Prop` and the attention support of `u` is the subtype `↥((νPk κ).str u).1`. The theorem is a non-surjection between them.

**Attention state (C3).** A finite-support simplex weighting over a state's relations:

```lean
structure Attn (κ : Cardinal.{u}) (u : (νPk κ).X) where
  w        : ↥((νPk κ).str u).1 → ℝ
  nonneg   : ∀ r, 0 ≤ w r
  supp_lt  : Cardinal.mk (↥{r | w r ≠ 0}) < κ      -- finite-support, inherits from PkObj
  total    : HasSum w 1                              -- simplex constraint
```

One feed/starve step is an abstract `step : Attn κ u → Attn κ u` constrained only by a **mutation-floor hypothesis** `hfloor : ∀ a r, μ * unif r ≤ (step a).w r`, where `unif` is the uniform reference weight. The dynamics itself is not formalized as an ODE; the discrete step + floor is what the anti-collapse claim needs.

**Metric realization (C4).** Kept abstract: an arbitrary `[MetricSpace M] [CompleteSpace M]` standing for the America–Rutten realization of `νP_κ`. The design does *not* construct this realization (that is a WS2/WS7-adjacent metric-coalgebra task); it takes completeness as given and proves only the Banach step.

### 2.3 Lemmas and theorems

**C2 — carrier incompleteness (Discharged).**

```lean
theorem ws5_carrier_incomplete (hinf : ℵ₀ ≤ κ) (u : (νPk κ).X) :
    ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop), Function.Surjective e
```

Proof route (primary, cardinality): the support is `< κ`; `(νPk κ).X → Prop` has cardinality `2^(mk (νPk κ).X) ≥ 2^κ > κ`; a `< κ`-sized type cannot surject onto a strictly larger one (`Cardinal.cantor` composed with `Cardinal.mk_le_of_surjective`). This *consumes the `< κ` bound* — the T4 grounding — so incompleteness is a consequence of *bounded* attention, not a generic diagonal. Backup route: `Function.cantor_surjective` with `B := Prop`, `neg := Not`, `Classical` for `Not p ≠ p`; kept as `ws5_incomplete_diagonal` in case the carrier-cardinality lower bound `κ ≤ mk (νPk κ).X` proves annoying (it follows from non-degeneracy + the branching, and is worth a helper lemma `mk_carrier_ge : κ ≤ Cardinal.mk (νPk κ).X` if needed).

*Non-triviality guard (must appear as a remark, not a theorem):* the same statement with description space `= (νPk κ).str u` is **false** — a state enumerates its own immediate relations. Incompleteness bites precisely where the description space out-sizes the support. The design records this so the theorem is not read as forbidding self-reference per se.

**C3 — plurality floor (Discharged).**

```lean
theorem ws5_plurality_floor {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ)
    (unif : ↥((νPk κ).str u).1 → ℝ) (hunif : ∀ r, 0 < unif r)
    (step : Attn κ u → Attn κ u)
    (hfloor : ∀ (a : Attn κ u) r, μ * unif r ≤ (step a).w r)
    (a : Attn κ u) (r : ↥((νPk κ).str u).1) : 0 < (step a).w r
```

Proof: `0 < μ * unif r ≤ (step a).w r` by `mul_pos hμ (hunif r)` then `hfloor`. Pure order algebra, no analysis. Corollary `ws5_no_delta`: the support of `step a` is all of the relation set, hence (given branching ≥ 2 from WS7's richness floor) not a Dirac delta — dynamical collapse excluded. The `μ = 0` case makes the floor `0` and is exactly where collapse re-enters; `hμ` is therefore load-bearing and stated, never assumed away.

**C4 — conditional convergence (Partial-conditional).**

```lean
theorem ws5_attention_converges
    {M : Type u} [MetricSpace M] [CompleteSpace M]
    (Tatt : M → M) (K : ℝ≥0) (hK : K < 1)
    (hcontr : ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) :
    ∃! p, Tatt p = p
```

Proof: `ContractingWith.exists_fixedPoint` (or the `∃!` wrapper). Trivial *given* `hcontr`. The scientific content is quarantined in:

```lean
/-- The replicator-with-mutation operator is a contraction on the metric
    realization. NOT PROVED — the WS5 open obstruction (charter standing risk
    "attention need not converge"). Registered as a typed hole; no inhabitant. -/
def replicator_mutator_contracts (μ : ℝ) : Prop :=
  ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] (Tatt : M → M),
    IsReplicatorMutator Tatt μ → ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y
```

`ws5_attention_converges` never instantiates this; the premise `hcontr` stays exposed at every call site.

**C6 — the honest assembly.**

```lean
structure WS5FiniteAttention (κ : Cardinal.{u}) where
  hinf         : ℵ₀ ≤ κ
  incomplete   : ∀ u : (νPk κ).X,
                   ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop), Function.Surjective e
  no_delta     : ∀ {u} (μ : ℝ), 0 < μ → PluralityFloor μ u          -- C3 packaged
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M]
                   (Tatt : M → M) (K : ℝ≥0), K < 1 →
                   (∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) → ∃! p, Tatt p = p

theorem ws5_incompleteness_and_floor (hreg : κ.IsRegular) :
    Nonempty (WS5FiniteAttention κ) := ⟨{
      hinf := hreg.aleph0_le,
      incomplete := fun u => ws5_carrier_incomplete hreg.aleph0_le u,
      no_delta := …,        -- from ws5_plurality_floor
      converges_if := fun Tatt K hK hc => ws5_attention_converges Tatt K hK hc }⟩
```

Deliberately named `ws5_incompleteness_and_floor`, **not** `ws5_resolved`: the convergence content lives only as the *conditional* field `converges_if`, and `replicator_mutator_contracts` sits outside the structure with no inhabitant. This is the WS4 naming discipline (`ws4_graded_coherence_Luk`, not `ws4_resolved`) transplanted, structurally preventing the solid incompleteness theorem from laundering the open convergence.

### 2.4 Status, hypotheses, and failure conditions

**Outcome class: Partial** (per §5). Incompleteness is **Discharged / Impossibility-proved** — a sharp negative the program wants, `(F,κ)`-robust, axiom-free, on the actual carrier. The plurality floor is **Discharged** conditional on `μ > 0` (a stated, load-bearing hypothesis, not an assumption smuggled away). Convergence is **Partial-conditional**: the Banach step is proved, the contraction premise is a typed open obligation routed as the WS5 residual.

**Hypothesis accounting.** `hinf : ℵ₀ ≤ κ` is consumed by C2 (support-vs-descriptions cardinality gap) and C3 (positivity). `κ.IsRegular` is *not* load-bearing for any WS5 result and is threaded only for charter fidelity, marked `_hreg` at the top level — mirroring the WS2 honesty note. `μ > 0` is load-bearing for C3. The contraction premise is load-bearing for C4 and is exactly what is *not* discharged.

**What counts as failure.** (a) *False incompleteness* — collapsing the description space to `(νPk κ).str u`, which trivializes C2 into a false statement; guarded by the §2.3 non-triviality remark. (b) *Dynamical collapse* — a reachable state is a Dirac delta; excluded by C3 exactly when `μ > 0`, re-entering at `μ = 0`. (c) *Non-convergence* — the replicator-mutator is expansive/chaotic for the relevant `μ`, so `replicator_mutator_contracts` is false; this is a *legitimate open outcome*, not a defect, and the design's fatal error would be reporting C4 as Discharged rather than conditional. (d) *Laundering* — naming the bundle `ws5_resolved`; structurally prevented.
