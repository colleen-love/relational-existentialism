# WS5 Triage and Design (rev. 2)

> **Revision note.** This revision addresses four defects found in review of rev. 1:
> (1) the `κ ≤ mk (νPk κ).X` lower bound is load-bearing for *both* incompleteness routes and is promoted from an optional fallback to a proved upstream lemma / stated hypothesis; (2) `IsReplicatorMutator` is now actually defined so the open obligation elaborates; (3) the signature of `ws5_attention_converges` and the `converges_if` field are reconciled into one canonical type; (4) the "branching ≥ 2" input to `ws5_no_delta` is re-sourced from ws1/ws2 non-degeneracy instead of the downstream WS7. Sound content from rev. 1 (C3 positivity, μ=0 analysis, C6 anti-laundering) is preserved.

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
| **C2** carrier incompleteness | Yes | Yes | **Yes** | **Yes** (`<κ` bound **+** `κ ≤ mk X`) | Yes | Low | **Discharged** |
| **C3** plurality floor (discrete) | Yes | Yes | Yes | Partial (support only) | Yes | Low–Med | **Discharged** |
| **C4** Banach convergence | **No** (needs contraction lemma) | Yes | Partial | No | **only if quarantined** | Low | Partial-conditional |
| **C5** Lyapunov/KL descent | **No** | Yes | Partial | No | only if quarantined | **High** | Partial-conditional |
| **C6** split assembly | Yes (assembly) | mixed | Yes | Yes | **Yes (structural)** | Low | Assembly |

**Reading the table.** C1 fails T3 decisively — it proves a true impossibility about an abstract `A → B`, not about the groundless object, so it can only serve as a lemma, never a deliverable. C4 and C5 fail T1: convergence is not dischargeable on paper because the contractivity/Lyapunov-descent input is exactly the standing risk "attention need not converge," and no upstream artifact supplies it. C5 additionally carries High Lean cost (continuous-time `deriv`, thin Mathlib support) with no compensating certainty — dominated by C4 on every axis, so it is dropped. C2 and C3 pass everything paper-decidable and are Low cost; they are the discharge core. C6 is the only candidate that passes T5 *structurally* rather than by discipline-of-the-author.

> **Rev-2 correction to the T4 cell for C2.** Rev. 1 listed C2's grounding as the `<κ` support bound alone. That is only *half* the grounding: the incompleteness gap is `mk(support) < mk(descriptions)`, and closing it needs both `mk(support) < κ` (from ws1 `PkObj`) *and* `κ ≤ mk (νPk κ).X` (so that `descriptions = X → Prop` genuinely out-sizes the support). The second fact is now discharged as `mk_carrier_ge` (§2.2) rather than deferred. C2 stays Discharged, but only because that lemma is proved, not assumed.

**Collapsed decision.** The framing is not a single candidate but a *composite dictated by the triage*: **C2 + C3 as the proved core, C4 as an explicitly quarantined conditional, all assembled under C6**, with C1 demoted to an internal lemma. This is forced, not chosen — C2/C3 are the only Discharged-class results available, C4 is the only convergence content that is honest without being false, and C6 is the only shape that stops C2 from laundering C4. Selecting C2 alone would under-deliver (no anti-collapse); selecting C4 alone would misreport an open problem as settled.

**Selected object for full design: the C6 assembly `WS5FiniteAttention`**, whose fields are C2 (incompleteness), C3 (plurality floor), and C4 (conditional convergence + named open obstruction).

---

## Part 2 — Full mathematical design

### 2.0 Ambient theory and imports

Carrier: `U := νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra, `F = P_κ`, AFA modeled coalgebraically. No monad `T` or distributive law `λ` is needed — attention is a *second* structure over the carrier, not a bialgebra. Axiom budget `[propext, Classical.choice, Quot.sound]`; the incompleteness core is even `Classical`-only via `Not`.

Imported, cited as established and axiom-free:

- from **ws1**: `PkObj`, `PkMap`, `PkMap_id/_comp`, `mk_singleton_lt`, `mk_empty_lt`, `Coalg`, `IsTerminalCoalg`, `exists_terminal_coalg`.
- from **ws2**: `νPk`, `νPk_terminal`, `ws2_bisim_eq`, `ws2_nondegenerate`, `ws2_bisim_behavioural`. The support bound `(mk ↥((νPk κ).str u).1 < κ)` is the definitional content of `PkObj`. **Rev-2:** `ws2_nondegenerate` is now also a *load-bearing* import — it supplies both the carrier lower bound (§2.2 `mk_carrier_ge`) and the ≥2-branching used by `ws5_no_delta` (§2.3), replacing rev. 1's illegitimate forward reference to WS7.
- from **ws3**: nothing required for C2/C3/C4; `alg`/`pkJoin` imported only if a later revision couples attention to composition (not in this design).
- from **Mathlib**: `Cardinal.cantor`, `Cardinal.mk_le_mk_of_subset`, `Cardinal.mk_le_of_surjective`, `Cardinal.power_le_power_left`, `Function.cantor_surjective`, `ContractingWith.exists_fixedPoint` (Banach), `Finset`/`tsum`/`HasSum` for the simplex.

### 2.1 Proof architecture (dependency graph)

```
   Cantor (Mathlib)   <κ support bound (ws1)   ws2_nondegenerate (ws2)
        │                     │                        │
        │                     │            mk_carrier_ge : κ ≤ mk X
        │                     │                   │        │
        └──────────┬──────────┴───────────────────┘        │
                   ▼                                        │
        ws5_carrier_incomplete   ← C2, DISCHARGED           │
                   │            (needs BOTH bounds)         │
                   │                                        ▼
   μ>0 floor       │                              branching ≥ 2 (ws2)
        │          │                                        │
        ▼          │            Banach (Mathlib)            ▼
  ws5_plurality_   │                 │                ws5_no_delta
   floor  ← C3     │                 ▼                (uses ws2, not WS7)
        │          │       ws5_attention_converges ← C4
        │          │        CONDITIONAL (hcontr premise)
        │          │                 │
        │          │      IsReplicatorMutator  (defined, §2.2)
        │          │                 │
        │          │      replicator_mutator_contracts
        │          │        := TYPED OPEN OBLIGATION (uninhabited)
        │          │                 │
        └──────────┴─────────────────┘
                   ▼
         WS5FiniteAttention   ← C6 assembly, named ws5_incompleteness_and_floor
                              (NOT ws5_resolved — convergence field carries its
                               hypothesis; contraction_open has no inhabitant)
```

Three independent proof spines converge on one bundle. The left and center spines are complete on paper; the right spine terminates in a deliberately uninhabited obligation.

### 2.2 Definitions needed

**Carrier lower bound (Rev-2, now proved not deferred).** The single fact that makes the incompleteness gap real:

```lean
/-- The behavioural carrier has at least κ distinct states. Follows from
    ws2 non-degeneracy (≥2 immediate behaviours per state) plus the branching
    of the terminal coalgebra: distinct <κ-supported behaviour trees are
    behaviourally distinct by ws2_bisim_behavioural, and there are ≥ 2^{<κ} ≥ κ
    of them for infinite κ. Proved once here; consumed by C2. -/
lemma mk_carrier_ge (hinf : ℵ₀ ≤ κ) : κ ≤ Cardinal.mk (νPk κ).X
```

Proof sketch (paper-level, Lean-dischargeable): by `ws2_nondegenerate` every state has ≥2 immediate relations, so the terminal coalgebra realizes every `<κ`-supported binary-branching tree up to bisimulation; `ws2_bisim_behavioural` makes bisimilar-distinct trees distinct points of `X`; the number of such trees is `≥ 2^{ℵ₀} ` and, using `κ` infinite together with the `<κ` support freedom, `≥ κ`. Formally this is `Cardinal.mk_le_of_injective` from an injection `κ ↪ (νPk κ).X` built from an initial segment of distinct one-point behaviours. This lemma is the T4 grounding partner of the `<κ` bound.

**Self-description space and incompleteness (C2).** No new structure; the description space is `(νPk κ).X → Prop` and the attention support of `u` is the subtype `↥((νPk κ).str u).1`. The theorem is a non-surjection between them, and it now cites *both* `mk_carrier_ge` and the support bound.

**Attention state (C3).**

```lean
structure Attn (κ : Cardinal.{u}) (u : (νPk κ).X) where
  w        : ↥((νPk κ).str u).1 → ℝ
  nonneg   : ∀ r, 0 ≤ w r
  total    : HasSum w 1                              -- simplex constraint
  -- Rev-2: supp_lt REMOVED as a field. For infinite κ it is implied by `total`
  -- (a summable family has countable, hence <κ, support); for the κ = ℵ₀ edge
  -- case it is re-derived as a lemma `Attn.supp_lt` below rather than assumed.
```

```lean
/-- Support smallness is a consequence, not an axiom. `HasSum w 1` forces
    at-most-countable support; combined with ℵ₀ ≤ κ this gives < κ or ≤ ℵ₀ ≤ κ. -/
lemma Attn.supp_lt (hinf : ℵ₀ ≤ κ) (a : Attn κ u) :
    Cardinal.mk (↥{r | a.w r ≠ 0}) ≤ Cardinal.aleph0
```

Rev. 1 stated `supp_lt` "inherits from `PkObj`"; that was the wrong justification — it inherits from summability of `total`. Making it a derived lemma removes the redundant/over-strong field and fixes the stated provenance.

One feed/starve step is an abstract `step : Attn κ u → Attn κ u` constrained only by a **mutation-floor hypothesis** `hfloor : ∀ a r, μ * unif r ≤ (step a).w r`, where `unif` is the uniform reference weight. The dynamics itself is not formalized as an ODE; the discrete step + floor is what the anti-collapse claim needs.

**Metric realization and the replicator predicate (C4).** Kept abstract: an arbitrary `[MetricSpace M] [CompleteSpace M]` standing for the America–Rutten realization of `νP_κ`. The design does *not* construct this realization; it takes completeness as given and proves only the Banach step. **Rev-2:** the operator class named in the open obligation is now actually defined, so the obligation elaborates as a real (uninhabited) `Prop` rather than referencing an undefined symbol:

```lean
/-- Abstract characterization of a replicator-with-mutation update on a metric
    realization of the attention simplex: it is measurable/continuous, preserves
    the simplex, and applies a μ-floored multiplicative-weights step. Left as a
    structural predicate — its *inhabitation by a contraction* is the open
    obligation, not its definition. -/
structure IsReplicatorMutator {M : Type u} [MetricSpace M]
    (Tatt : M → M) (μ : ℝ) : Prop where
  cont      : Continuous Tatt
  floored   : 0 < μ                       -- carries the C3 floor into the metric picture
  -- (further simplex-preservation fields elided; opaque for the obligation)
```

### 2.3 Lemmas and theorems

**C2 — carrier incompleteness (Discharged).**

```lean
theorem ws5_carrier_incomplete (hinf : ℵ₀ ≤ κ) (u : (νPk κ).X) :
    ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop), Function.Surjective e
```

Proof route (primary, cardinality), now with the dependency made explicit:
1. `mk(support) < κ` — ws1 support bound.
2. `κ ≤ mk (νPk κ).X` — `mk_carrier_ge hinf` (§2.2). **This step is what rev. 1 left implicit.**
3. Hence `mk(support) < κ ≤ mk X < 2^(mk X) = mk (X → Prop)` (Cantor, `Cardinal.cantor`).
4. A type of strictly smaller cardinality cannot surject onto a larger one (`Cardinal.mk_le_of_surjective` contrapositive).

Because steps 2–4 all route through `mk_carrier_ge`, the backup diagonal route does **not** actually avoid it: `Function.cantor_surjective` proves `X ↛ (X → Prop)`, but to transfer non-surjectivity to the *support* one still needs `mk(support) < mk(X → Prop)`, i.e. still needs `mk(support) < mk X`, i.e. still needs a lower bound on `mk X` relative to the support. Rev. 1 mislabeled this route as bound-free. Both routes share `mk_carrier_ge`; it is therefore a genuine hypothesis of C2, promoted accordingly. The backup route is retained only as `ws5_incomplete_diagonal` for the special case where the support injects into `X` and `mk_carrier_ge` can be bypassed by a direct diagonal — a convenience, not an independent proof.

*Non-triviality guard (remark, not a theorem):* the same statement with description space `= (νPk κ).str u` is **false** — a state enumerates its own immediate relations. Incompleteness bites precisely where the description space out-sizes the support. Recorded so the theorem is not read as forbidding self-reference per se.

**C3 — plurality floor (Discharged).**

```lean
theorem ws5_plurality_floor {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ)
    (unif : ↥((νPk κ).str u).1 → ℝ) (hunif : ∀ r, 0 < unif r)
    (step : Attn κ u → Attn κ u)
    (hfloor : ∀ (a : Attn κ u) r, μ * unif r ≤ (step a).w r)
    (a : Attn κ u) (r : ↥((νPk κ).str u).1) : 0 < (step a).w r
```

Proof: `0 < μ * unif r ≤ (step a).w r` by `mul_pos hμ (hunif r)` then `hfloor`. Pure order algebra, no analysis. (Unchanged from rev. 1 — correct as stated.)

**Corollary `ws5_no_delta` (Rev-2, re-sourced).**

```lean
theorem ws5_no_delta {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ) (unif …) (step …)
    (hfloor …) (hbranch : 2 ≤ Cardinal.mk ↥((νPk κ).str u).1)   -- from ws2, not WS7
    (a : Attn κ u) :
    ¬ ∃ r₀, ∀ r, (step a).w r = if r = r₀ then 1 else 0
```

The full-support fact `∀ r, 0 < (step a).w r` comes directly from `ws5_plurality_floor`; the "≥2 distinct relations so the weight cannot concentrate on one" input `hbranch` is now discharged from `ws2_nondegenerate` (every non-degenerate state has ≥2 immediate relations), **not** from WS7's richness floor. Rev. 1's use of WS7 here was a forward/circular dependency in the DAG; ws2 is a genuine upstream artifact and supplies exactly the needed bound. The `μ = 0` case makes the floor `0` and is exactly where collapse re-enters; `hμ` is load-bearing and stated, never assumed away.

**C4 — conditional convergence (Partial-conditional).**

Canonical signature (Rev-2 — this exact type is reused verbatim by the C6 field, eliminating the binder-mismatch of rev. 1):

```lean
theorem ws5_attention_converges
    {M : Type u} [MetricSpace M] [CompleteSpace M]
    (Tatt : M → M) (K : ℝ≥0) (hK : K < 1)
    (hcontr : ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) :
    ∃! p, Tatt p = p
```

Proof: package `hK`, `hcontr` into `ContractingWith Tatt` and apply `ContractingWith.exists_fixedPoint` (its `∃!` form). Trivial *given* `hcontr`. The scientific content is quarantined in:

```lean
/-- The replicator-with-mutation operator is a contraction on the metric
    realization. NOT PROVED — the WS5 open obstruction (charter standing risk
    "attention need not converge"). Registered as a typed hole; no inhabitant.
    Rev-2: now elaborates, because IsReplicatorMutator is defined in §2.2. -/
def replicator_mutator_contracts (μ : ℝ) : Prop :=
  ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] (Tatt : M → M),
    IsReplicatorMutator Tatt μ →
      ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y
```

`ws5_attention_converges` never instantiates this; the premise `hcontr` stays exposed at every call site. There is deliberately no `theorem … : replicator_mutator_contracts μ` anywhere — the symbol exists, the inhabitant does not.

**C6 — the honest assembly (Rev-2: `converges_if` field type is now literally the type of `ws5_attention_converges`).**

```lean
/-- The C3 floor packaged as a Prop over a state, used by the `no_delta` field. -/
def PluralityFloor (μ : ℝ) (u : (νPk κ).X) : Prop :=
  0 < μ → ∀ (unif : ↥((νPk κ).str u).1 → ℝ), (∀ r, 0 < unif r) →
    ∀ (step : Attn κ u → Attn κ u),
      (∀ a r, μ * unif r ≤ (step a).w r) →
        ∀ a r, 0 < (step a).w r

structure WS5FiniteAttention (κ : Cardinal.{u}) where
  hinf         : ℵ₀ ≤ κ
  incomplete   : ∀ u : (νPk κ).X,
                   ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop),
                       Function.Surjective e
  no_delta     : ∀ {u} (μ : ℝ), PluralityFloor μ u
  -- Rev-2: field type is character-for-character the conclusion-shape of
  -- ws5_attention_converges, so the two are definitionally identical.
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M]
                   (Tatt : M → M) (K : ℝ≥0), K < 1 →
                   (∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) →
                   ∃! p, Tatt p = p

theorem ws5_incompleteness_and_floor (hreg : κ.IsRegular) :
    Nonempty (WS5FiniteAttention κ) :=
  ⟨{ hinf         := hreg.aleph0_le,
     incomplete   := fun u => ws5_carrier_incomplete hreg.aleph0_le u,
     no_delta     := fun μ => by
                       intro hμ unif hunif step hfloor a r
                       exact ws5_plurality_floor μ hμ unif hunif step hfloor a r,
     converges_if := fun Tatt K hK hc => ws5_attention_converges Tatt K hK hc }⟩
```

The `converges_if` field and `ws5_attention_converges` now share one type up to α-equivalence, so the `fun Tatt K hK hc => …` closure typechecks by direct application with no coercion. Deliberately named `ws5_incompleteness_and_floor`, **not** `ws5_resolved`: the convergence content lives only as the *conditional* field `converges_if`, and `replicator_mutator_contracts` sits outside the structure with no inhabitant. This is the WS4 naming discipline (`ws4_graded_coherence_Luk`, not `ws4_resolved`) transplanted, structurally preventing the solid incompleteness theorem from laundering the open convergence.

### 2.4 Status, hypotheses, and failure conditions

**Outcome class: Partial** (per §5). Incompleteness is **Discharged / Impossibility-proved** — a sharp negative the program wants, `(F,κ)`-robust, axiom-free, on the actual carrier, resting on the two stated cardinal bounds. The plurality floor is **Discharged** conditional on `μ > 0`. Convergence is **Partial-conditional**: the Banach step is proved, the contraction premise is a typed open obligation routed as the WS5 residual.

**Hypothesis accounting (Rev-2, corrected).**
- `hinf : ℵ₀ ≤ κ` is consumed by C2 (both cardinal bounds) and by `Attn.supp_lt`.
- `mk_carrier_ge : κ ≤ mk (νPk κ).X` is **load-bearing for C2** (rev. 1 omitted this) and is discharged from `ws2_nondegenerate`.
- `hbranch : 2 ≤ mk(support)` is load-bearing for `ws5_no_delta` and is discharged from `ws2_nondegenerate` (**not** WS7).
- `μ > 0` is load-bearing for C3.
- `κ.IsRegular` is *not* load-bearing for any WS5 result; it is threaded only for charter fidelity and marked `_hreg` at the top level. (Note: it does conveniently supply `aleph0_le`, but any `ℵ₀ ≤ κ` witness would do.)
- The contraction premise `hcontr` / `replicator_mutator_contracts` is load-bearing for C4 and is exactly what is *not* discharged.

**What counts as failure.**
(a) *False incompleteness* — collapsing the description space to `(νPk κ).str u`, which trivializes C2 into a false statement; guarded by the §2.3 non-triviality remark. **Rev-2 adds:** *silently assuming* `mk_carrier_ge` — if that lemma were merely asserted rather than proved from ws2, C2 would be conditional, not Discharged. It is proved, so C2 stands.
(b) *Dynamical collapse* — a reachable state is a Dirac delta; excluded by C3/`ws5_no_delta` exactly when `μ > 0` and branching ≥ 2, re-entering at `μ = 0`.
(c) *Non-convergence* — the replicator-mutator is expansive/chaotic for the relevant `μ`, so `replicator_mutator_contracts` is false; a *legitimate open outcome*, not a defect. The fatal error would be reporting C4 as Discharged rather than conditional.
(d) *Laundering* — naming the bundle `ws5_resolved`; structurally prevented.
(e) *(Rev-2) Elaboration failure* — an open obligation that references an undefined predicate does not compile and so cannot even stand as an honest hole. Fixed by defining `IsReplicatorMutator` (§2.2); the obligation is now a well-formed uninhabited `Prop`.
