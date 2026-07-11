/-
`series-03/formal/ws5.lean`

WS5 (`series-03/spec/ws5/04-charter-design-review.md`, rev. 3): **finite attention.**
The three-spine split the charter §8.1 pre-registers: self-description
incompleteness (Impossibility-proved, `(F,κ)`-robust), the plurality/anti-collapse
floor (Discharged), and convergence (Partial-conditional — the Banach step proved,
the contraction premise a typed open obligation with no inhabitant).

Built on `ws1`/`ws2` (imported, axiom-free): `PkObj`/`PkMap`, `νPk`, `νPk_terminal`,
`ws2_nondegenerate`. WS3/WS4 are not needed.

## Outcome: PARTIAL (split), exactly as the charter §8.1 pre-registers

* **C2 — self-description incompleteness: Impossibility-proved, `(F,κ)`-robust.**
  `ws5_carrier_incomplete`: no state's attention support surjects onto its own space
  of self-descriptions `S u → Prop`. A pure Lawvere/Cantor diagonal
  (`Function.cantor_surjective`) — it consumes **no** carrier-cardinality fact and
  **no** functor-specific branching, so it survives WS4's `W_Q` and any WS7 `(F,κ)`
  unchanged (the rev. 3 robustness fix). `ws5_incomplete_nonvacuous` records that the
  gap is non-vacuous (`|S u| < |S u → Prop|`, Cantor).
* **C3 — plurality floor: Discharged.** `ws5_plurality_floor`: under a mutation
  floor `μ > 0`, every reachable weight is strictly positive; `ws5_no_delta`: no
  reachable state is a Dirac delta (given ≥2 branching, sourced from
  `ws2_nondegenerate`). `μ = 0` is exactly where collapse re-enters — `hμ` is
  load-bearing and stated. This is the discrete floored surrogate for §3.6's ODE
  (declared substitution, design §2.1a — a theorem about the floor, not the ODE).
* **C4 — convergence: Partial-conditional.** `ws5_attention_converges`: the Banach
  step, unique fixed point *given* a contraction. `replicator_mutator_contracts` is
  the typed open obligation (the charter standing risk "attention need not
  converge") — the symbol exists, no theorem inhabits it; `hcontr` stays exposed at
  every call site.
* **C6 — honest assembly.** `WS5FiniteAttention` / `ws5_incompleteness_and_floor`
  bundles the two proved halves with convergence as a *conditional* field. Named
  `ws5_incompleteness_and_floor`, **not** `ws5_resolved` (the WS4
  `ws4_graded_coherence_Luk` discipline transplanted): the incompleteness theorem
  cannot launder the open convergence, structurally.

All `sorry`-free and **axiom-free** beyond Mathlib's standard
`propext`/`Classical.choice`/`Quot.sound` (verify `#print axioms
ws5_incompleteness_and_floor`; the incompleteness core is `Classical`-only).

## Honest hypothesis note (a faithful correction to the design signature)

`ws5_attention_converges` additionally carries `[Nonempty M]`: Banach's *existence*
half is false on the empty space (`∃! p` needs a point to iterate from), and the
design's §2.3 signature omitted it. Uniqueness needs only the contraction; existence
needs nonempty + complete. This mirrors the WS2 honesty note; `κ.IsRegular` remains
non-load-bearing for every WS5 result (threaded nowhere).
-/
import ws2

universe u

open Cardinal Series03.WS1 Series03.WS2
open scoped NNReal

attribute [local instance] Classical.propDecidable

namespace Series03.WS5

variable {κ : Cardinal.{u}}

/-! ## §2.2 Self-description space (C2, rev. 3 functor-robust form) -/

/-- The attention support of `u`: the `<κ`-sized set of relations `u` attends to.
The description space is over *this* support, not the carrier `X` — which is what
makes incompleteness `(F,κ)`-robust (design §2.2). -/
abbrev SelfSupport (κ : Cardinal.{u}) (u : (νPk κ).X) : Type u := ↥((νPk κ).str u).1

/-! ## §2.3 C2 — self-description incompleteness (Impossibility-proved) -/

/-- **C2 (Impossibility-proved, `(F,κ)`-robust).** No state's attention support
surjects onto its own space of self-descriptions. Pure Lawvere/Cantor diagonal:
`Function.cantor_surjective` with description space `S u → Prop = Set (S u)`. Consumes
**no** cardinality fact and mentions the functor only through "supports are sets", so
it survives every observation functor unchanged (the rev. 3 robustness fix). -/
theorem ws5_carrier_incomplete (u : (νPk κ).X) :
    ¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e := by
  rintro ⟨e, he⟩
  exact Function.cantor_surjective e he

/-- **Non-vacuity of C2 (records the role of the `<κ` bound).** The self-description
space strictly out-sizes the support: `|S u| < |S u → Prop| = 2^|S u|` (Cantor). The
bound is what makes bounded attention genuinely unable to enumerate its own
self-descriptions — non-vacuity, not the impossibility itself. -/
theorem ws5_incomplete_nonvacuous (u : (νPk κ).X) :
    Cardinal.mk (SelfSupport κ u) < Cardinal.mk (SelfSupport κ u → Prop) := by
  have h : Cardinal.mk (SelfSupport κ u → Prop) = Cardinal.mk (Set (SelfSupport κ u)) := rfl
  rw [h, Cardinal.mk_set]
  exact Cardinal.cantor _

/-- **Non-triviality guard (remark, not a hazard).** The analogous statement with
description space `= (νPk κ).str u` (the relations themselves) is *false*: a state
enumerates its own immediate relations by the identity. Incompleteness bites only at
the predicate/power level, where self-description out-sizes the support. -/
theorem ws5_self_enumerates_relations (u : (νPk κ).X) :
    ∃ e : SelfSupport κ u → SelfSupport κ u, Function.Surjective e :=
  ⟨id, Function.surjective_id⟩

/-! ## §2.2 Attention state (C3) -/

/-- A finite-attention state on `u`: a probability weighting of its support. -/
structure Attn (κ : Cardinal.{u}) (u : (νPk κ).X) where
  w      : SelfSupport κ u → ℝ
  nonneg : ∀ r, 0 ≤ w r
  total  : HasSum w 1

/-- Support smallness is a *consequence* of summability (a summable real family has
countable support), not an axiom and not an inheritance from `PkObj`. `hinf` is kept
for charter fidelity; the countability bound holds regardless. -/
theorem Attn.supp_lt {u : (νPk κ).X} (_hinf : ℵ₀ ≤ κ) (a : Attn κ u) :
    Cardinal.mk (↥{r | a.w r ≠ 0}) ≤ Cardinal.aleph0 := by
  have hc : {r | a.w r ≠ 0}.Countable := a.total.summable.countable_support
  have : Countable ↥{r | a.w r ≠ 0} := hc.to_subtype
  exact Cardinal.mk_le_aleph0

/-! ## §2.3 C3 — plurality floor (Discharged) -/

/-- **C3 (Discharged).** Under a mutation floor `μ > 0` against a strictly positive
uniform reference, every reachable weight is strictly positive — pure order algebra,
no analysis. `hμ` is load-bearing: at `μ = 0` the floor is `0` and collapse
re-enters. -/
theorem ws5_plurality_floor {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ)
    (unif : SelfSupport κ u → ℝ) (hunif : ∀ r, 0 < unif r)
    (step : Attn κ u → Attn κ u)
    (hfloor : ∀ (a : Attn κ u) r, μ * unif r ≤ (step a).w r)
    (a : Attn κ u) (r : SelfSupport κ u) : 0 < (step a).w r :=
  lt_of_lt_of_le (mul_pos hμ (hunif r)) (hfloor a r)

/-- **Corollary `ws5_no_delta` (Discharged; branching sourced from ws2).** No
reachable state is a Dirac delta: full support (from the floor) plus ≥2 branching
excludes concentration at a single point. `hbranch` is the `ws2_nondegenerate`
≥2-branching input; `μ > 0` is load-bearing (collapse re-enters at `μ = 0`). -/
theorem ws5_no_delta {u : (νPk κ).X} (μ : ℝ) (hμ : 0 < μ)
    (unif : SelfSupport κ u → ℝ) (hunif : ∀ r, 0 < unif r)
    (step : Attn κ u → Attn κ u)
    (hfloor : ∀ (a : Attn κ u) r, μ * unif r ≤ (step a).w r)
    (hbranch : 2 ≤ Cardinal.mk (SelfSupport κ u)) (a : Attn κ u) :
    ¬ ∃ r₀, ∀ r, (step a).w r = if r = r₀ then 1 else 0 := by
  rintro ⟨r₀, hr₀⟩
  obtain ⟨x, y, hxy⟩ := Cardinal.two_le_iff.mp hbranch
  have hpos : ∀ r, 0 < (step a).w r :=
    fun r => ws5_plurality_floor μ hμ unif hunif step hfloor a r
  rcases eq_or_ne x r₀ with hx | hx
  · have hyr : y ≠ r₀ := by rw [← hx]; exact fun h => hxy h.symm
    have hp := hpos y; rw [hr₀ y, if_neg hyr] at hp; exact lt_irrefl 0 hp
  · have hp := hpos x; rw [hr₀ x, if_neg hx] at hp; exact lt_irrefl 0 hp

/-! ## §2.3 C4 — conditional convergence (Partial-conditional) -/

/-- Abstract characterization of a replicator-with-mutation update on a metric
realization of the attention simplex. Its *definition* is here; its inhabitation by
a **contraction** is the open obligation (`replicator_mutator_contracts`). -/
structure IsReplicatorMutator {M : Type u} [MetricSpace M] (Tatt : M → M) (μ : ℝ) : Prop where
  cont    : Continuous Tatt
  floored : 0 < μ

/-- **C4 Banach step (Discharged given the contraction).** A contraction on a
nonempty complete metric realization has a unique fixed point. The scientific content
— that the replicator-with-mutation *is* a contraction — is quarantined into the
hypothesis `hcontr` and never discharged here. `[Nonempty M]` is required for the
existence half (see the header hypothesis note). -/
theorem ws5_attention_converges {M : Type u} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    (Tatt : M → M) (K : ℝ≥0) (hK : K < 1)
    (hcontr : ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) :
    ∃! p, Tatt p = p := by
  have hcw : ContractingWith K Tatt := ⟨hK, LipschitzWith.of_dist_le_mul hcontr⟩
  obtain ⟨p, hp, -⟩ := hcw.exists_fixedPoint (Classical.arbitrary M) (edist_ne_top _ _)
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hne
  have hdpos : 0 < dist q p := dist_pos.mpr hne
  have hle : dist q p ≤ (K : ℝ) * dist q p := by
    have hc := hcontr q p; rwa [hq, hp] at hc
  exact absurd hle (not_le.mpr (mul_lt_of_lt_one_left hdpos (by exact_mod_cast hK)))

/-- **The WS5 open obstruction (typed, uninhabited).** "The replicator-with-mutation
operator is a contraction on the metric realization." NOT PROVED — the charter
standing risk "attention need not converge". The symbol exists; there is deliberately
**no** `theorem … : replicator_mutator_contracts μ`. `ws5_attention_converges` never
instantiates it — `hcontr` stays exposed. -/
def replicator_mutator_contracts (μ : ℝ) : Prop :=
  ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] (Tatt : M → M),
    IsReplicatorMutator Tatt μ →
      ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y

/-! ## §2.3 C6 — the honest assembly -/

/-- The plurality-floor obligation, packaged as a `Prop` for the assembly. -/
def PluralityFloor (μ : ℝ) (u : (νPk κ).X) : Prop :=
  0 < μ → ∀ (unif : SelfSupport κ u → ℝ), (∀ r, 0 < unif r) →
    ∀ (step : Attn κ u → Attn κ u),
      (∀ a r, μ * unif r ≤ (step a).w r) → ∀ a r, 0 < (step a).w r

/-- The WS5 finite-attention bundle (C6). Incompleteness and the plurality floor are
proved fields; convergence lives only as the *conditional* `converges_if`, whose type
is character-for-character the conclusion of `ws5_attention_converges` — the
contraction premise stays a hypothesis, never discharged. -/
structure WS5FiniteAttention (κ : Cardinal.{u}) where
  incomplete   : ∀ u : (νPk κ).X,
                   ¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e
  no_delta     : ∀ {u : (νPk κ).X} (μ : ℝ), PluralityFloor μ u
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] [Nonempty M]
                   (Tatt : M → M) (K : ℝ≥0), K < 1 →
                   (∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) →
                   ∃! p, Tatt p = p

/-- **The WS5 deliverable.** For every `κ`, finite attention on `νP_κ` carries
`(F,κ)`-robust self-description incompleteness and the anti-collapse plurality floor,
with convergence exposed as a conditional. Named `ws5_incompleteness_and_floor`,
**not** `ws5_resolved`: convergence is only the conditional field and
`replicator_mutator_contracts` sits outside with no inhabitant, so the split status
cannot be read as full discharge. -/
theorem ws5_incompleteness_and_floor : Nonempty (WS5FiniteAttention κ) :=
  ⟨{ incomplete   := fun u => ws5_carrier_incomplete u
   , no_delta     := fun μ => by
       intro hμ unif hunif step hfloor a r
       exact ws5_plurality_floor μ hμ unif hunif step hfloor a r
   , converges_if := fun Tatt K hK hc => ws5_attention_converges Tatt K hK hc }⟩

end Series03.WS5
