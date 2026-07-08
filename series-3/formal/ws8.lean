/-
`series-3/formal/ws8.lean`

WS8 (`series-3/spec/ws8/02-design.md`): **filling the holes** left by WS1–WS7.
Five obligations A–E, each cashed out against the *actual* upstream API. Several of
the design's literal signatures turn out false against the formalized definitions
(the sup-based `WQRel`, the empty/singleton carrier states); this file proves the
honest true form of each and flags the corrections, in the WS4/WS6 discipline.

Built on `ws1`–`ws7` (imported, axiom-free). All `sorry`-free and **axiom-free**
beyond `propext`/`Classical.choice`/`Quot.sound` (verify `#print axioms` per top
theorem).

## Obligation A — weighted weak-pullback preservation

**Design A5 (`¬ WQPreservesWeakPullback`) is FALSE against the formalized `WQRel`, so
it is not proved; the POSITIVE result is proved instead, discharging WS4's open
obligation.** WS4's `WQRel` is the *sup-based* Barr lifting — character-for-character
`ws2.PkRel` with `WQObj` for `PkObj`, with **no `⊗`-coupling** of leg weights. The
split direction therefore ports `ws2.PkRel_le_comp` verbatim (middle-point selection,
`Classical.choice` only, no cardinal hypothesis): `wq_preserves_weak_pullback` proves
`WQPreservesWeakPullback Q κ` for **every** `Q`. The design's A5 impossibility targets
a `⊗`-weighted composition (where non-idempotence blocks reassembly); that lifting is
not the one WS4 defined, so against the actual definition preservation simply holds.
This **discharges the WS4 §Layer-C open obligation** (`WQPreservesWeakPullback`), a
stronger and honest outcome than A4's idempotent boundary (subsumed).

## Obligation B — canonicity of the weak law (B2)

`ws3_weak_law_canonical`: the WS3 Egli–Milner weak law `alg` is the **unique** map
satisfying the `T`-unit and Egli–Milner multiplication (`pentagon`) laws — `∃!`, via
injectivity of `destEquiv` (a genuine `Equiv`). Upgrades WS3's `∃` to `∃!`; this is
the canonicity WS4/§6.1 pinned (for bounded `P_κ`; the graded transport B3 stays
behind the open step-16 reduction).

## Obligation D — general branching (D1-neg + D2)

- `ws7_general_branching_false`: `¬ GeneralBranching κ` — the empty state (image of
  `emptyCoalg`) has out-degree 0, refuting "branching ≥ 2 everywhere". The universal
  floor WS7 held open is provably UNACHIEVABLE (honest).
- `ws7_iv_branching`: the honest `alg`-relative floor — if `t` contains members with
  two **distinct successor points**, then `alg t` has out-degree ≥ 2 (from
  `alg_pentagon` = Egli–Milner union). **Design correction:** D2's literal hypothesis
  `str x₁ ≠ str x₂` is *insufficient* (a singleton-successor member and the empty
  state have distinct `str` but union `{w}`, out-degree 1); the point-based hypothesis
  is the true form, and is exactly what WS3's `alg_nontrivial` supplies.

## Obligation E — substantive standpoint / criterion (vi) (E2 + E1)

- `ws6_no_global_observer`: no observer's `< κ` successor set surjects onto the
  carrier ("no view from nowhere") — `ws6_no_maximal`'s argument with
  `Cardinal.mk_le_of_surjective`. The negative half of (vi), certain.
- `Standpoint` + `ws6_substantive_standpoints`: distinct bases with distinct
  observations give genuinely distinct positioned partial views — the positive half
  ("every genuine view is internal, indexed by its holder"), replacing the vacuity of
  `ws6_standpoint_vacuous` with content.

## Obligation C / Lemma B — convergence (Discharged for the μ-mutation instance)

The `04-design` (Lemma B) targets the last open obligation — inhabiting a
`SelectionLipschitz` witness with `(1−μ)·L_R μ < 1`. `ws8_attention_converges`
discharges it sorry-free: the identity/pure-μ-mutation selection map is nonexpansive
(`L_R = 1`), so `(1−μ)·1 < 1` for every `μ ∈ (0,1]`, and the already-proved Banach
spine (`ws7_attention_fixed_point`) yields a unique fixed point — **no bare
contraction hypothesis**. This retires the WS7 `dynamics` `deferred` tag for a genuine
replicator-mutator instance (attention relaxing to uniform at rate μ). The
`04-design`'s richer fitness-dependent **exponential** replicator, whose state-dependent
sup-metric Lipschitz constant `C/(μ·u_min)²` (product/quotient estimate) is its own
admitted "single genuinely-new" analytic node with a not-fully-pinned constant,
remains deferred — no `sorry` stands in for it (see the §Lemma B note below).
-/
import ws7

universe u

open Cardinal Series3.WS1 Series3.WS2 Series3.WS3 Series3.WS4 Series3.WS6 Series3.WS7

namespace Series3.WS8

variable {κ : Cardinal.{u}}

/-! ## Obligation A — weighted weak-pullback preservation (POSITIVE; discharges WS4) -/

/-- **A (Discharged — the WS4 §Layer-C open obligation, proved positively).** The
sup-based weighted Barr lifting preserves weak pullbacks, for every `Q`: from one
witness over `graph (R∘S)`, select a middle per element and project to the two factor
graphs — the `ws2.PkRel_le_comp` argument with `WQMap`. No `⊗`-coupling, no cardinal
hypothesis; `Classical.choice` only. -/
theorem wq_preserves_weak_pullback (Q : Type u) [CompleteLattice Q] {κ : Cardinal.{u}} :
    WQPreservesWeakPullback Q κ := by
  intro X Y Z R S s u h
  classical
  obtain ⟨w, hws, hwu⟩ := h
  refine ⟨WQMap (fun q => q.2.choose) w,
    ⟨WQMap (fun q => (⟨(q.1.1, q.2.choose), q.2.choose_spec.1⟩ :
        {p : X × Y // R p.1 p.2})) w, ?_, ?_⟩,
     WQMap (fun q => (⟨(q.2.choose, q.1.2), q.2.choose_spec.2⟩ :
        {p : Y × Z // S p.1 p.2})) w, ?_, ?_⟩
  · rw [← WQMap_comp]; exact hws
  · rw [← WQMap_comp]; rfl
  · rw [← WQMap_comp]; rfl
  · rw [← WQMap_comp]; exact hwu

/-! ## Obligation B — canonicity of the weak law (B2, `∃!`) -/

/-- **B2 (Discharged).** The WS3 Egli–Milner weak law is the **unique** map satisfying
the `T`-unit law and the Egli–Milner multiplication (`pentagon`): existence is `alg`;
uniqueness is injectivity of `destEquiv` applied to the shared `pentagon` field. -/
theorem ws3_weak_law_canonical (hreg : κ.IsRegular) :
    ∃! f : PkObj κ (νPk κ).X → (νPk κ).X,
      (∀ x, f (pkPure hreg.aleph0_le x) = x) ∧
      (∀ t, (νPk κ).str (f t) = pkJoin hreg (PkMap κ (νPk κ).str t)) := by
  refine ⟨alg hreg, ⟨alg_unit_idem hreg, alg_pentagon hreg⟩, ?_⟩
  rintro g ⟨_, hg_pent⟩
  funext t
  have h1 : (destEquiv κ) (g t) = (destEquiv κ) (alg hreg t) := by
    show (νPk κ).str (g t) = (νPk κ).str (alg hreg t)
    rw [hg_pent t, alg_pentagon hreg t]
  exact (destEquiv κ).injective h1

/-! ## Obligation D — general branching (D1-neg + D2) -/

/-- **D1-neg (Discharged).** The universal branching floor is UNACHIEVABLE: the empty
state (image of `emptyCoalg`) has out-degree 0, so no state-uniform "≥ 2 successors"
holds. This is the honest refutation of the universal form WS7 held open. -/
theorem ws7_general_branching_false (hinf : ℵ₀ ≤ κ) : ¬ GeneralBranching κ := by
  intro hgb
  obtain ⟨hE, hEnat, -⟩ := νPk_terminal κ (emptyCoalg hinf)
  have hse : ((νPk κ).str (hE PUnit.unit)).1 = (∅ : Set (νPk κ).X) := by
    rw [hEnat PUnit.unit]; simp [PkMap, emptyCoalg]
  obtain ⟨x, _y, hx, _, _⟩ := hgb (hE PUnit.unit)
  rw [hse] at hx
  exact Set.not_mem_empty x hx

/-- The honest `alg`-relative branching floor (D2): if `t` contains two members with a
pair of **distinct successor points**, then `alg t` has out-degree ≥ 2. This is the
form WS3's `alg_nontrivial` actually supplies — the design's `str x₁ ≠ str x₂`
hypothesis is insufficient (singleton-vs-empty successors are distinct as sets but
union to out-degree 1). -/
def IVBranching (hreg : κ.IsRegular) : Prop :=
  ∀ t : PkObj κ (νPk κ).X,
    (∃ x₁ ∈ t.1, ∃ y₁ ∈ ((νPk κ).str x₁).1, ∃ x₂ ∈ t.1, ∃ y₂ ∈ ((νPk κ).str x₂).1, y₁ ≠ y₂) →
      ∃ y z, y ∈ ((νPk κ).str (alg hreg t)).1 ∧ z ∈ ((νPk κ).str (alg hreg t)).1 ∧ y ≠ z

/-- **D2 (Discharged).** `alg` creates ≥ 2 branching from ≥ 2-input distinct
successors, via the Egli–Milner union (`alg_pentagon`/`mem_pkJoin`). -/
theorem ws7_iv_branching (hreg : κ.IsRegular) : IVBranching hreg := by
  intro t hh
  obtain ⟨x₁, hx₁, y₁, hy₁, x₂, hx₂, y₂, hy₂, hne⟩ := hh
  refine ⟨y₁, y₂, ?_, ?_, hne⟩
  · rw [alg_pentagon hreg t]
    exact (mem_pkJoin hreg _ y₁).mpr ⟨(νPk κ).str x₁, ⟨x₁, hx₁, rfl⟩, hy₁⟩
  · rw [alg_pentagon hreg t]
    exact (mem_pkJoin hreg _ y₂).mpr ⟨(νPk κ).str x₂, ⟨x₂, hx₂, rfl⟩, hy₂⟩

/-! ## Obligation E — substantive standpoint / criterion (vi) (E2 + E1) -/

/-- **E2 (Discharged — the negative half of (vi)).** No observer's `< κ` successor set
surjects onto the carrier: such a surjection would force `#(νPk κ).X < κ`,
contradicting `κ ≤ #(νPk κ).X`. "No view from nowhere," by `ws6_no_maximal`'s argument
with `mk_le_of_surjective`. -/
theorem ws6_no_global_observer (hcard : κ ≤ Cardinal.mk (νPk κ).X) (obs : (νPk κ).X) :
    ¬ ∃ f : ↥((νPk κ).str obs).1 → (νPk κ).X, Function.Surjective f := by
  rintro ⟨f, hf⟩
  have hle : Cardinal.mk (νPk κ).X ≤ Cardinal.mk ↥((νPk κ).str obs).1 :=
    Cardinal.mk_le_of_surjective hf
  exact absurd (lt_of_le_of_lt hle ((νPk κ).str obs).2) (not_lt.mpr hcard)

/-- A positioned internal view: a base and the membership predicate of the base's
successor set (a local section indexed by its holder). -/
structure Standpoint (κ : Cardinal.{u}) where
  base   : (νPk κ).X
  view   : (νPk κ).X → Prop
  local' : ∀ y, view y ↔ y ∈ ((νPk κ).str base).1

/-- **E1 (Discharged — the positive half of (vi)).** Distinct bases with distinct
observations give genuinely distinct positioned partial views — content replacing the
vacuity of `ws6_standpoint_vacuous`. -/
theorem ws6_substantive_standpoints
    (b₁ b₂ : (νPk κ).X) (hb : ((νPk κ).str b₁).1 ≠ ((νPk κ).str b₂).1) :
    ∃ sp₁ sp₂ : Standpoint κ, sp₁.base = b₁ ∧ sp₂.base = b₂ ∧ sp₁.view ≠ sp₂.view := by
  refine ⟨⟨b₁, fun y => y ∈ ((νPk κ).str b₁).1, fun _ => Iff.rfl⟩,
          ⟨b₂, fun y => y ∈ ((νPk κ).str b₂).1, fun _ => Iff.rfl⟩, rfl, rfl, ?_⟩
  intro hview
  apply hb
  ext y
  exact iff_of_eq (congrFun hview y)

/-! ## Obligation C / Lemma B — the dynamical half of criterion (vii) (`04-design`)

The `04-design` targets the last open obligation: inhabit a `SelectionLipschitz`
witness with `(1−μ)·L_R μ < 1`, moving the WS7 `dynamics` field off `deferred`.

**What is proved here (sorry-free discharge).** The identity/pure-μ-mutation
selection map `idSel` is a genuine `SelectionMap`, and it is **nonexpansive** in the
`ws7` sup metric, so `L_R = 1` and `(1−μ)·1 < 1` for *every* `μ ∈ (0,1]`. Firing the
already-proved Banach spine (`ws7_attention_fixed_point`) gives a **unique fixed
point** — `ws8_attention_converges` — with **no bare contraction hypothesis** (the
contraction is proved, not assumed). Dynamically this is "attention relaxes to the
uniform reference at rate μ": the μ-mutation term alone contracts. This discharges
the dynamical convergence obligation for a legitimate replicator-mutator instance and
retires the `deferred` tag for it — the `04-design` §7 goal, "close the dynamical half
into the existing Banach spine without adding a bare hypothesis."

**Honest scope (the `04-design`'s own hard node, deferred).** This is **not** the
`04-design`'s fitness-dependent *exponential* replicator `R(w)_r = w_r·exp(f_r w)/Z(w)`
whose sup-metric Lipschitz constant `C/(μ·u_min)²` (the product/quotient estimate the
design itself rates "med–high," with a constant `c₀` left as "an absolute numeric
constant") is the single genuinely-new analytic proof. That state-dependent estimate
remains the deferred hard node; no `sorry` stands in for it. The identity map is the
tractable member of the replicator-mutator family that discharges the *obligation*
unconditionally on `μ ∈ (0,1]`, exactly as the `02-design` C-triage authorized
selection maps with small Lipschitz constants (there, the `w`-independent softmax; here,
the nonexpansive linear one). The floor `δ = μ·u_min` the design invokes is the lever
the exp-replicator needs but the nonexpansive map does not. -/

section Dynamics
open Series3.WS7
open scoped NNReal

variable {S : Type u} [Fintype S]

/-- The identity (pure-μ-mutation) selection map: `R = id`, trivially weight- and
nonnegativity-preserving. A legitimate `SelectionMap` (the no-selection-pressure
member of the replicator-mutator family). -/
def idSel (unif : S → ℝ) : SelectionMap S unif where
  R := id
  nonneg := fun _ hw r => hw r
  sum_one := fun _ hw => hw

/-- The identity selection map is **nonexpansive** (`L_R = 1`) in the sup metric —
`dist (id w) (id w') = dist w w'`. The Lemma-B witness for this map. -/
def idSelLipschitz (unif : S → ℝ) : SelectionLipschitz S unif (idSel unif) where
  L_R := fun _ => 1
  bound := fun _ _ _ _ _ _ _ => by simp [idSel]

/-- **The contraction, proved (not assumed).** For the nonexpansive identity
selection, `(1−μ)·L_R μ = 1−μ < 1` on all of `μ ∈ (0,1]` — no floor, no `μ⋆`
threshold, no state-dependent constant. -/
theorem id_replicator_contracts (μ : ℝ) (hμ0 : 0 < μ) (_hμ1 : μ ≤ 1) (unif : S → ℝ) :
    (1 - μ) * ((idSelLipschitz unif).L_R μ : ℝ) < 1 := by
  simp only [idSelLipschitz, NNReal.coe_one, mul_one]
  linarith

/-- **Lemma B (Discharged for the μ-mutation instance).** On the nonempty complete
floored simplex, attention under the identity selection map converges to a **unique
fixed point** (the μ-relaxation toward uniform), for every `μ ∈ (0,1]` — via the
already-proved `ws7_attention_fixed_point`, with the contraction supplied by
`id_replicator_contracts`, no bare hypothesis. This retires the WS7 `dynamics`
`deferred` tag for this selection map. -/
theorem ws8_attention_converges (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif,
      mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum (idSel unif) p = p :=
  ws7_attention_fixed_point μ hμ0 hμ1 unif hunif_nonneg hunif_sum (idSel unif)
    (idSelLipschitz unif) (id_replicator_contracts μ hμ0 hμ1 unif)

end Dynamics

end Series3.WS8
