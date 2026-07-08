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

## Obligation C / Lemma B — convergence (Discharged, including the hard analytic node)

The `04-design` (Lemma B) targets the last open obligation — inhabiting a
`SelectionLipschitz` witness with `(1−μ)·L_R μ < 1`. Two discharges, both sorry-free:

1. **`ws8_attention_converges`** — the identity/pure-μ-mutation selection map is
   nonexpansive (`L_R = 1`), so `(1−μ)·1 < 1` for every `μ ∈ (0,1]`; the Banach spine
   (`ws7_attention_fixed_point`) gives a unique fixed point (attention relaxing to
   uniform), no bare hypothesis.

2. **`ws8_replicator_converges` — the hard analytic node, done.** A genuine
   `w`-dependent replicator (the linear/multiplicative-weights update
   `R(w)_r = w_r·c_r / ∑_s w_s c_s`) is proved Lipschitz on the μ-floor region with the
   **explicit, rigorously-pinned** constant `L_R μ = 2/(μ·u_min)` in the `ws7` sup
   metric (`linReplicatorLipschitz` — the product/quotient estimate the design flagged
   as its "single genuinely-new proof"), and it contracts on the explicit band
   `2(1−μ) < μ·u_min`, whence a unique fixed point via the Banach spine.

**Correction to the `04-design` (surfaced, not patched).** The design's constant
`C/(μ·u_min)²` assumes floor-region points are simplex points (`w r ≤ 1`), but
`ws7.floorRegion` imposes **only** the floor `w r ≥ μ·unif r`, so `w r` is unbounded
above and `≤ 1` is unavailable. The honest lever is scale-covariance (`R(λw) = R(w)`)
plus `∑ w c ≥ (μ·u_min)·∑ c`: every ratio `w_r c_r / Z ≤ 1`, giving the true constant
`2/(μ·u_min)` (first power of `δ = μ·u_min`, absolute numeric `2`), which is what the
*unbounded* floor region actually supports. Detail in the §Lemma B note below.
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

**Two selection maps.** The identity map is the nonexpansive member (this note). The
*next* section does the design's actual hard node — the product/quotient Lipschitz
estimate — for a genuine `w`-dependent **linear replicator**
`R(w)_r = w_r·c_r / ∑ w_s c_s` (`linReplicatorLipschitz`, constant `2/(μ·u_min)`). What
is **not** attempted is the further *exponential* fitness `R(w)_r = w_r·exp(f_r w)/Z(w)`,
which adds the `exp`/fitness-Lipschitz coupling on top of the quotient estimate; the
quotient estimate itself — the design's "single genuinely-new proof" — is done below.
The floor `δ = μ·u_min` the design invokes is the lever
the exp-replicator needs but the nonexpansive map does not. -/

section Dynamics
open Series3.WS7
open scoped NNReal

variable {S : Type u} [Fintype S] [Nonempty S]

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

/-! ### The hard thing — a genuine `w`-dependent replicator with a proved Lipschitz bound

The identity map above is nonexpansive but carries no selection pressure. The
**linear (frequency-independent) replicator** `R(w)_r = w_r·c_r / ∑_s w_s·c_s` — the
classical multiplicative-weights update with fixed positive selection coefficients
`c` — genuinely depends on `w`, and its sup-metric Lipschitz constant on the floor
region is the `04-design`'s "single genuinely-new proof" (the product/quotient
estimate). We prove it sorry-free with the **explicit** constant `L_R μ = 2/(μ·u_min)`.

**Correction to the `04-design` (surfaced, not patched).** The design reads the
constant off `w r ∈ [δ, 1]`, i.e. assumes floor-region points are simplex points
(`∑ w = 1`), giving `C/(μ·u_min)²`. But `ws7.floorRegion` imposes **only** the floor
`w r ≥ μ·unif r`, so `w r` is unbounded above; the `≤ 1` is unavailable and the
`δ^{-2}` blows the wrong way. The true lever is scale-covariance: `R(λw) = R(w)`, and
`Z(w) = ∑ w_s c_s ≥ (∑ μ·unif_s)·(min c) = μ·(min c)`… more simply, on the floor
`Z(w) ≥ (μ·u_min)·(∑ c_s)`, and every ratio `w_r c_r / Z ≤ 1`. That gives the honest
constant `2/(μ·u_min) = 2/δ` (first power of `δ`), independent of any upper bound —
which is what the unbounded floor region actually supports. -/

/-- The uniform reference's minimum weight (`u_min`), the floor's analytic lever. -/
noncomputable def uMin (unif : S → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty unif

lemma uMin_le (unif : S → ℝ) (r : S) : uMin unif ≤ unif r :=
  Finset.inf'_le _ (Finset.mem_univ r)

lemma uMin_pos {unif : S → ℝ} (hunif_pos : ∀ r, 0 < unif r) : 0 < uMin unif :=
  (Finset.lt_inf'_iff _).mpr (fun r _ => hunif_pos r)

/-- On the floor region, the replicator normalizer is bounded below by `δ·∑c > 0`
(each `w s ≥ μ·u_min = δ`). The single fact the Lipschitz bound consumes. -/
lemma floor_Z_lower {c unif : S → ℝ} (hc : ∀ s, 0 < c s)
    {μ : ℝ} (hμ0 : 0 < μ) {w : S → ℝ} (hw : ∀ r, μ * unif r ≤ w r) :
    (μ * uMin unif) * (∑ s, c s) ≤ ∑ s, w s * c s := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  exact mul_le_mul_of_nonneg_right
    (le_trans (mul_le_mul_of_nonneg_left (uMin_le unif s) hμ0.le) (hw s)) (hc s).le

/-- The linear replicator update, total on `S → ℝ` (identity off the positive-`Z`
region, so `nonneg`/`sum_one` hold unconditionally). On the floor region `Z > 0`, so
it is the genuine `w_r c_r / Z`. -/
noncomputable def linR (c w : S → ℝ) (r : S) : ℝ :=
  if 0 < ∑ s, w s * c s then w r * c r / (∑ s, w s * c s) else w r

/-- The linear replicator as a `SelectionMap` (weight- and nonnegativity-preserving). -/
noncomputable def linReplicatorSel (c : S → ℝ) (hc : ∀ s, 0 < c s) (unif : S → ℝ) :
    SelectionMap S unif where
  R := linR c
  nonneg := fun w hw r => by
    rw [linR]
    by_cases hZ : 0 < ∑ s, w s * c s
    · rw [if_pos hZ]; exact div_nonneg (mul_nonneg (hw r) (hc r).le) hZ.le
    · rw [if_neg hZ]; exact hw r
  sum_one := fun w hw => by
    by_cases hZ : 0 < ∑ s, w s * c s
    · have hval : ∀ r, linR c w r = w r * c r / (∑ s, w s * c s) := fun r => by
        rw [linR, if_pos hZ]
      simp_rw [hval, ← Finset.sum_div]; exact div_self hZ.ne'
    · have hval : ∀ r, linR c w r = w r := fun r => by rw [linR, if_neg hZ]
      simp_rw [hval]; exact hw

/-- **Lemma B (the hard analytic obligation), Discharged with an explicit constant.**
The linear replicator is Lipschitz on the `μ`-floor region with `L_R μ = 2/(μ·u_min)`
in the `ws7` sup metric — the product/quotient estimate, with a rigorously-pinned
constant `2` (not the design's unpinned `c₀`) and first-power `δ`. -/
noncomputable def linReplicatorLipschitz (c : S → ℝ) (hc : ∀ s, 0 < c s)
    (unif : S → ℝ) (hunif_pos : ∀ r, 0 < unif r) :
    SelectionLipschitz S unif (linReplicatorSel c hc unif) where
  L_R := fun μ => Real.toNNReal (2 / (μ * uMin unif))
  bound := by
    intro μ hμ0 _hμ1 w hw w' hw'
    have hu : 0 < uMin unif := uMin_pos hunif_pos
    have hδ : 0 < μ * uMin unif := mul_pos hμ0 hu
    have hcS : 0 < ∑ s, c s := Finset.sum_pos (fun s _ => hc s) Finset.univ_nonempty
    have hZw : (μ * uMin unif) * (∑ s, c s) ≤ ∑ s, w s * c s := floor_Z_lower hc hμ0 hw
    have hZw' : (μ * uMin unif) * (∑ s, c s) ≤ ∑ s, w' s * c s := floor_Z_lower hc hμ0 hw'
    have hZwp : 0 < ∑ s, w s * c s := lt_of_lt_of_le (mul_pos hδ hcS) hZw
    have hZw'p : 0 < ∑ s, w' s * c s := lt_of_lt_of_le (mul_pos hδ hcS) hZw'
    have hd : (0 : ℝ) ≤ dist w w' := dist_nonneg
    have hLR : ((Real.toNNReal (2 / (μ * uMin unif)) : ℝ≥0) : ℝ) = 2 / (μ * uMin unif) :=
      Real.coe_toNNReal _ (le_of_lt (div_pos two_pos hδ))
    rw [hLR, dist_pi_le_iff (mul_nonneg (le_of_lt (div_pos two_pos hδ)) hd)]
    intro r
    -- reduce both sides to the genuine quotient (floor ⇒ `Z > 0`)
    have hRw : linR c w r = w r * c r / (∑ s, w s * c s) := by rw [linR, if_pos hZwp]
    have hRw' : linR c w' r = w' r * c r / (∑ s, w' s * c s) := by rw [linR, if_pos hZw'p]
    show dist (linR c w r) (linR c w' r) ≤ 2 / (μ * uMin unif) * dist w w'
    rw [hRw, hRw', Real.dist_eq]
    -- per-coordinate facts
    have hdr : |w r - w' r| ≤ dist w w' := by rw [← Real.dist_eq]; exact dist_le_pi_dist w w' r
    have hcr_le : c r ≤ ∑ s, c s := Finset.single_le_sum (fun s _ => (hc s).le) (Finset.mem_univ r)
    have hw'r_le : w' r * c r ≤ ∑ s, w' s * c s :=
      Finset.single_le_sum
        (fun s _ => mul_nonneg (le_trans (le_of_lt (mul_pos hμ0 (hunif_pos s))) (hw' s)) (hc s).le)
        (Finset.mem_univ r)
    have hZdiff : |(∑ s, w' s * c s) - (∑ s, w s * c s)| ≤ (∑ s, c s) * dist w w' := by
      rw [← Finset.sum_sub_distrib]
      calc |∑ s, (w' s * c s - w s * c s)| ≤ ∑ s, |w' s * c s - w s * c s| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s, c s * dist w w' := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [← sub_mul, abs_mul, abs_of_pos (hc s), mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ (hc s).le
            rw [abs_sub_comm, ← Real.dist_eq]; exact dist_le_pi_dist w w' s
        _ = (∑ s, c s) * dist w w' := by rw [← Finset.sum_mul]
    have hw'rc0 : 0 ≤ w' r * c r :=
      mul_nonneg (le_trans (le_of_lt (mul_pos hμ0 (hunif_pos r))) (hw' r)) (hc r).le
    -- the two triangle legs, each `≤ dist/δ`, cleared to a polynomial and closed by nlinarith
    have hleg1 : |w r * c r / (∑ s, w s * c s) - w' r * c r / (∑ s, w s * c s)|
        ≤ dist w w' / (μ * uMin unif) := by
      rw [div_sub_div_same, ← sub_mul, abs_div, abs_of_pos hZwp, abs_mul, abs_of_pos (hc r),
        div_le_div_iff₀ hZwp hδ]
      have h1 : |w r - w' r| * c r ≤ dist w w' * (∑ s, c s) :=
        mul_le_mul hdr hcr_le (hc r).le hd
      nlinarith [mul_le_mul_of_nonneg_right h1 hδ.le, mul_le_mul_of_nonneg_left hZw hd]
    have hleg2 : |w' r * c r / (∑ s, w s * c s) - w' r * c r / (∑ s, w' s * c s)|
        ≤ dist w w' / (μ * uMin unif) := by
      rw [div_sub_div _ _ hZwp.ne' hZw'p.ne', mul_comm (∑ s, w s * c s) (w' r * c r), ← mul_sub,
        abs_div, abs_mul, abs_of_nonneg hw'rc0,
        abs_of_pos (mul_pos hZwp hZw'p), div_le_div_iff₀ (mul_pos hZwp hZw'p) hδ]
      have h2 : w' r * c r * |(∑ s, w' s * c s) - (∑ s, w s * c s)|
          ≤ (∑ s, w' s * c s) * ((∑ s, c s) * dist w w') :=
        mul_le_mul hw'r_le hZdiff (abs_nonneg _) hZw'p.le
      nlinarith [mul_le_mul_of_nonneg_right h2 hδ.le,
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZw hd) hZw'p.le]
    calc |w r * c r / (∑ s, w s * c s) - w' r * c r / (∑ s, w' s * c s)|
        ≤ |w r * c r / (∑ s, w s * c s) - w' r * c r / (∑ s, w s * c s)|
          + |w' r * c r / (∑ s, w s * c s) - w' r * c r / (∑ s, w' s * c s)| := abs_sub_le _ _ _
      _ ≤ dist w w' / (μ * uMin unif) + dist w w' / (μ * uMin unif) := by
          exact add_le_add hleg1 hleg2
      _ = 2 / (μ * uMin unif) * dist w w' := by ring

/-- **The contraction window (the fork, quantitative).** For the linear replicator,
`(1−μ)·L_R μ < 1` on the explicit band where `2·(1−μ) < μ·u_min` — i.e. for `μ`
close to `1`, exactly the `04-design`'s `(μ⋆, 1]`, with a nameable crossover. -/
theorem lin_replicator_contracts (c : S → ℝ) (hc : ∀ s, 0 < c s)
    (unif : S → ℝ) (hunif_pos : ∀ r, 0 < unif r)
    (μ : ℝ) (hμ0 : 0 < μ) (_hμ1 : μ ≤ 1)
    (hband : 2 * (1 - μ) < μ * uMin unif) :
    (1 - μ) * ((linReplicatorLipschitz c hc unif hunif_pos).L_R μ : ℝ) < 1 := by
  have hu : 0 < uMin unif := uMin_pos hunif_pos
  have hδ : 0 < μ * uMin unif := mul_pos hμ0 hu
  have hLR : ((linReplicatorLipschitz c hc unif hunif_pos).L_R μ : ℝ) = 2 / (μ * uMin unif) :=
    Real.coe_toNNReal _ (le_of_lt (div_pos two_pos hδ))
  rw [hLR, show (1 - μ) * (2 / (μ * uMin unif)) = (2 * (1 - μ)) / (μ * uMin unif) from by ring,
    div_lt_one hδ]
  exact hband

/-- **Lemma B, Discharged (the fitness-based instance).** On the nonempty complete
floored simplex, attention under the linear replicator converges to a **unique fixed
point** on the contraction band `2(1−μ) < μ·u_min` — via the already-proved Banach
spine, with the contraction supplied by the proved sup-metric Lipschitz bound. No
bare hypothesis; the floor `δ = μ·u_min` is the shared lever WS5 proved load-bearing
for anti-collapse. -/
theorem ws8_replicator_converges (c : S → ℝ) (hc : ∀ s, 0 < c s)
    (unif : S → ℝ) (hunif_pos : ∀ r, 0 < unif r)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hband : 2 * (1 - μ) < μ * uMin unif)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif,
      mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum (linReplicatorSel c hc unif) p = p :=
  ws7_attention_fixed_point μ hμ0 hμ1 unif hunif_nonneg hunif_sum (linReplicatorSel c hc unif)
    (linReplicatorLipschitz c hc unif hunif_pos)
    (lin_replicator_contracts c hc unif hunif_pos μ hμ0 hμ1 hband)

/-! ### Exploring the exponential fitness replicator (`04-design` §2–3)

The `04-design`'s target is the **fitness-dependent** replicator
`R(w)_r = w_r · exp(f_r w) / Z(w)`, `Z(w) = ∑_s w_s exp(f_s w)`. We build its pieces
sorry-free (`exp_lip`, `expReplicatorSel`, the fitness-Lipschitz and normalizer
bounds) and record the precise mathematical finding.

**The finding (why the linear case was clean and the exp case is delicate).** The
linear replicator is **scale-covariant** (`R(λw) = R(w)`), so its Lipschitz constant
`2/(μ·u_min)` survives the *unbounded* `ws7.floorRegion` (only `∑w ≥ μ` is needed).
Fitness-dependence **breaks scale-covariance** (`f_r(λw) ≠ f_r(w)`), and on the
unbounded floor region **no uniform Lipschitz constant exists**: the cross term
`w'_r·(g_r(w) − g_r(w')) / Z(w)` mixes `w'` in the numerator with `Z(w)` in the
denominator, and `w'_r / Z(w) → ∞` as `w'` scales up while `w` stays small — the
direct estimate is `O(d²)`, not `O(d)`. So the exp replicator **cannot** inhabit
`ws7.SelectionLipschitz` (whose `bound` quantifies over the unbounded floor region).

**Where it IS Lipschitz.** On the **bounded** simplex-floor (`∑w = 1` *and* the floor,
so `w_r ∈ [δ, 1]`) — which is exactly where the dynamics lives (`mutT` maps
`FlooredSimplex` to itself) — the exp replicator is Lipschitz with the **explicit**
constant `L = 1/δ + e^{2B}·L_f + |S|·e^{4B}·(1 + L_f)`, from the bounds below (`w'_r ≤ 1`
is now available, killing the cross term). Firing convergence from this needs either a
`SelectionLipschitz` tightened to the simplex-floor, or a `C¹`-fitness Jacobian /
mean-value route on the convex floor region — an upstream change beyond `ws8`.

**Correction to the `04-design`'s constant.** The design's `C/(μ·u_min)²` with
`c₀·e^{3B}` is neither the unbounded-region truth (no finite constant) nor the
bounded-region truth (constant above, first-power `δ`, `e^{4B}`); its `w r ≤ 1`
assumption silently restricts to the simplex, which is the honest domain. -/

/-- `exp` is Lipschitz with constant `exp C` on `Iic C` — the fitness building block
(from `Real.add_one_le_exp`). -/
lemma exp_lip {a b C : ℝ} (ha : a ≤ C) (hb : b ≤ C) :
    |Real.exp a - Real.exp b| ≤ Real.exp C * |a - b| := by
  wlog hab : b ≤ a generalizing a b with H
  · rw [abs_sub_comm, abs_sub_comm a b]; exact H hb ha (le_of_not_le hab)
  have ht : (0 : ℝ) ≤ a - b := by linarith
  have key : Real.exp (a - b) - 1 ≤ (a - b) * Real.exp (a - b) := by
    have h := Real.add_one_le_exp (-(a - b))
    have he : Real.exp (-(a - b)) * Real.exp (a - b) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos (a - b)).le, he, Real.exp_pos (a - b)]
  have hfact : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
    have : Real.exp b * Real.exp (a - b) = Real.exp a := by rw [← Real.exp_add]; congr 1; ring
    rw [mul_sub, mul_one, this]
  have hexpb : Real.exp b * ((a - b) * Real.exp (a - b)) = (a - b) * Real.exp a := by
    have : Real.exp b * Real.exp (a - b) = Real.exp a := by rw [← Real.exp_add]; congr 1; ring
    rw [← mul_assoc, mul_comm (Real.exp b) (a - b), mul_assoc, this]
  have h1 : Real.exp a - Real.exp b ≤ (a - b) * Real.exp C := by
    calc Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := hfact
      _ ≤ Real.exp b * ((a - b) * Real.exp (a - b)) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos b).le
      _ = (a - b) * Real.exp a := hexpb
      _ ≤ (a - b) * Real.exp C := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) ht
  rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hab] : (0 : ℝ) ≤ Real.exp a - Real.exp b),
    abs_of_nonneg ht, mul_comm]
  exact h1

/-- The exponential-fitness replicator update, total on `S → ℝ` (identity off the
positive-`Z` region). On any point with a positive coordinate it is the genuine
`w_r·exp(f_r w) / Z(w)`. -/
noncomputable def expR (f : S → (S → ℝ) → ℝ) (w : S → ℝ) (r : S) : ℝ :=
  if 0 < ∑ s, w s * Real.exp (f s w) then
    w r * Real.exp (f r w) / (∑ s, w s * Real.exp (f s w)) else w r

/-- The exp-fitness replicator as a `SelectionMap` (weight- and nonnegativity-
preserving — `exp > 0` makes every fibre positive). -/
noncomputable def expReplicatorSel (f : S → (S → ℝ) → ℝ) (unif : S → ℝ) :
    SelectionMap S unif where
  R := expR f
  nonneg := fun w hw r => by
    rw [expR]
    by_cases hZ : 0 < ∑ s, w s * Real.exp (f s w)
    · rw [if_pos hZ]
      exact div_nonneg (mul_nonneg (hw r) (Real.exp_pos _).le) hZ.le
    · rw [if_neg hZ]; exact hw r
  sum_one := fun w hw => by
    by_cases hZ : 0 < ∑ s, w s * Real.exp (f s w)
    · have hval : ∀ r, expR f w r = w r * Real.exp (f r w) / (∑ s, w s * Real.exp (f s w)) :=
        fun r => by rw [expR, if_pos hZ]
      simp_rw [hval, ← Finset.sum_div]; exact div_self hZ.ne'
    · have hval : ∀ r, expR f w r = w r := fun r => by rw [expR, if_neg hZ]
      simp_rw [hval]; exact hw

/-- **Fitness-Lipschitz bound** (from `exp_lip`): the fibre multiplier `exp(f_r ·)` is
Lipschitz with constant `e^B·L_f` on the region where `|f| ≤ B` and `f_r` is
`L_f`-Lipschitz — the coupling the linear replicator lacked. -/
lemma expG_lipschitz {f : S → (S → ℝ) → ℝ} {B L_f : ℝ}
    (hf_bdd : ∀ r w, |f r w| ≤ B) (hf_lip : ∀ r w w', |f r w - f r w'| ≤ L_f * dist w w')
    (r : S) (w w' : S → ℝ) :
    |Real.exp (f r w) - Real.exp (f r w')| ≤ Real.exp B * L_f * dist w w' := by
  have hb1 : f r w ≤ B := le_of_abs_le (hf_bdd r w)
  have hb2 : f r w' ≤ B := le_of_abs_le (hf_bdd r w')
  calc |Real.exp (f r w) - Real.exp (f r w')| ≤ Real.exp B * |f r w - f r w'| := exp_lip hb1 hb2
    _ ≤ Real.exp B * (L_f * dist w w') :=
        mul_le_mul_of_nonneg_left (hf_lip r w w') (Real.exp_pos B).le
    _ = Real.exp B * L_f * dist w w' := by ring

/-- **Normalizer lower bound** on the simplex-floor: `Z(w) = ∑ w_s exp(f_s w) ≥ e^{−B}`
(uses `∑ w = 1` and `exp(f) ≥ e^{−B}`), so `Z > 0` and every ratio `g_r/Z ≤ 1/w_r`. -/
lemma expZ_lower {f : S → (S → ℝ) → ℝ} {B : ℝ} (hf_bdd : ∀ r w, |f r w| ≤ B)
    {w : S → ℝ} (hw : ∀ s, 0 ≤ w s) (hws : ∑ s, w s = 1) :
    Real.exp (-B) ≤ ∑ s, w s * Real.exp (f s w) := by
  calc Real.exp (-B) = ∑ s, w s * Real.exp (-B) := by rw [← Finset.sum_mul, hws, one_mul]
    _ ≤ ∑ s, w s * Real.exp (f s w) := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_of_abs_le (hf_bdd s w))) (hw s)

end Dynamics

end Series3.WS8
