/-
`series-03/formal/ws15.lean`

WS15 (`series-03/spec/ws15/02-design.md`): **constitutive attention.** Two deficits,
one workstream:

* **the self-model former (A1, A2).** The dynamics' output (an attention weight
  vector) is sent back *into the carrier* as a state: `selfModel u w θ` is the state
  whose unfolding is the `θ`-attended sub-support of `u`. It re-enters the carrier
  (`ws13.mkState`), is the object exactly when attention `θ`-covers the whole support
  (`ws15_selfModel_eq_iff`), is a strictly partial image when some successor is
  sub-threshold (`ws15_selfModel_ne`), and its view always misses a state
  (`ws15_selfModel_view_proper`).
* **the exact per-family landscape (A5, A6).** For the coordination replicator the
  fixed-point cubic *factors* (`ws15_coord_cubic_factor`, a `ring` identity), giving
  the exact count: a non-central fixed point exists iff `μ < 1/2`
  (`ws15_multistable_iff`) — the bifurcation threshold is precisely `1/2`, by
  root-counting rather than estimate. Below all bands, every orbit keeps its floor
  (`ws15_orbit_floor`).
* **structurally sourced fitness (A7).** Fitness read off the carrier's own
  out-degree is positive (`ws15_struct_fitness_pos`) — the exogenous parameter made
  endogenous.

Bundle `ws15_constitutive_attention`. Axiom-clean beyond Mathlib's standard three,
`sorry`-free.

Built on `ws10` (dynamics + `carrier_card_ge` + `SelfSupport`/`coordIndF`/`coordFix`)
and `ws13` (the state-former `mkState`).
-/
import ws10
import ws13

open Cardinal Series03.WS1 Series03.WS2 Series03.WS5 Series03.WS7 Series03.WS9
open Series03.WS10 Series03.WS13

namespace Series03.WS15

/-- The ratified carrier cardinal. -/
abbrev κ₀ : Cardinal.{0} := Cardinal.aleph0.{0}

/-! ## Block 1 — the coordination family: exact fixed-point count (A5; carrier-free) -/

/-- **A5 keystone.** The coordination fixed-point cubic factors exactly. -/
lemma ws15_coord_cubic_factor (μ x : ℝ) :
    2 * x ^ 3 - 3 * x ^ 2 + (1 + μ) * x - μ / 2 = (x - 1 / 2) * (2 * x ^ 2 - 2 * x + μ) := by
  ring

/-- The scalar fixed-point equation clears to the cubic. -/
lemma coordFix_iff_cubic {μ x : ℝ} :
    coordIndF μ x = x ↔ 2 * x ^ 3 - 3 * x ^ 2 + (1 + μ) * x - μ / 2 = 0 := by
  have hDne : (x ^ 2 + (1 - x) ^ 2) ≠ 0 := ne_of_gt (coordDen_pos x)
  rw [coordIndF, ← mul_div_assoc, div_add' _ _ _ hDne, div_eq_iff hDne]
  constructor <;> intro h <;> linear_combination -h

/-- **A5 (`≥ 1/2`).** For `μ ≥ 1/2` the center `1/2` is the only fixed point in the
unit interval. -/
theorem ws15_coord_unique_ge_half {μ : ℝ} (hμ : 1 / 2 ≤ μ) {x : ℝ}
    (hfix : coordIndF μ x = x) : x = 1 / 2 := by
  rw [coordFix_iff_cubic, ws15_coord_cubic_factor] at hfix
  rcases mul_eq_zero.mp hfix with h | h
  · linarith [sub_eq_zero.mp h]
  · nlinarith [sq_nonneg (x - 1 / 2), h]

/-- The positive square-root witness of the side roots. -/
noncomputable def sroot (μ : ℝ) : ℝ := Real.sqrt (1 - 2 * μ)

lemma sroot_sq {μ : ℝ} (hμ : μ ≤ 1 / 2) : sroot μ ^ 2 = 1 - 2 * μ := by
  rw [sroot, Real.sq_sqrt (by linarith)]

lemma sroot_pos {μ : ℝ} (hμ : μ < 1 / 2) : 0 < sroot μ :=
  Real.sqrt_pos.mpr (by linarith)

lemma sroot_lt_one {μ : ℝ} (hμ0 : 0 < μ) : sroot μ < 1 :=
  (Real.sqrt_lt' one_pos).mpr (by nlinarith)

/-- The two side roots `(1 ± √(1−2μ))/2`. -/
noncomputable def xPlus (μ : ℝ) : ℝ := (1 + sroot μ) / 2
noncomputable def xMinus (μ : ℝ) : ℝ := (1 - sroot μ) / 2

lemma xPlus_quad {μ : ℝ} (hμ : μ ≤ 1 / 2) : 2 * xPlus μ ^ 2 - 2 * xPlus μ + μ = 0 := by
  have hs := sroot_sq hμ; rw [xPlus]; linear_combination (1 / 2 : ℝ) * hs

lemma xMinus_quad {μ : ℝ} (hμ : μ ≤ 1 / 2) : 2 * xMinus μ ^ 2 - 2 * xMinus μ + μ = 0 := by
  have hs := sroot_sq hμ; rw [xMinus]; linear_combination (1 / 2 : ℝ) * hs

lemma xPlus_fix {μ : ℝ} (hμ : μ ≤ 1 / 2) : coordIndF μ (xPlus μ) = xPlus μ := by
  rw [coordFix_iff_cubic, ws15_coord_cubic_factor, xPlus_quad hμ, mul_zero]

lemma xMinus_fix {μ : ℝ} (hμ : μ ≤ 1 / 2) : coordIndF μ (xMinus μ) = xMinus μ := by
  rw [coordFix_iff_cubic, ws15_coord_cubic_factor, xMinus_quad hμ, mul_zero]

/-- **A5 (`< 1/2`).** For `0 < μ < 1/2` the coordination map has three distinct fixed
points in the unit interval — the center and the two side roots. -/
theorem ws15_multistable_below_half {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ < 1 / 2) :
    ∃ a b c : ℝ, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (a ∈ Set.Icc (0:ℝ) 1 ∧ coordIndF μ a = a) ∧
      (b ∈ Set.Icc (0:ℝ) 1 ∧ coordIndF μ b = b) ∧
      (c ∈ Set.Icc (0:ℝ) 1 ∧ coordIndF μ c = c) := by
  have hsp := sroot_pos hμ
  have hs1 := sroot_lt_one hμ0
  refine ⟨xMinus μ, 1 / 2, xPlus μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xMinus]; intro h; linarith
  · rw [xPlus]; intro h; linarith
  · rw [xMinus, xPlus]; intro h; linarith
  · exact ⟨⟨by rw [xMinus]; linarith, by rw [xMinus]; linarith⟩, xMinus_fix hμ.le⟩
  · exact ⟨⟨by norm_num, by norm_num⟩, coordIndF_center μ⟩
  · exact ⟨⟨by rw [xPlus]; linarith, by rw [xPlus]; linarith⟩, xPlus_fix hμ.le⟩

/-- **A5 (the iff).** A non-central fixed point exists in the unit interval iff
`μ < 1/2`: the bifurcation threshold is precisely `1/2`. -/
theorem ws15_multistable_iff {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x ∧ x ≠ 1 / 2) ↔ μ < 1 / 2 := by
  constructor
  · rintro ⟨x, _, hfix, hne⟩
    by_contra hμ
    exact hne (ws15_coord_unique_ge_half (not_lt.mp hμ) hfix)
  · intro hμ
    have hsp := sroot_pos hμ
    have hs1 := sroot_lt_one hμ0
    refine ⟨xMinus μ, ⟨by rw [xMinus]; linarith, by rw [xMinus]; linarith⟩,
      xMinus_fix hμ.le, ?_⟩
    rw [xMinus]; intro h; linarith

/-! ## Block 2 — orbit floor (A6; carrier-free) -/

/-- **A6.** Every iterate of the mutation step keeps every coordinate above its
floor — no trajectory collapses toward a vertex, at any `μ`. Immediate from the
`FlooredSimplex` invariant of the iterate. -/
theorem ws15_orbit_floor {S : Type} [Fintype S] (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : S → ℝ) (hn : ∀ r, 0 ≤ unif r) (hs : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (w : FlooredSimplex S μ unif) (n : ℕ) (r : S) :
    μ * unif r ≤ ((mutT μ hμ0.le hμ1 unif hn hs sel)^[n] w).1 r :=
  (((mutT μ hμ0.le hμ1 unif hn hs sel)^[n] w).2.1) r

/-! ## Block 3 — the self-model former (A1, A2; carrier) -/

variable (u : (νPk κ₀).X) {μ : ℝ} {unif : SelfSupport κ₀ u → ℝ}

/-- The `θ`-attended sub-support of `u`, as a set of carrier states. -/
def attended (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) : Set (νPk κ₀).X :=
  Subtype.val '' {r : SelfSupport κ₀ u | θ ≤ w.1 r}

lemma attended_subset (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    attended u w θ ⊆ ((νPk κ₀).str u).1 := by
  rintro _ ⟨r, _, rfl⟩; exact r.2

lemma attended_small (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    Cardinal.mk ↥(attended u w θ) < κ₀ :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (attended_subset u w θ)) ((νPk κ₀).str u).2

/-- **A1.** The self-model of `u` under attention `w` and threshold `θ`: the state
whose unfolding is the `θ`-attended sub-support. The dynamics' output re-enters the
carrier as a state. -/
noncomputable def selfModel (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    (νPk κ₀).X :=
  mkState ⟨attended u w θ, attended_small u w θ⟩

@[simp] lemma str_selfModel (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    ((νPk κ₀).str (selfModel u w θ)).1 = attended u w θ := by
  simp only [selfModel, str_mkState]

/-- **A1.** The self-model *is* the object exactly when attention `θ`-covers the
whole support. -/
theorem ws15_selfModel_eq_iff (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    selfModel u w θ = u ↔ attended u w θ = ((νPk κ₀).str u).1 := by
  constructor
  · intro h
    have h2 : ((νPk κ₀).str (selfModel u w θ)).1 = ((νPk κ₀).str u).1 := by rw [h]
    rwa [str_selfModel] at h2
  · intro h
    have hpk : (⟨attended u w θ, attended_small u w θ⟩ : PkObj κ₀ (νPk κ₀).X)
        = (νPk κ₀).str u := Subtype.ext h
    calc selfModel u w θ = mkState ⟨attended u w θ, attended_small u w θ⟩ := rfl
      _ = mkState ((νPk κ₀).str u) := by rw [hpk]
      _ = u := mkState_str u

/-- **A1.** A single sub-threshold successor makes the self-model a strictly
different state. -/
theorem ws15_selfModel_ne (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ)
    (r : SelfSupport κ₀ u) (hr : w.1 r < θ) : selfModel u w θ ≠ u := by
  rw [Ne, ws15_selfModel_eq_iff]
  intro h
  have hmem : (r : (νPk κ₀).X) ∈ attended u w θ := by rw [h]; exact r.2
  obtain ⟨r', hr', hval⟩ := hmem
  have hrr : r' = r := Subtype.ext hval
  rw [hrr] at hr'
  exact absurd hr' (not_le.mpr hr)

/-- **A2.** The self-model's view always misses a state (its unfolding is finite,
the carrier is infinite). -/
theorem ws15_selfModel_view_proper (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    ∃ v, v ∉ ((νPk κ₀).str (selfModel u w θ)).1 := by
  by_contra h
  push_neg at h
  have huniv : ((νPk κ₀).str (selfModel u w θ)).1 = Set.univ := Set.eq_univ_of_forall h
  have h1 : Cardinal.mk (νPk κ₀).X ≤ Cardinal.mk ↥(((νPk κ₀).str (selfModel u w θ)).1) := by
    rw [huniv]; exact le_of_eq Cardinal.mk_univ.symm
  have h2 : Cardinal.mk ↥(((νPk κ₀).str (selfModel u w θ)).1) < κ₀ :=
    ((νPk κ₀).str (selfModel u w θ)).2
  exact absurd (lt_of_le_of_lt h1 h2) (not_lt.mpr (carrier_card_ge κ₀))

/-! ## Block 4 — structurally sourced fitness (A7; carrier) -/

/-- **A7.** Fitness read off the carrier's own structure: out-degree plus one. -/
noncomputable def structFitness (u : (νPk κ₀).X) : SelfSupport κ₀ u → ℝ :=
  fun r => (Fintype.card ↥((νPk κ₀).str r.val).1 : ℝ) + 1

theorem ws15_struct_fitness_pos (u : (νPk κ₀).X) (r : SelfSupport κ₀ u) :
    0 < structFitness u r := by
  rw [structFitness]; positivity

/-! ## Block 5 — the bundle -/

/-- The WS15 constitutive-attention deliverable. -/
structure WS15Bundle where
  selfModel_eq_iff : ∀ (u : (νPk κ₀).X) {μ : ℝ} {unif : SelfSupport κ₀ u → ℝ}
    (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ),
    selfModel u w θ = u ↔ attended u w θ = ((νPk κ₀).str u).1
  view_proper : ∀ (u : (νPk κ₀).X) {μ : ℝ} {unif : SelfSupport κ₀ u → ℝ}
    (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ),
    ∃ v, v ∉ ((νPk κ₀).str (selfModel u w θ)).1
  coord_iff : ∀ {μ : ℝ}, 0 < μ → μ ≤ 1 →
    ((∃ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x ∧ x ≠ 1 / 2) ↔ μ < 1 / 2)

/-- **The WS15 deliverable.** -/
theorem ws15_constitutive_attention : WS15Bundle where
  selfModel_eq_iff := ws15_selfModel_eq_iff
  view_proper := ws15_selfModel_view_proper
  coord_iff := fun hμ0 hμ1 => ws15_multistable_iff hμ0 hμ1

end Series03.WS15
