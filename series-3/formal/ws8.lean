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

## Obligation C — convergence (deferred)

The design's own verdict: C is "the one obligation with no upstream lever that forces
the truth-value"; C4 (Brouwer/Schauder existence on the floored simplex) and C2
(softmax Lipschitz bound) are the analysis-heavy pieces, and the C1/C5 replicator
Jacobian fork is "the single open analytic node," explicitly quarantined. Consistent
with that, C is **not** formalized here (no sorry stands in for it); it remains the
quarantined analytic obligation, with the Banach scaffold already in `ws7`
(`ws7_attention_fixed_point`) ready to consume any contraction proof.
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

end Series3.WS8
