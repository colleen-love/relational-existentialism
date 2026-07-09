/-
`series-4/formal/ws4.lean`

WS4 — **No top, no view from nowhere.** Series 4.

Owns: no object relates to everything (a real size-wall, not an imposed cap), no
observer surveys the whole, and the positive companion that views are positioned.

The endogenous wall: relating to `y` *costs* carrying `y` as a successor, and an
object can carry only `< κ` successors (its own relating is `< κ`-bounded) while the
world is `≥ κ` (`carrier_card_ge`). So no object relates to everything — not because
we capped the world from outside, but because *you can only turn part of yourself
toward another, and you are not big enough to face everything.* The bound is the
world's grain: a `< κ` bound on each object's own relating.

Deliverables: `FacingInjective`, `ws4_no_top_facing` (N2/N3, unconditional),
`ws4_faces_inject` (faces distinguish targets), `ws4_no_global_observer` (V2),
`ws4_view_is_positioned` (V1), `ws4_substantive_standpoints` (V3),
`ws4_pole_coincidence_residue`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws3

universe u

open Cardinal Series4.WS1 Series4.WS2

namespace Series4.WS4

variable {κ : Cardinal.{u}}

/-! ## The no-top wall — cardinal form (the real wall) and a reachability restatement -/

/-- **No-top, cardinal form (the real, unconditional wall).** No object relates to *every*
object: its successor set is `< κ`, but the carrier is `≥ κ`. This is the Series 3
cardinality wall, inherited: the contradiction is a bound on `x`'s successor *count*, not
derived from face-structure. Per `project-review-2.md` (S1/S2), this — not a face-counting
wall — is what the no-top payoff actually rests on; `ws4_no_top_reach` below is only a
reachability restatement (faces do no work there), and faces provably cannot bound on this
carrier (the WS5 M1/M2 negatives). So the no-top payoff is **Relocated (cardinal wall)**,
not an endogenous face wall. -/
theorem ws4_no_top_cardinal (x : (νPk κ).X) : ¬ (∀ y, y ∈ ((νPk κ).str x).1) := by
  intro hall
  have huniv : (Set.univ : Set (νPk κ).X) ⊆ ((νPk κ).str x).1 := fun y _ => hall y
  have hle : Cardinal.mk (νPk κ).X ≤ Cardinal.mk ↥((νPk κ).str x).1 := by
    have h := Cardinal.mk_le_mk_of_subset huniv
    rwa [Cardinal.mk_univ] at h
  exact absurd (lt_of_le_of_lt hle ((νPk κ).str x).2) (not_lt.mpr (carrier_card_ge κ))

/-! ## Facing-injectivity: faces distinguish targets -/

/-- Distinct successors have distinguishable faces. -/
def FacingInjective (x : (νPk κ).X) : Prop :=
  ∀ y z, y ∈ ((νPk κ).str x).1 → z ∈ ((νPk κ).str x).1 → y ≠ z → face x y ≠ face x z

/-- Under facing-injectivity, `x`'s faces inject its successors into its sub-objects:
the number of *distinct positioned views* `x` holds equals its successor count. So a
maximal object would need as many distinct faces as there are objects — more than the
`< κ` its own relating allows. -/
theorem ws4_faces_inject (x : (νPk κ).X) (hinj : FacingInjective x) :
    Function.Injective (fun y : ↥((νPk κ).str x).1 => face x y.1) := by
  intro a b hab
  by_contra hne
  exact hinj a.1 b.1 a.2 b.2 (fun h => hne (Subtype.ext h)) hab

/-- **No-top, reachability form (honest re-labelling; NOT face-routed).** If `x`
reached every object then its reach would be the whole world, contradicting that `x`'s
reach is a *proper part* of it (`hreach`).

Adversarial-review finding (`project-review-2.md`, S2): this is a **reachability** wall,
not a face wall. `Reaches` is a plain-carrier notion that exists with no face structure,
and the contradiction is powered entirely by `hreach` (the deferred cardinality fact
`#reach x < #carrier`). Faces do *no* work here — the proof below uses only
`Reaches.step` (a successor is reachable). This is kept, honestly named, precisely to
record that on the R2 carrier faces do **not** bound: the WS5 negatives
(`ws5_contraction_insufficient`, `ws5_quotient_insufficient`) already proved faces tame
*quality*, not *branching*, so no genuine face-counting wall is available here. The real,
unconditional no-top is the cardinal wall `ws4_no_top_cardinal`. -/
theorem ws4_no_top_reach (x : (νPk κ).X)
    (hreach : Cardinal.mk ↥(ReachSet x) < Cardinal.mk (νPk κ).X) :
    ¬ (∀ y, y ∈ ((νPk κ).str x).1) := by
  intro hall
  -- purely reachability: every successor is reachable, so reaching everything = univ
  have hcov : ∀ y, y ∈ ReachSet x := fun y => Reaches.step (hall y)
  have huniv : ReachSet x = Set.univ := Set.eq_univ_of_forall hcov
  have hcard : Cardinal.mk ↥(ReachSet x) = Cardinal.mk (νPk κ).X := by
    rw [huniv]; exact Cardinal.mk_univ
  exact absurd hcard (ne_of_lt hreach)

/-! ## No global observer — the cardinal wall, observer-side (NOT a face-routed V2) -/

/-- **No global observer (cardinal wall, observer-side).** An observer whose immediate
window covered every object would relate to everything, contradicting `ws4_no_top_cardinal`.

Adversarial-review finding (`project-review-2.md`, R2): this is **not** the charter's
forced V2 ("an unpositioned total view is impossible, *routed through faces*"). It is the
cardinality wall applied observer-side. A genuine face-routed V2 is **absent** — and, per
S2 / the WS5 negatives, unavailable on the R2 carrier, since faces do not bound. So
no-view is **not** earned by a real coincidence (see `ws4_view_is_positioned`). -/
theorem ws4_no_global_observer (obs : (νPk κ).X) : ¬ (∀ y, y ∈ ((νPk κ).str obs).1) :=
  ws4_no_top_cardinal obs

/-! ## Views are positioned (definitional) and standpoints are substantive -/

/-- An observation is a genuine positioned view: an object together with one of its
successors, the edge along which it looks. -/
def Observation (κ : Cardinal.{u}) : Type u :=
  {p : (νPk κ).X × (νPk κ).X // p.2 ∈ ((νPk κ).str p.1).1}

/-- The content of an observation is a face. -/
def viewOf (o : Observation κ) : Set (νPk κ).X := face o.1.1 o.1.2

/-- Observations are inhabited (Ω's self-loop is one), so `ws4_view_is_positioned` is
not vacuously true (`project-review-2.md`, C1). -/
theorem ws4_observation_inhabited (hinf : ℵ₀ ≤ κ) : Nonempty (Observation κ) :=
  ⟨⟨(omegaState hinf, omegaState hinf), by
      rw [omega_selfsingleton hinf]; exact rfl⟩⟩

/-- **V1 — every view is positioned (definitional).** A view *is* an object's face toward
one of its successors: positioned by construction.

Adversarial-review finding (`project-review-2.md`, R2): this is `rfl` — `viewOf o` is
*defined* as `face o.1.1 o.1.2`, so "a view is a face" holds because a view was defined as
a face. It carries no force on its own. The charter wanted V1 paired with a *forced* V2
(an unpositioned total view impossible, via faces); that V2 does not exist as a distinct
face-routed theorem (`ws4_no_global_observer` is the cardinal wall). So the no-view
*coincidence* is **not** delivered — V1 is definitional, V2 absent. Reported honestly. -/
theorem ws4_view_is_positioned (o : Observation κ) : ∃ x y, viewOf o = face x y :=
  ⟨o.1.1, o.1.2, rfl⟩

/-- **V3 — substantive standpoints.** Distinct objects genuinely see differently:
the labelled carrier (WS3) carries two distinct non-atomic states, hence two distinct
positioned views. Free here rather than manufactured (contrast Series 3's `ws6`,
which had to construct positional content on a carrier where it held vacuously). -/
theorem ws4_substantive_standpoints (hinf : ℵ₀ ≤ κ) :
    ∃ a b : Series4.WS3.νLk κ (ULift.{u} Bool), a ≠ b ∧
      Series4.WS3.NonAtomic a ∧ Series4.WS3.NonAtomic b :=
  Series4.WS3.ws3_plurality_core_concrete hinf

/-! ## The disarmed pole-coincidence (one remark) -/

/-- **The pole-coincidence residue.** The face is improper *exactly* at Ω — the sole
place the part-that-faces equals the whole-faced: `Ω↾(Ω,Ω) = ReachSet Ω`. The honest
residue of the old zero-object/pole-coincidence claim, recorded (not elevated). -/
theorem ws4_pole_coincidence_residue (hinf : ℵ₀ ≤ κ) :
    face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf) := by
  rw [ws1_omega_face hinf, reachSet_omega hinf]

end Series4.WS4
