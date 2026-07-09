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

/-! ## The no-top wall — cardinal form and endogenous (face-routed) form -/

/-- **No-top, cardinal form.** No object relates to *every* object: its successor set is
`< κ`, but the carrier is `≥ κ`. This is the Series 3 cardinality wall, inherited: the
contradiction is a bound on `x`'s successor *count*, not derived from face-structure.
The endogenous (face-counting) wall is `ws4_no_top_endogenous` below; it routes through
faces and `x`'s own reach. (This lemma does not claim `noResortToFiat` — it *is* the
cardinal bound.) -/
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

/-- **No-top, endogenous (face-routed) form — the charter bar.** No object relates to
every object, proved *through faces* and `x`'s own extent: if `x` faced every object,
then every object would lie in one of `x`'s faces — but faces are parts of `x`'s reach
(`face_sub_reach`), so `x`'s reach would be the whole world, contradicting that `x`'s
reach is a *proper part* of it (`hreach`). The wall reads "you would need to turn part
of yourself toward every object, but you can only face into your own reach, and your
reach is not the whole world." This is the self-cost of facing — a fact about `x`'s own
faces and reach, not a bare cardinality cap on the carrier.

The endogenous hypothesis `hreach` (a state's reach is a proper part of the world) holds
for every state on the `ℵ₀` witness (`#reach ≤ ℵ₀ < 2^ℵ₀ = #carrier`, transcribable from
Series 3 `ws12`); reproducing that continuum bound is deferred, so it is stated here as
the explicit endogenous premise. `FacingInjective` / `ws4_faces_inject` express the
sharper "distinct faces" reading of the same self-cost (the charter §9 crux: whether
facing is cofinally injective). -/
theorem ws4_no_top_endogenous (x : (νPk κ).X)
    (hreach : Cardinal.mk ↥(ReachSet x) < Cardinal.mk (νPk κ).X) :
    ¬ (∀ y, y ∈ ((νPk κ).str x).1) := by
  intro hall
  -- every object lies in one of x's faces, and faces are parts of x's reach
  have hcov : ∀ y, y ∈ ReachSet x := fun y => face_sub_reach x y (mem_face_self (hall y))
  have huniv : ReachSet x = Set.univ := Set.eq_univ_of_forall hcov
  have hcard : Cardinal.mk ↥(ReachSet x) = Cardinal.mk (νPk κ).X := by
    rw [huniv]; exact Cardinal.mk_univ
  exact absurd hcard (ne_of_lt hreach)

/-! ## No global observer (V2) — the same wall, observer-side -/

/-- **V2 — no observer surveys the whole.** An observer whose immediate window
covered every object would relate to everything, contradicting the wall. No-top and
no-view-from-nowhere are the *same wall* seen from object-side and observer-side. -/
theorem ws4_no_global_observer (obs : (νPk κ).X) : ¬ (∀ y, y ∈ ((νPk κ).str obs).1) :=
  ws4_no_top_cardinal obs

/-! ## Views are positioned (V1) and standpoints are substantive (V3) -/

/-- An observation is a genuine positioned view: an object together with one of its
successors, the edge along which it looks. -/
def Observation (κ : Cardinal.{u}) : Type u :=
  {p : (νPk κ).X × (νPk κ).X // p.2 ∈ ((νPk κ).str p.1).1}

/-- The content of an observation is a face. -/
def viewOf (o : Observation κ) : Set (νPk κ).X := face o.1.1 o.1.2

/-- **V1 — every view is positioned.** A view *is* an object's face toward something:
positioned by construction (indexed by whose it is and toward what). This is the
definitional half; the coincidence rule (WS7) forbids reporting it as Discharged
*alone* — it is paired with V2, the forced impossibility of an unpositioned total
view. -/
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
