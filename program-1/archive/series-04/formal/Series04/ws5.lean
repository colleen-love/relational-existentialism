/-
`series-04/formal/ws5.lean`

WS5 — **The self-bounding of the world.** Series 04. The "grain, not wall" thesis.

Can the world be set-sized because faces are parts of sources, rather than because a
size was imposed? WS5 adjudicates the three mechanisms of charter §3.2 and reports,
per the pre-registered outcomes:

* **M1 / M2 (sharp negatives).** Contraction alone does not free the bound — the
  carrier is still `≥ κ` (`ws5_contraction_insufficient`); quotient-by-same-face does
  not collapse plurality — distinct states survive (`ws5_quotient_insufficient`). So
  faces tame *quality*, not *branching* or *state-count*.
* **M3 (the real mechanism), the Impossibility.** Making the world groundless
  *everywhere* forces it to a single point (`ws5_global_groundless_collapses`, from
  `ws2_collapse`): global atomlessness is incompatible with plurality. So the bound
  **cannot** be freed from fiat *globally* while keeping plurality — a sharp negative
  directly answering the charter's central question at the global scale.
* **M3, the Partial positive.** On the self-loop spine the endogenous profile *does*
  hold: Ω is groundless and improper-faced (`ws5_omega_endogenous_point`), witnessing
  a `GroundlessDiagonal` region (`omegaGroundlessDiagonal`). The bound is endogenous
  on the spine; extending it to carry plurality is the named residue.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series04.ws4

universe u

open Cardinal Series04.WS1 Series04.WS2

namespace Series04.WS5

variable {κ : Cardinal.{u}}

/-! ## The M1 / M2 negatives -/

/-- **M1 (sharp negative).** Contraction does not free the bound: faces constrain the
*decoration* of edges, not their breadth, so the carrier is still `≥ κ`. Faces alone
cannot make the world set-sized without a bound — they tame quality, not branching. -/
theorem ws5_contraction_insufficient : κ ≤ Cardinal.mk (νPk κ).X := carrier_card_ge κ

/-- **M2 (sharp negative).** Quotient-by-same-face does not collapse the world:
distinct states survive same-face identification (WS3's plurality). The quotient tames
edge-redundancy, not state-proliferation. -/
theorem ws5_quotient_insufficient (hinf : ℵ₀ ≤ κ) :
    ∃ a b : Series04.WS3.νLk κ (ULift.{u} Bool), a ≠ b := by
  obtain ⟨a, b, hab, _, _⟩ := Series04.WS3.ws3_plurality_core_concrete hinf
  exact ⟨a, b, hab⟩

/-! ## M3 — the impossibility: global groundlessness collapses the world -/

/-- **The M3 Impossibility (the crux).** If the world were groundless *everywhere*
(every state hereditarily nonempty — no atom anywhere), it would collapse to a single
point, by the Collapse Theorem. So global atomlessness and plurality are incompatible:
the bound that permits plurality **cannot** be globally converted into endogenous
groundlessness. This is the honest limit of the "grain, not wall" thesis at the global
scale — a sharp negative, counted as success. -/
theorem ws5_global_groundless_collapses (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X :=
  ⟨fun a b => ws2_collapse hinf a b (h a) (h b)⟩

/-! ## M3 — the partial positive: the loop-spine carries the endogenous profile -/

/-- Ω is groundless: it reaches only itself, whose successor set `{Ω}` is nonempty. -/
theorem ws5_omega_groundless (hinf : ℵ₀ ≤ κ) : HereditarilyNonempty (omegaState hinf) := by
  intro v hv
  have hveq : v = omegaState hinf := (reaches_omega hinf v).mp hv
  subst hveq
  rw [omega_selfsingleton hinf]
  exact Set.singleton_ne_empty _

/-- Ω's self-face is improper — it faces *all* of itself, `Ω↾(Ω,Ω) = ReachSet Ω`. On
the diagonal the "face shrinks" recursion has a fixed point, so groundlessness
survives there while the face-bound is carried by improperness, not a cap. -/
theorem ws5_omega_improper (hinf : ℵ₀ ≤ κ) :
    face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf) := by
  rw [ws1_omega_face hinf, reachSet_omega hinf]

/-- **The endogenous point (Partial positive).** Ω is a groundless point whose bound is
carried by its improper self-face rather than an external cap: the two descents decouple
on the diagonal (groundless in states, improper — hence non-shrinking — in quality). -/
theorem ws5_omega_endogenous_point (hinf : ℵ₀ ≤ κ) :
    HereditarilyNonempty (omegaState hinf)
  ∧ face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf) :=
  ⟨ws5_omega_groundless hinf, ws5_omega_improper hinf⟩

/-- A **groundless-diagonal region**: a sub-world on which faces are improper on the
diagonal and every point is groundless. The design's decoupling of the two descents,
packaged as a typed structure. -/
structure GroundlessDiagonal (κ : Cardinal.{u}) where
  region : (νPk κ).X → Prop
  improper_on : ∀ x, region x → face x x = ReachSet x
  groundless_on : ∀ x, region x → HereditarilyNonempty x
  inhabited : ∃ x, region x

/-- **`ws5_endogenous_bound` (conditional).** Given a groundless-diagonal region, it is
a genuinely groundless, improper-faced sub-world: its bound is the improper diagonal,
not an imposed cardinal cap. -/
theorem ws5_endogenous_bound (G : GroundlessDiagonal κ) :
    ∃ x, G.region x ∧ HereditarilyNonempty x ∧ face x x = ReachSet x := by
  obtain ⟨x, hx⟩ := G.inhabited
  exact ⟨x, hx, G.groundless_on x hx, G.improper_on x hx⟩

/-- **An exhibited witness** (not merely posited): the loop-spine `{Ω}` is a
groundless-diagonal region. The endogenous bound is realized on the spine. -/
noncomputable def omegaGroundlessDiagonal (hinf : ℵ₀ ≤ κ) : GroundlessDiagonal κ where
  region := fun x => x = omegaState hinf
  improper_on := fun x hx => by subst hx; exact ws5_omega_improper hinf
  groundless_on := fun x hx => by subst hx; exact ws5_omega_groundless hinf
  inhabited := ⟨omegaState hinf, rfl⟩

end Series04.WS5
