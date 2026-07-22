/-
`program-3/series-4/formal/P3S4/ws4.lean`

WS4 - The flux-curvature law. Program 3 Series 4 (3.4), the curve.

The heart of the capstone: for every state and every applicable move, transporting attention toward a
relatum lowers its charge by exactly one and brings it within unit distance of the mover. Grain flux and
metric change are two faces of the same event, coupled by an exact universal law: concentration of the
conserved quantity contracts distance. The shape of gravity, in the model's own key, as a theorem about
the dynamics.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S4.ws3

namespace P3S4

open P3S0 P3S1 P3S2 P3S3

set_option linter.unusedVariables false

/-- The moved row contains the new target. -/
lemma transport_row_target {x y z : Fin 3} {g : G} (hy : y ∈ g x) (hz : z ∉ g x) :
    z ∈ (transport x y z g) x := by
  rw [transport_row, if_pos ⟨hy, hz⟩]
  exact Finset.mem_insert_self z _

/-- The move raises the target's in-degree by exactly one: the moved row gains it, no other row changes. -/
lemma inDeg_target {x y z : Fin 3} (g : G) (hy : y ∈ g x) (hz : z ∉ g x) :
    inDeg (transport x y z g) z = inDeg g z + 1 := by
  unfold inDeg
  simp only [Finset.card_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hrow : z ∈ (transport x y z g) x := transport_row_target hy hz
  rw [if_pos hrow, if_neg hz]
  have hrest : (∑ u ∈ Finset.univ.erase x, if z ∈ (transport x y z g) u then 1 else 0)
      = ∑ u ∈ Finset.univ.erase x, if z ∈ g u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [transport_other x y z u (Finset.ne_of_mem_erase hu)]
  rw [hrest]
  omega

/-- The flux-curvature law: transporting attention toward a relatum lowers its charge by exactly one and
brings it within unit distance of the mover. For every state and every applicable move. Concentration of
the conserved quantity contracts distance — an exact coupling of the grain to the metric, as a law of the
dynamics. -/
theorem ws4_flux_curves (x y z : Fin 3) (g : G) (hy : y ∈ g x) (hz : z ∉ g x) :
    charge (transport x y z g) z = charge g z - 1
  ∧ flowDist (transport x y z g) x z ≤ 1 := by
  constructor
  · unfold charge
    rw [inDeg_target g hy hz, ws2_capacity_conserved]
    push_cast
    ring
  · exact ws3_attention_is_proximity _ x z (transport_row_target hy hz)

end P3S4
