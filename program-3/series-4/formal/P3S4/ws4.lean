/-
`program-3/series-4/formal/P3S4/ws4.lean`

WS4 - The flux-curvature law. Program 3 Series 4 (3.4), the curve.

For every state and every applicable move, transporting attention toward a relatum lowers its charge by
exactly one and brings it within unit distance of the mover — and, when the relatum was not the mover,
the distance strictly contracts, from at least two to at most one (`ws4_flux_contracts`).

Scope, repaired at Program Review 3-1 (P3R1-S3). This is a per-event law linking two readings of one
attention event: the charge conjunct is exact degree bookkeeping, and the distance bound follows from the
metric's definition once the new edge exists — the two are coupled by common cause, not by one driving
the other. The strict contraction is the law's non-definitional content. No field equation is stated or
claimed, and no theorem gives distance change as a function of the charge distribution; `ws1` proves the
static version of such a law does not exist.

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

/-- The flux law: transporting attention toward a relatum lowers its charge by exactly one and brings it
within unit distance of the mover. For every state and every applicable move. A per-event law linking two
readings of one attention event; the charge conjunct is exact bookkeeping, the distance conjunct the
metric's definition once the edge exists (see the header's scope note, Program Review 3-1, P3R1-S3). -/
theorem ws4_flux_curves (x y z : Fin 3) (g : G) (hy : y ∈ g x) (hz : z ∉ g x) :
    charge (transport x y z g) z = charge g z - 1
  ∧ flowDist (transport x y z g) x z ≤ 1 := by
  constructor
  · unfold charge
    rw [inDeg_target g hy hz, ws2_capacity_conserved]
    push_cast
    ring
  · exact ws3_attention_is_proximity _ x z (transport_row_target hy hz)

/-- The one-step ball is the mover and its attended relata. -/
lemma mem_ball_one_iff (g : G) (x z : Fin 3) : z ∈ ball g 1 x ↔ z = x ∨ z ∈ g x := by
  show z ∈ insert x ((g x).biUnion (fun y => ball g 0 y)) ↔ _
  simp [ball, Finset.mem_insert, Finset.mem_biUnion]

/-- The strict contraction (the law's non-definitional content, stated at Program Review 3-1's direction,
P3R1-S3): when the relatum was neither attended nor the mover itself, its distance from the mover was at
least two before the move and is at most one after. Attention flux strictly contracts distance. -/
theorem ws4_flux_contracts (x y z : Fin 3) (g : G) (hy : y ∈ g x) (hz : z ∉ g x) (hzx : z ≠ x) :
    2 ≤ flowDist g x z ∧ flowDist (transport x y z g) x z ≤ 1 := by
  refine ⟨?_, (ws4_flux_curves x y z g hy hz).2⟩
  unfold flowDist
  split_ifs with h0 h1
  · exact absurd (Finset.mem_singleton.mp h0) hzx
  · rcases (mem_ball_one_iff g x z).mp h1 with h | h
    · exact absurd h hzx
    · exact absurd h hz
  · omega
  · omega

end P3S4
