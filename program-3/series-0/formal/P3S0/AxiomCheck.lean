/-
`program-3/series-0/formal/P3S0/AxiomCheck.lean`

The axiom pass for Program 3 Series 0 (3.0), THE FLOW. Each `#print axioms` line prints the axiom dependencies
of a headline theorem. Axiom-clean means each rests on at most Mathlib's standard `propext` /
`Classical.choice` / `Quot.sound`, with no `sorry`, no custom axiom, and no `native_decide`.
-/
import P3S0

namespace P3S0

#print axioms ws1_moves_reversible
#print axioms ws1_move_local
#print axioms ws2_capacity_conserved
#print axioms ws2_exchange_zero_sum
#print axioms ws2_charge_is_incr_sum
#print axioms ws3_wall_is_a_state
#print axioms ws3_wall_reachable
#print axioms ws4_flow_connects
#print axioms ws5_verdict_tied
#print axioms ws5_verdict_eq

end P3S0
