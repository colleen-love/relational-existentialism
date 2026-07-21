/-
`program-2/series-10/formal/P2S10/AxiomCheck.lean` — the axiom pass for Series 2.10.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl` over `Fin 4` and `Finset (Fin 4)`
and the imported `P2S7.ws2_tick_raises` (itself standard-three), to Mathlib's standard three (`propext`,
`Classical.choice`, `Quot.sound`) and no others.
-/
import P2S10.ws1
import P2S10.ws2
import P2S10.ws3
import P2S10.ws4
import P2S10.ws5

namespace P2S10

#print axioms ws1_tick_moves
#print axioms ws2_tick_not_invertible
#print axioms ws3_section_not_measure_preserving
#print axioms ws3_core_criterion
#print axioms ws4_core_reachable
#print axioms ws4_no_core_built
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_no_smuggle
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_decode_not_measure_preserving
#print axioms ws5_audit_measure_is_built_rank
#print axioms ws5_audit_names_not_terms

end P2S10
