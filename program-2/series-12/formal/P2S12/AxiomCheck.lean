/-
`program-2/series-12/formal/P2S12/AxiomCheck.lean` — the axiom pass for Series 2.12.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl`/`norm_num`/`simp` over `Fin 3`
and `ℤ`, the parity of the imported holonomy `hol`, the imported sign `amp` and its weights `combinedWeight` /
`partsWeight`, and the antisymmetry of the imported increment `incr`, to Mathlib's standard three (`propext`,
`Classical.choice`, `Quot.sound`) and no others.
-/
import P2S12.ws1
import P2S12.ws2
import P2S12.ws3
import P2S12.ws4
import P2S12.ws5

namespace P2S12

#print axioms ws1_outcomes_nontrivial
#print axioms ws1_measure_nontrivial
#print axioms ws2_sq_nonneg
#print axioms ws2_not_classical
#print axioms ws3_classical_fails
#print axioms ws3_sq_consistent
#print axioms ws3_sq_forced
#print axioms ws3_sq_earned
#print axioms ws4_squared_reachable
#print axioms ws4_deterministic_reachable
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_earned
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_nonclassical
#print axioms ws5_audit_scope
#print axioms ws5_audit_names_not_terms

end P2S12
