/-
`program-2/series-13/formal/P2S13/AxiomCheck.lean` — the axiom pass for Series 2.13.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl`/`simp` over `Fin 4` and `ℕ` —
the fuel-computed path-length `pathDist` (a function of the adjacency), the grain `grainBump`, the imported distance
`adjDist` and the counterfactual foil `foilDist`, and the finite Bool computation of `verdict` — to Mathlib's standard
three (`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S13.ws1
import P2S13.ws2
import P2S13.ws3
import P2S13.ws4
import P2S13.ws5

namespace P2S13

#print axioms ws1_grain_and_metric_nontrivial
#print axioms ws2_metric_from_adjacency
#print axioms ws2_metric_reads_adjacency
#print axioms ws3_grain_test
#print axioms ws3_grain_test_witnessed
#print axioms ws3_no_by_hand_coupling
#print axioms ws4_inert_reachable
#print axioms ws4_gravitational_reachable
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_coupling_earned
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_metric_is_built
#print axioms ws5_audit_scope
#print axioms ws5_audit_names_not_terms
#print axioms ws5_the_verdict

end P2S13
