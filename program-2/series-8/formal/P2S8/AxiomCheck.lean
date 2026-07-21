/-
`program-2/series-8/formal/P2S8/AxiomCheck.lean` — the axiom pass for Series 2.8.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl`/`omega` over `Fin 3` and `ℤ`,
the antisymmetry of the directed increment `incr`, and the `Converges₂` bridge, to Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S8.ws1
import P2S8.ws2
import P2S8.ws3
import P2S8.ws4
import P2S8.ws5

namespace P2S8

#print axioms ws1_nontrivial
#print axioms ws2_pairwise_coherent
#print axioms ws2_reconciliation_nontrivial
#print axioms ws2_bridge_converges
#print axioms ws3_two_body_trivial
#print axioms ws3_holonomy_model_derived
#print axioms ws4_frustrated_reachable
#print axioms ws4_gluable_reachable
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_no_global
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_many_body
#print axioms ws5_audit_coherence_pervasive
#print axioms ws5_audit_names_not_terms

end P2S8
