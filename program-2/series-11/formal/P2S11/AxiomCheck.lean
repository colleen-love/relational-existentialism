/-
`program-2/series-11/formal/P2S11/AxiomCheck.lean` — the axiom pass for Series 2.11.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl`/`norm_num`/`omega` over `Fin 3`
and `ℤ`, the parity of the imported holonomy `hol`, and the antisymmetry of the imported increment `incr`, to Mathlib's
standard three (`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S11.ws1
import P2S11.ws2
import P2S11.ws3
import P2S11.ws4
import P2S11.ws5

namespace P2S11

#print axioms ws1_amp_signed
#print axioms amp_values
#print axioms amp_sq
#print axioms ws2_amp_cancels
#print axioms ws2_amp_cancels_general
#print axioms ws3_destructive
#print axioms ws3_destructive_iff
#print axioms ws3_amp_earned
#print axioms ws4_interfering_reachable
#print axioms ws4_additive_reachable
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_earned
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_destructive
#print axioms ws5_audit_scope
#print axioms ws5_audit_names_not_terms

end P2S11
