/-
`program-2/series-6/formal/P2S6/AxiomCheck.lean` — the axiom pass for Series 2.6.

Runs `#print axioms` over every payoff. Each reduces through the recoverability / import test
(`ws1_atomless_bisim`, `ws4_recoverable_not_import`, `AttentionDistinguishes`), the rank lift, the transcribed
tick machinery and Series 2.1's linearization import, and `decide`/`rfl` to Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S6.ws1
import P2S6.ws2
import P2S6.ws3
import P2S6.ws4
import P2S6.ws5

namespace P2S6

#print axioms ws1_succ_witnessed
#print axioms ws1_strict_fails
#print axioms plainOf_rankLift_gen
#print axioms const_first_recoverable
#print axioms distinguishes_not_recoverable
#print axioms ws2_cont_recoverable
#print axioms ws2_cont_is_import
#print axioms ws2_weaker_than_strict
#print axioms ws3_line_is_import
#print axioms ws3_partial_order_endogenous
#print axioms ws3_line_not_scalar
#print axioms ws4_woven_reachable
#print axioms ws4_severed_reachable
#print axioms ws4_carrier_relative
#print axioms ws4_cessation_relative
#print axioms ws4_conservative_reachable
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_carrier_relative_verdict
#print axioms ws5_audit_no_absolute
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_knot_not_strict
#print axioms ws5_audit_line_is_import
#print axioms ws5_audit_names_not_terms

end P2S6
