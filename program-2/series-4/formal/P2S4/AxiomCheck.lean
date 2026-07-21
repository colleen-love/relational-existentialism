/-
`program-2/series-4/formal/P2S4/AxiomCheck.lean` — the axiom pass for Series 2.4.

Runs `#print axioms` over every payoff. Each reduces through the collapse engine (`ws1_atomless_bisim`), the
rank-labelled lift (`rankLift`), the length-indexed reach (`reachIn`), and `decide` to Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S4.ws1
import P2S4.ws2
import P2S4.ws3
import P2S4.ws4
import P2S4.ws5

namespace P2S4

#print axioms ws1_lateral_extent
#print axioms ws1_peers_non_recoverable
#print axioms ws1_not_collapsed
#print axioms ws2_lateral_step_no_rank
#print axioms ws2_reify_no_lateral
#print axioms ws2_axes_independent
#print axioms ws3_lateral_is_import
#print axioms ws3_directed
#print axioms ws3_granular
#print axioms ws3_metric_grounded
#print axioms ws3_metric_source_relative
#print axioms ws4_reduced_reachable
#print axioms ws4_distinct_witnessed
#print axioms ws4_two_axes
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_no_absolute_frame
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_knot_is_independence
#print axioms ws5_audit_lateral_import
#print axioms ws5_audit_names_not_terms

end P2S4
