/-
`program-2/series-3/formal/P2S3/AxiomCheck.lean` — the axiom pass for Series 2.3.

Runs `#print axioms` over every payoff. Each reduces through the collapse engine (`ws1_atomless_bisim`), the
labelled lift `valLift`, `faithful_converges_iff`, and `decide` to Mathlib's standard three (`propext`,
`Classical.choice`, `Quot.sound`) and no others.
-/
import P2S3.ws1
import P2S3.ws2
import P2S3.ws3
import P2S3.ws4
import P2S3.ws5

namespace P2S3

#print axioms faithful_converges_iff
#print axioms ws1_converges_typed
#print axioms ws1_two_sided_free
#print axioms ws2_converges_decided_in_sight
#print axioms ws2_insight_inhabited
#print axioms ws2_sight_is_uniform
#print axioms valLift_not_recoverable
#print axioms ws3_dissent_is_import
#print axioms ws4_insight_proper
#print axioms ws4_two_zone
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_no_evaluation
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_dissent_import
#print axioms ws5_audit_faces_are_readers

end P2S3
