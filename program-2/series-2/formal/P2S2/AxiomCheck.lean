/-
`program-2/series-2/formal/P2S2/AxiomCheck.lean` — the axiom pass for Series 2.2.

Runs `#print axioms` over every payoff. Each reduces through the collapse engine, `rankLift` / `faceLift`, the
diagonal, and `decide` to Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S2.ws1
import P2S2.ws2
import P2S2.ws3
import P2S2.ws4
import P2S2.ws5

namespace P2S2

#print axioms ws1_other_is_locus
#print axioms ws2_other_distinguishes
#print axioms ws2_other_reader_wise
#print axioms ws2_other_non_recoverable
#print axioms ws3_four_readings
#print axioms ws3_facing_asymmetric
#print axioms ws3_facing_partial
#print axioms ws4_mutual_residue
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_reader_loadbearing
#print axioms ws5_audit_twoness_import
#print axioms ws5_audit_facing_asymmetric
#print axioms ws5_audit_residue_genuine
#print axioms ws5_audit_coherence_open
#print axioms ws5_audit_names_not_terms

end P2S2
