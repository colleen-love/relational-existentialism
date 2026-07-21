/-
`program-2/series-7/formal/P2S7/AxiomCheck.lean` — the axiom pass for Series 2.7.

Runs `#print axioms` over every payoff. Each reduces through the recoverability / import test
(`ws1_atomless_bisim`, `ws4_recoverable_not_import`, `AttentionDistinguishes`, `rankM_sep_general`), the rank lift,
the P1 diagonal (`ws2_residue_free`), and `decide`/`rfl` to Mathlib's standard three (`propext`,
`Classical.choice`, `Quot.sound`) and no others.
-/
import P2S7.ws1
import P2S7.ws2
import P2S7.ws3
import P2S7.ws4
import P2S7.ws5

namespace P2S7

#print axioms ws1_rank_nontrivial
#print axioms rankM_sep_general
#print axioms ws2_tick_raises
#print axioms ws3_not_conserved
#print axioms ws3_change_is_source
#print axioms ws3_source_nonvacuous
#print axioms ws4_rise_is_internal
#print axioms ws4_no_lossless_tick
#print axioms ws4_no_conserved_side
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_not_conserved
#print axioms ws5_audit_no_conserved_side
#print axioms ws5_audit_no_global
#print axioms ws5_audit_arrow_genuine
#print axioms ws5_audit_source_is_diagonal
#print axioms ws5_audit_change_is_source
#print axioms ws5_audit_names_not_terms

end P2S7
