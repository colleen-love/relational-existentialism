/-
`program-2/series-5/formal/P2S5/AxiomCheck.lean` — the axiom pass for Series 2.5.

Runs `#print axioms` over every payoff. Each reduces through the P1 diagonal (`ws1_no_self_total_hold`,
`ws2_residue_distinct`, `ws1_insp_not_surjective`), the reification section (`FinReify`), the rank spine
(`transgen_rank_lt`, `causation_acyclic`, `loop_forces_selfloop`), and `decide` to Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S5.ws1
import P2S5.ws2
import P2S5.ws3
import P2S5.ws4
import P2S5.ws5

namespace P2S5

#print axioms ws1_no_pole_below
#print axioms ws1_no_pole_above
#print axioms ws1_reify_nonvacuous
#print axioms ws1_fold
#print axioms ws1_no_total_count
#print axioms ws2_relating_cycles
#print axioms transgen_rank_lt
#print axioms causation_acyclic
#print axioms ws3_causal_rank_lift
#print axioms ws3_causation_acyclic
#print axioms ws2_cycle_not_causal
#print axioms loop_forces_selfloop
#print axioms ws4_loop_only_at_fold
#print axioms ws4_no_fold_on_tower
#print axioms ws4_looped_reachable
#print axioms ws4_fold_no_rank
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_no_absolute_frame
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_knot_is_coexistence
#print axioms ws5_audit_fold_is_diagonal
#print axioms ws5_audit_names_not_terms

end P2S5
