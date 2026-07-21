/-
`program-2/series-9/formal/P2S9/AxiomCheck.lean` — the axiom pass for Series 2.9.

Runs `#print axioms` over every payoff. Each reduces through concrete `decide`/`rfl` over `Fin 5` and `ℕ`, the
`Finset.sup` / `Finset.le_sup` / `Finset.sup_mono` bound facts, and `Finset.mem_filter`, to Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`) and no others.
-/
import P2S9.ws1
import P2S9.ws2
import P2S9.ws3
import P2S9.ws4
import P2S9.ws5

namespace P2S9

#print axioms ws1_rate_bounded
#print axioms ws1_rate_earned_from_knows
#print axioms ws1_rate_monotone
#print axioms ws1_rate_tracks_attention
#print axioms ws2_cone
#print axioms ws2_cone_nontrivial
#print axioms ws3_rate_is_content
#print axioms ws3_earned_from_attention
#print axioms ws4_cone_reachable
#print axioms ws4_nocone_reachable
#print axioms ws4_nocone_trivial
#print axioms ws5_verdict_eq
#print axioms ws5_verdict_discriminates
#print axioms ws5_flags_justified
#print axioms ws5_audit_rate_earned
#print axioms ws5_audit_fork_genuine
#print axioms ws5_audit_rate_not_order
#print axioms ws5_audit_cone_nontrivial
#print axioms ws5_audit_names_not_terms
#print axioms ws5_the_verdict

end P2S9
