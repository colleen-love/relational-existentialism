/-
`program-3/series-1/formal/P3S1/AxiomCheck.lean`

The axiom pass for Program 3 Series 1 (3.1), the arrow. Axiom-clean means each headline rests on at most
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`, with no `sorry`, no custom axiom, and no
`native_decide`.
-/
import P3S1

namespace P3S1

#print axioms ws1_summary_symmetric
#print axioms ws1_state_count
#print axioms ws2_summary_lossy
#print axioms ws2_fiber_multiple
#print axioms ws2_no_decoder
#print axioms ws3_micro_loses_nothing
#print axioms ws3_observation_always_lossy
#print axioms ws3_macro_not_autonomous
#print axioms ws4_summary_is_p2_sym
#print axioms ws4_charge_erased
#print axioms ws5_verdict_tied
#print axioms ws5_verdict_eq

end P3S1
