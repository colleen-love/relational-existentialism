/-
`program-3/series-4/formal/P3S4/AxiomCheck.lean`

The axiom pass for Program 3 Series 4 (3.4), the curve. Axiom-clean means each headline rests on at most
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`, with no `sorry`, no custom axiom, and no
`native_decide`.
-/
import P3S4

namespace P3S4

#print axioms ws1_dist_self
#print axioms ws1_metric_reads_state
#print axioms ws1_grain_underdetermines
#print axioms ws2_metric_moves
#print axioms ws3_attention_is_proximity
#print axioms ws4_flux_curves
#print axioms ws4_flux_contracts
#print axioms ws5_verdict_tied
#print axioms ws5_verdict_eq

end P3S4
