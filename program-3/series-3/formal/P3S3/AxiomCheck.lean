/-
`program-3/series-3/formal/P3S3/AxiomCheck.lean`

The axiom pass for Program 3 Series 3 (3.3), the phase. Axiom-clean means each headline rests on at most
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`, with no `sorry`, no custom axiom, and no
`native_decide`.
-/
import P3S3

namespace P3S3

#print axioms ws1_run_append
#print axioms ws1_wind_append
#print axioms ws2_winding_path_dependent
#print axioms ws2_windings_both_parities
#print axioms ws3_sign_forced
#print axioms ws4_amp_canonical
#print axioms ws4_destructive_iff
#print axioms ws4_interference_on_histories
#print axioms ws4_exponent_not_forced
#print axioms ws5_verdict_tied
#print axioms ws5_verdict_eq

end P3S3
