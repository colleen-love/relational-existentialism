/-
`program-3/series-2/formal/P3S2/AxiomCheck.lean`

The axiom pass for Program 3 Series 2 (3.2), the ledger. Axiom-clean means each headline rests on at most
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`, with no `sorry`, no custom axiom, and no
`native_decide`.
-/
import P3S2

namespace P3S2

#print axioms ws1_total_charge_zero
#print axioms ws2_region_flux
#print axioms ws2_region_interior
#print axioms ws2_region_exterior
#print axioms ws2_boundary_flux
#print axioms ws3_flow_preserves_capacity
#print axioms ws3_orbits_are_capacity
#print axioms ws4_creation_not_flow
#print axioms ws4_holonomy_not_conserved
#print axioms ws5_verdict_tied
#print axioms ws5_verdict_eq

end P3S2
