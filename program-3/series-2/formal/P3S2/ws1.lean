/-
`program-3/series-2/formal/P3S2/ws1.lean`

WS1 - The closed ledger. Program 3 Series 2 (3.2), the ledger.

Imports `P3S1` at the series boundary (reaching `P3S0` transitively). This file defines the region ledger
and proves the world's total ledger closed:

- `regionCharge`, the sum of a region's members' charges;
- `transport_self`, the degenerate move is the identity (so the flux law's `y ≠ z` hypothesis excludes
  nothing substantive);
- `ws1_total_charge_zero`: the sum of all charges is zero in every state — every unit of attention given
  is a unit received, by double counting. Structural.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1

namespace P3S2

open P3S0 P3S1

set_option linter.unusedVariables false

/-- The region ledger: the sum of the region's members' charges. -/
def regionCharge (g : G) (r : Finset (Fin 3)) : ℤ := ∑ w ∈ r, charge g w

/-- The degenerate move is the identity: transporting between a target and itself does nothing. -/
lemma transport_self (x y : Fin 3) (g : G) : transport x y y g = g := by
  funext w
  by_cases hw : w = x
  · subst hw
    rw [transport_row, if_neg (fun h => h.2 h.1), if_neg (fun h => h.2 h.1)]
  · rw [transport_other x y y w hw]

/-- The world's total ledger is closed: the sum of all charges is zero in every state. Every unit of
attention given is a unit of attention received, so the out-degrees and in-degrees have the same total. -/
theorem ws1_total_charge_zero (g : G) : ∑ w : Fin 3, charge g w = 0 := by
  unfold charge
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have h : ∑ w : Fin 3, inDeg g w = ∑ w : Fin 3, (g w).card := by
    unfold inDeg
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast h.symm

end P3S2
