/-
`program-3/series-1/formal/P3S1/ws4.lean`

WS4 - The bridges: the summary is Program 2's symmetric relating, and what it erases is the charge.
Program 3 Series 1 (3.1), the arrow.

Two reuse bridges, entering by theorem:

- `ws4_summary_is_p2_sym`: the summary is exactly `P2S0.sym`, the symmetric relating Series 2.0 built and
  proved blind to the knowing-asymmetry. The coarse-graining is not a fresh gadget; it is the reading
  Program 2 already studied.
- `ws4_charge_erased`: the summary erases the charge — two states with one summary and different charges.
  The information the arrow's coarse-graining discards is exactly the quantity the ledger (Series 3.2)
  accounts.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1.ws2

namespace P3S1

open P3S0

set_option linter.unusedVariables false

/-- The summary is Program 2's symmetric relating: `summary g a b` holds exactly when `P2S0.sym g a b`
does. The reuse enters by theorem, not by prose. -/
theorem ws4_summary_is_p2_sym (g : G) (a b : Fin 3) :
    summary g a b = true ↔ P2S0.sym g a b := by
  simp [summary, P2S0.sym]

/-- The summary erases the charge: the one-edge pair has one summary and opposite charges at the source.
What the coarse-graining forgets is exactly the ledger's quantity. -/
theorem ws4_charge_erased :
    summary gFwd = summary gBwd ∧ charge gFwd 0 ≠ charge gBwd 0 := by
  refine ⟨ws2_summary_lossy.2, ?_⟩
  decide

end P3S1
