/-
`program-3/series-1/formal/P3S1/ws1.lean`

WS1 - The two levels: the summary and the scale of the micro world. Program 3 Series 1 (3.1), the arrow.

Imports `P3S0` (the flow: the state space `G`, the transport moves, their reversibility, the charge). This
file adds the coarse-graining and the two facts that frame the series:

- `summary`, the direction-erasing summary of a state: whether two relata attend each other in either
  direction, forgetting which;
- `ws1_summary_symmetric`: the summary is direction-blind, for every state;
- `ws1_state_count`: the micro world has 512 states, computed structurally, so the coming loss has a scale.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0

namespace P3S1

open P3S0

set_option linter.unusedVariables false

/-- The direction-erasing summary of a state: `summary g a b` holds when `a` attends `b` or `b` attends
`a`, forgetting which. The coarse-graining of the series. -/
def summary (g : G) : Fin 3 → Fin 3 → Bool := fun a b => decide (b ∈ g a) || decide (a ∈ g b)

/-- The summary is direction-blind: it reports the same value in both orders, for every state. What it
cannot report is exactly the direction of attention. -/
theorem ws1_summary_symmetric (g : G) (a b : Fin 3) : summary g a b = summary g b a := by
  simp only [summary]
  exact Bool.or_comm _ _

/-- The micro world has 512 states. Computed structurally from the shape of the state space, not by
enumeration; it gives the summary's loss its scale. -/
theorem ws1_state_count : Fintype.card G = 512 := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
  norm_num

end P3S1
