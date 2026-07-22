/-
`program-3/series-3/formal/P3S3/ws2.lean`

WS2 - The winding is path-dependent. Program 3 Series 3 (3.3), the phase.

Two co-terminal histories from one state with different windings: the one-move history that carries the
attention from `1` to `2` directly, and the two-move history that routes it through `0`. Both end at the
same state; their windings are `1` and `2`. The winding is not a function of the endpoints — the flow has
genuine holonomy, which is the necessary condition for interference to be non-trivial. Had the winding
been exact (a state function), the phase would collapse before it began; this is the series' pre-registered
`exact'` refutation, foreclosed by witness.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws1

namespace P3S3

open P3S0 P3S1 P3S2

set_option linter.unusedVariables false

/-- The direct history: one move, attention from `1` to `2`. -/
def hDirect : Hist := [(0, 1, 2)]

/-- The routed history: two moves, attention from `1` through `0` to `2`. -/
def hRouted : Hist := [(0, 1, 0), (0, 0, 2)]

/-- A longer routed history: three moves, out to `0`, back to `1`, then to `2`. Winding `3`. -/
def hLong : Hist := [(0, 1, 0), (0, 0, 1), (0, 1, 2)]

/-- The winding is path-dependent: the direct and routed histories are co-terminal from the one-edge
state, with windings `1` and `2`. Genuine holonomy: the phase reads the path, not the endpoints. -/
theorem ws2_winding_path_dependent :
    run hDirect gFwd = run hRouted gFwd
  ∧ wind hDirect gFwd = 1
  ∧ wind hRouted gFwd = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The long history is also co-terminal, with winding `3`: the windings realize both parities on
co-terminal histories, which WS4's interference needs. -/
theorem ws2_windings_both_parities :
    run hLong gFwd = run hDirect gFwd ∧ wind hLong gFwd = 3 := by
  refine ⟨by decide, by decide⟩

end P3S3
