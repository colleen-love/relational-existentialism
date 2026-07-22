/-
`program-3/series-4/formal/P3S4/ws2.lean`

WS2 - The metric moves. Program 3 Series 4 (3.4), the curve.

A transport changes a distance: moving the only unit of attention away from a neighbour sends it from
distance one to the sentinel. The metric is dynamical — the precondition Series 2.13's static setting
could not offer.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S4.ws1

namespace P3S4

open P3S0 P3S1 P3S2 P3S3

set_option linter.unusedVariables false

/-- The metric moves under the flow: transporting `0`'s attention from `1` to `2` stretches the distance
to `1` from one to the sentinel, and contracts the distance to `2` from the sentinel to one. -/
theorem ws2_metric_moves :
    flowDist gFwd 0 1 = 1
  ∧ flowDist (transport 0 1 2 gFwd) 0 1 = 3
  ∧ flowDist gFwd 0 2 = 3
  ∧ flowDist (transport 0 1 2 gFwd) 0 2 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end P3S4
