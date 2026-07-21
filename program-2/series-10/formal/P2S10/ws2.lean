/-
`program-2/series-10/formal/P2S10/ws2.lean`

WS2 - The full tick is not invertible (the irreversible headline). Program 2 Series 10 (2.10).

Imports `P2S10.ws1`. Proves the FULL tick is NOT a measure-preserving bijection, two independent ways: (i) it is NOT
injective — two distinct configurations `e0' ≠ e2` are identified (`tick e0' = tick e2 = e0`, the collapse engine's
in-sight identification), so not a bijection; (ii) it is NOT measure-preserving — it RAISES the built rank
(`mu (tick e0) = mu e0 + 1`), the content of `P2S7.ws2_tick_raises`. Either obstruction alone defeats invertibility.
This is the honest starting point (the top-level dynamics is one-way); WS3/WS4 ask whether a CORE escapes it.

Design docs: `program-2/series-10/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S10.ws1

universe u

namespace P2S10

open P2S7

set_option linter.unusedVariables false

/-- **THE FULL TICK IS NOT A MEASURE-PRESERVING BIJECTION (WS2).** (i) NOT injective: `e0' ≠ e2` yet
`tick e0' = tick e2 = e0` — the collapse identifies distinct configurations, so the tick is not a bijection. (ii) NOT
measure-preserving: `mu (tick e0) ≠ mu e0` — the tick RAISES the built rank (`mu (tick e0) = mu e0 + 1`), so it cannot
be run backward as it stands. Both obstructions hold; either alone suffices. -/
theorem ws2_tick_not_invertible :
    ¬ Function.Injective tick
  ∧ (∃ x : Cfg, mu (tick x) ≠ mu x)
  ∧ mu (tick e0) = mu e0 + 1 := by
  refine ⟨?_, ⟨e0, by decide⟩, by decide⟩
  intro h
  have : e0' = e2 := h (by decide)
  exact absurd this (by decide)

end P2S10
