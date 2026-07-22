/-
`program-3/series-1/formal/P3S1/ws2.lean`

WS2 - The loss, counted. Program 3 Series 1 (3.1), the arrow.

The summary genuinely loses the microstate:

- `ws2_summary_lossy`: the one-edge pair — two distinct states, one summary;
- `ws2_fiber_multiple`: a named fiber with three distinct states in it (edge forward, edge back, both), so
  the loss is counted on a fiber, not asserted;
- `ws2_no_decoder`: no function recovers the microstate from the summary; the projection admits no section.

The witnesses are single states, decided individually; nothing here enumerates the state space.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1.ws1

namespace P3S1

open P3S0

set_option linter.unusedVariables false

/-- One directed edge, forward: `0` attends `1`. -/
def gFwd : G := fun w => if w = 0 then {1} else ∅

/-- One directed edge, back: `1` attends `0`. -/
def gBwd : G := fun w => if w = 1 then {0} else ∅

/-- The mutual edge: each attends the other. -/
def gMut : G := fun w => if w = 0 then {1} else if w = 1 then {0} else ∅

/-- The summary erases the direction: the two one-edge states are distinct but summarize identically. -/
theorem ws2_summary_lossy : gFwd ≠ gBwd ∧ summary gFwd = summary gBwd := by
  constructor
  · intro h
    have := congrFun h 0
    simp [gFwd, gBwd] at this
  · decide

/-- The fiber over the one-edge summary holds at least three distinct states: the forward edge, the back
edge, and the mutual edge. The loss is counted on a named fiber. -/
theorem ws2_fiber_multiple :
    gFwd ≠ gBwd ∧ gBwd ≠ gMut ∧ gFwd ≠ gMut
  ∧ summary gFwd = summary gBwd ∧ summary gBwd = summary gMut := by
  refine ⟨ws2_summary_lossy.1, ?_, ?_, ws2_summary_lossy.2, by decide⟩
  · decide
  · decide

/-- No function recovers the microstate from the summary: the projection admits no section. Whatever a
decoder returns on the one-edge summary, it cannot be both one-edge states at once. -/
theorem ws2_no_decoder : ¬ ∃ back : (Fin 3 → Fin 3 → Bool) → G, ∀ g, back (summary g) = g := by
  rintro ⟨back, hback⟩
  have h1 := hback gFwd
  have h2 := hback gBwd
  rw [ws2_summary_lossy.2] at h1
  exact ws2_summary_lossy.1 (h1.symm.trans h2)

end P3S1
