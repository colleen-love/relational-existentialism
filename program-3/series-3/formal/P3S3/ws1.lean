/-
`program-3/series-3/formal/P3S3/ws1.lean`

WS1 - Histories and their composition. Program 3 Series 3 (3.3), the phase.

Imports `P3S2` at the series boundary. Histories — lists of moves, run by folding transports — are the
first appearance of paths as objects in either program. The winding of a history is the accumulated step
sign along the evolving state: `+1` when a move transports forward, `-1` backward, `0` when it idles.

- `ws1_run_append`: histories compose;
- `ws1_wind_append`: the winding is a cocycle over composition — the winding of a composite is the first
  leg's winding plus the second leg's winding from where the first leg ended.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2

namespace P3S3

open P3S0 P3S1 P3S2

set_option linter.unusedVariables false

/-- A move: the triple fed to `transport`. -/
abbrev Move : Type := Fin 3 × Fin 3 × Fin 3

/-- A history: a list of moves. The first path object of the programs. -/
abbrev Hist : Type := List Move

/-- One step of a history. -/
def stepOf (m : Move) (g : G) : G := transport m.1 m.2.1 m.2.2 g

/-- The sign a move contributes at a state: `+1` transporting forward, `-1` back, `0` idling. -/
def stepSign (m : Move) (g : G) : ℤ :=
  if m.2.1 ∈ g m.1 ∧ m.2.2 ∉ g m.1 then 1
  else if m.2.2 ∈ g m.1 ∧ m.2.1 ∉ g m.1 then -1
  else 0

/-- Running a history: fold the moves through the state. -/
def run : Hist → G → G
  | [], g => g
  | m :: h, g => run h (stepOf m g)

/-- The winding of a history: the accumulated step sign along the evolving state. -/
def wind : Hist → G → ℤ
  | [], _ => 0
  | m :: h, g => stepSign m g + wind h (stepOf m g)

/-- Histories compose: running a concatenation is running the legs in turn. -/
theorem ws1_run_append (h1 h2 : Hist) (g : G) : run (h1 ++ h2) g = run h2 (run h1 g) := by
  induction h1 generalizing g with
  | nil => rfl
  | cons m h ih => exact ih (stepOf m g)

/-- The winding is a cocycle over composition: the winding of a composite history is the first leg's
winding plus the second leg's winding from where the first leg ended. -/
theorem ws1_wind_append (h1 h2 : Hist) (g : G) :
    wind (h1 ++ h2) g = wind h1 g + wind h2 (run h1 g) := by
  induction h1 generalizing g with
  | nil => simp [wind, run]
  | cons m h ih =>
      show stepSign m g + wind (h ++ h2) (stepOf m g)
        = stepSign m g + wind h (stepOf m g) + wind h2 (run h (stepOf m g))
      rw [ih (stepOf m g)]
      ring

end P3S3
