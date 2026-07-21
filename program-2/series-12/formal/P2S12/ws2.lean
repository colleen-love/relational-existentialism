/-
`program-2/series-12/formal/P2S12/ws2.lean`

WS2 - The weight is a non-negative, non-classical candidate measure. Program 2 Series 12 (2.12).

The add-then-square weight (the imported `combinedWeight`, the squared modulus of the summed amplitudes) is read as a
candidate probability over the outcomes. WS2 proves it a genuine NON-NEGATIVE weight (`ws2_sq_nonneg`: a square is
`≥ 0`), and NON-CLASSICAL (`ws2_not_classical`, resting on `P2S11.ws3_destructive`): the destructive interference of
Series 2.11 makes the combined weight fall STRICTLY below the sum of the parts (`combinedWeight attTri = 0 < 2 =
partsWeight attTri`). No classical additive probability can undercut its own parts — classically the weights of the
ways add, so `combined ≥ parts`. So the squared form is a candidate probability that already departs from any classical
measure: the quantum signature at the level of the weight.

Design docs: `program-2/series-12/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11

universe u

namespace P2S12

open P2S8 P2S11

set_option linter.unusedVariables false

/-! ## The candidate weight is non-negative -/

/-- **THE WEIGHT IS NON-NEGATIVE (WS2).** The add-then-square weight `combinedWeight att = (directAmp + loopAmp att)^2`
is `≥ 0` for every configuration — a square is non-negative. A candidate probability is at least a non-negative
number, and this one is. -/
theorem ws2_sq_nonneg (att : S → Finset S) : 0 ≤ combinedWeight att := by
  unfold combinedWeight
  exact sq_nonneg _

/-! ## The candidate weight is non-classical (below its parts) -/

/-- **THE WEIGHT IS NON-CLASSICAL (WS2).** On the frustrated cycle the add-then-square weight falls STRICTLY below the
square-then-add sum of the parts: `combinedWeight attTri = 0 < 2 = partsWeight attTri` (Series 2.11's `ws3_destructive`,
the destructive interference). No classical additive probability can do this — classically the weights of the ways add,
so the combined weight is at least the parts. The candidate probability already cannot be a classical additive one. -/
theorem ws2_not_classical : combinedWeight attTri < partsWeight attTri :=
  P2S11.ws3_destructive

end P2S12
