/-
`program-2/series-4/formal/P2S4/ws3.lean`

WS3 - Space is real-as-import; directed, granular, self-relative. Program 2 Series 4 (2.4).

The lateral separation between peers is a genuine IMPORT: the `latW`-label is non-recoverable over the plain
relating (`ws3_lateral_is_import`, resting on Series 07's collapse engine). The breadth metric is DIRECTED (a
pair reachable forward but not backward at the same length), GRANULAR (step 0 is identity, a smallest positive
step exists), and SELF-RELATIVE (path-grounded from the fixed self `w0`, `ws3_metric_grounded`), never absolute.
The directedness inherits the Series 2.0 knowing-asymmetry (`ws3_direction_not_recoverable`); that inheritance is
prose, not re-proved here.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S4.ws2

universe u

namespace P2S4

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE LATERAL SEPARATION IS A GENUINE IMPORT (WS3, Series 07).** The `latW`-label is not recoverable: the
plain bisimulation relating `w0`,`w2` (the collapse engine) is not a lat-bisimulation, so no recovery of the
plain relating carries the lateral labels. Collapsing space into time would require recovering what the relating
cannot carry. -/
theorem ws3_lateral_is_import (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (latLiftW hinf) := by
  intro hrec
  obtain ⟨⟨R, hR, hRel⟩, hno⟩ := ws1_peers_non_recoverable hinf
  exact hno ⟨R, hrec R hR, hRel⟩

/-- **THE METRIC IS DIRECTED (WS3).** `w0` reaches `w1` in one step, but `w1` does not reach `w0` in one step
(it takes two): the attention path runs one way, so distance need not equal its reverse. The spatial face of the
Series 2.0 knowing-asymmetry. -/
theorem ws3_directed :
    reachIn attendsW 1 w0 w1 ∧ ¬ reachIn attendsW 1 w1 w0 ∧ reachIn attendsW 2 w1 w0 := by
  decide

/-- **THE METRIC IS GRANULAR (WS3).** The length-0 reach is identity (the discrete floor), and a smallest
positive step (length 1 between distinct states) exists: a smallest step, the spatial twin of the tick. -/
theorem ws3_granular :
    (∀ x y : W, reachIn attendsW 0 x y ↔ x = y)
  ∧ (∃ x y : W, reachIn attendsW 1 x y ∧ x ≠ y) :=
  ⟨fun _ _ => Iff.rfl, ⟨w0, w1, by decide, by decide⟩⟩

/-- **THE METRIC IS SELF-RELATIVE AND PATH-GROUNDED (WS3, audit a + d).** On the peers, `latW` is EXACTLY the
shortest attention-path length FROM the fixed self `w0`: there is a path of length `latW x` from `w0` to `x`,
and no shorter path. The distance is measured FROM a self; there is no absolute two-argument metric. -/
theorem ws3_metric_grounded :
    ∀ x : W, x ∈ ({w0, w1, w2} : Finset W) →
      reachIn attendsW (latW x) w0 x ∧ ∀ m : ℕ, m < latW x → ¬ reachIn attendsW m w0 x := by
  intro x hx
  fin_cases hx
  · exact ⟨by decide, by intro m hm; change m < 0 at hm; omega⟩
  · exact ⟨by decide, by intro m hm; change m < 1 at hm; interval_cases m; decide⟩
  · exact ⟨by decide, by intro m hm; change m < 2 at hm; interval_cases m <;> decide⟩

end P2S4
