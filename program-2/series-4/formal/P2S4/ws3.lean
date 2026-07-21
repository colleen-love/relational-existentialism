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

/-! ## EXT-A1 — LOAD-BEARING self-relativity (Charter Extension 1)

The single-basepoint grounding above discharges only the NEGATIVE content (no absolute metric). EXT-A1 adds the
POSITIVE, load-bearing content: the metric genuinely VARIES by self, and no absolute frame reconciles the selves.
`stepsFrom x y` is the shortest directed attention-path length FROM the self `x` TO `y`. -/

/-- The self-relative distance: shortest directed attention-path length FROM the first argument (the self). -/
noncomputable def stepsFrom (x y : W) : ℕ := sInf {n | reachIn attendsW n x y}

/-- The shortest-path characterization: `stepsFrom x y = k` iff a path of length `k` exists and none shorter. -/
lemma stepsFrom_eq (x y : W) (k : ℕ) (hk : reachIn attendsW k x y)
    (hmin : ∀ m, m < k → ¬ reachIn attendsW m x y) : stepsFrom x y = k := by
  have hne : {n | reachIn attendsW n x y}.Nonempty := ⟨k, hk⟩
  refine le_antisymm (Nat.sInf_le hk) ?_
  by_contra h
  push_neg at h
  have hmem : reachIn attendsW (sInf {n | reachIn attendsW n x y}) x y := Nat.sInf_mem hne
  exact hmin _ h hmem

/-- **THE METRIC IS LOAD-BEARING SELF-RELATIVE (WS3, EXT-A1).** The distance genuinely VARIES by self (two selves
disagree at `w2`: FAR from `w0` at 2, NEAR `w1` at 1, so as functions `stepsFrom w0 ≠ stepsFrom w1`); it is DIRECTED
(`stepsFrom w0 w1 ≠ stepsFrom w1 w0`, so no undirected absolute metric); NO absolute frame reconciles the selves
(no single `g : W → ℕ` is the distance for every self); and it GROUNDS `latW` on the peers (`stepsFrom w0 = latW`,
so `ws3_metric_grounded` and the DISTINCT verdict are preserved verbatim). Self-relativity is now a proof term,
not an interpretation of a fixed grading. -/
theorem ws3_metric_source_relative :
    ( stepsFrom w0 w2 = 2 ∧ stepsFrom w1 w2 = 1 ∧ stepsFrom w0 ≠ stepsFrom w1 )
  ∧ ( stepsFrom w0 w1 = 1 ∧ stepsFrom w1 w0 = 2 ∧ stepsFrom w0 w1 ≠ stepsFrom w1 w0 )
  ∧ ( ¬ ∃ g : W → ℕ, ∀ x : W, stepsFrom x = g )
  ∧ ( ∀ x : W, x ∈ ({w0, w1, w2} : Finset W) → stepsFrom w0 x = latW x ) := by
  have dw0w2 : stepsFrom w0 w2 = 2 :=
    stepsFrom_eq w0 w2 2 (by decide) (by intro m hm; interval_cases m <;> decide)
  have dw1w2 : stepsFrom w1 w2 = 1 :=
    stepsFrom_eq w1 w2 1 (by decide) (by intro m hm; interval_cases m; decide)
  have dw0w1 : stepsFrom w0 w1 = 1 :=
    stepsFrom_eq w0 w1 1 (by decide) (by intro m hm; interval_cases m; decide)
  have dw1w0 : stepsFrom w1 w0 = 2 :=
    stepsFrom_eq w1 w0 2 (by decide) (by intro m hm; interval_cases m <;> decide)
  have hne : stepsFrom w0 ≠ stepsFrom w1 := by
    intro h; have := congrFun h w2; rw [dw0w2, dw1w2] at this; exact absurd this (by decide)
  refine ⟨⟨dw0w2, dw1w2, hne⟩, ⟨dw0w1, dw1w0, by rw [dw0w1, dw1w0]; decide⟩, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact hne ((hg w0).trans (hg w1).symm)
  · intro x hx
    fin_cases hx
    · exact stepsFrom_eq w0 w0 (latW w0) (by decide) (by intro m hm; change m < 0 at hm; omega)
    · exact stepsFrom_eq w0 w1 (latW w1) (by decide) (by intro m hm; change m < 1 at hm; interval_cases m; decide)
    · exact stepsFrom_eq w0 w2 (latW w2) (by decide) (by intro m hm; change m < 2 at hm; interval_cases m <;> decide)

end P2S4
