/-
`program-2/series-13/formal/P2S13/ws2.lean`

WS2 - The baseline: the distance is a function of the adjacency. Program 2 Series 13 (2.13), THE CURVE.

The imported distance, read over configurations (`adjDist c := pathDist c.1`), is determined by the ADJACENCY: two
configurations with the same adjacency have the same distance (`ws2_metric_from_adjacency`). This fixes what "the
grain sources the distance" would ADD: a dependence on the grain beyond the adjacency. And the distance genuinely
RESPONDS to the adjacency (`ws2_metric_reads_adjacency`: a different adjacency gives a different distance) — it is
not a rigged constant, so the INERT verdict of WS3/WS4 is substantive: the distance is alive to the connections,
blind to the grain. The code-level face of Series 2.4's `ws4_two_axes` (the lateral axis a real grading, distinct
from the vertical one).

Design docs: `program-2/series-13/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S13.ws1

namespace P2S13

set_option linter.unusedVariables false

/-- **THE IMPORTED DISTANCE, read over configurations.** It reads the ADJACENCY component `c.1` ONLY — the grain
`c.2` never enters. This is the object whose grain-dependence is under test (audit a: the metric under test is the
imported adjacency-distance). -/
def adjDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y

/-- **THE DISTANCE IS A FUNCTION OF THE ADJACENCY (WS2).** Two configurations with the same adjacency have the same
imported distance: the geometry reads the connections, nothing else about the configuration. The baseline a
grain-dependence would have to EXCEED. -/
theorem ws2_metric_from_adjacency (c1 c2 : Config) (h : c1.1 = c2.1) :
    ∀ x y, adjDist c1 x y = adjDist c2 x y := by
  intro x y; simp only [adjDist, h]

/-- **THE DISTANCE GENUINELY RESPONDS TO THE ADJACENCY (WS2).** It is not a rigged constant: a different adjacency
gives a different distance (`pathDist aChain p0 p3 = 3 ≠ 1 = pathDist aStar p0 p3`). The distance is ALIVE to the
connections — which makes its blindness to the grain (WS3) a real decoupling, not a triviality. -/
theorem ws2_metric_reads_adjacency : ∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y :=
  ⟨p0, p3, by decide⟩

end P2S13
