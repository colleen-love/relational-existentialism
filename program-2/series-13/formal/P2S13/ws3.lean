/-
`program-2/series-13/formal/P2S13/ws3.lean`

WS3 - The coupling is earned, not defined (the anti-costume core). Program 2 Series 13 (2.13), THE CURVE.

Test the grain-dependence of the model's OWN distance, WITHOUT defining a grain-weighted distance as the recovery.
Two fronts: (i) `ws3_grain_test` — hold the adjacency FIXED and change the grain: the imported distance `adjDist` is
INVARIANT (it reads the adjacency component only, so a grain-change cannot move it) — INERT, geometry decoupled from
the grain; (ii) `ws3_no_by_hand_coupling` — the distance under test is the imported adjacency-distance `adjDist`, a
function of the adjacency, NOT the grain-weighted `foilDist`. The no-smuggling gate, at the capstone.

`foilDist` is the single COUNTERFACTUAL FOIL: a by-hand grain-weighted distance, exhibited ONLY (in WS4) to witness
that the grain-dependence test has a genuine positive side, and proved DISTINCT from the object under test here. It is
never the recovered object; the verdict (WS5) reads `adjDist` alone. The Series 2.12 `partsWeight` discipline (a built
alternative the discipline fences off), at the capstone.

Design docs: `program-2/series-13/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S13.ws2

namespace P2S13

set_option linter.unusedVariables false

/-- **THE GRAIN-DEPENDENCE TEST.** A distance-over-configurations `d` is grain-dependent on the pair `(c1, c2)` iff
it takes different values on them somewhere. Applied with `c1.1 = c2.1` (same adjacency, different grain), it asks:
does changing the grain at fixed adjacency move the distance? -/
def grainDependent (d : Config → S → S → ℕ) (c1 c2 : Config) : Prop := ∃ x y, d c1 x y ≠ d c2 x y

/-- **THE COUNTERFACTUAL FOIL.** A by-hand grain-weighted distance (`pathDist` plus a grain term): it reads BOTH the
adjacency and the grain. NOT the recovered object; exhibited only (WS4) to witness the test's positive side, and
proved DISTINCT from the object under test (`adjDist`) below. -/
def foilDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y + c.2 y

/-- **THE GRAIN TEST — INVARIANT (WS3, the anti-costume core).** For any two configurations with the SAME adjacency,
the imported distance is NOT grain-dependent: changing the grain at fixed adjacency does not move `adjDist`. INERT —
geometry decoupled from the grain. Structural: `adjDist c = pathDist c.1` has no channel to the grain `c.2`. -/
theorem ws3_grain_test (c1 c2 : Config) (h : c1.1 = c2.1) : ¬ grainDependent adjDist c1 c2 := by
  rintro ⟨x, y, hxy⟩; exact hxy (by simp only [adjDist, h])

/-- **THE GRAIN TEST, WITNESSED.** On the grain-derisking carriers (same adjacency `aChain`, grains differing at
`p3`), the imported distance is invariant: the grain genuinely moved, the distance did not. -/
theorem ws3_grain_test_witnessed :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2 ∧ ¬ grainDependent adjDist cfgFlat cfgBump := by
  refine ⟨rfl, ?_, ws3_grain_test cfgFlat cfgBump rfl⟩
  intro h; exact absurd (congrFun h p3) (by decide)

/-- **NO BY-HAND COUPLING (WS3, the no-smuggling gate, at the capstone).** The distance under test reads the
ADJACENCY component ONLY (`adjDist c = pathDist c.1`, not a function of the grain); and the grain-weighted foil is a
DISTINCT object (`foilDist cfgBump p0 p3 = 4 ≠ 3 = adjDist cfgBump p0 p3`), so the object under test is not the
smuggle. No proof term defines the distance as a function of the grain and recovers it. -/
theorem ws3_no_by_hand_coupling :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y) :=
  ⟨fun _ _ _ => rfl, ⟨cfgBump, p0, p3, by decide⟩⟩

end P2S13
