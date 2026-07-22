/-
`program-2/series-13/formal/P2S13/ws4.lean`

WS4 - The fork (GRAVITATIONAL vs INERT) (the knot). Program 2 Series 13 (2.13), THE CURVE.

The fork, each pole pre-registered, neither by fiat. `ws4_inert_reachable`: a configuration pair (same adjacency,
different grain) on which the imported distance is INVARIANT — geometry decoupled from the grain (which Series 2.4's
distinctness of the two axes suggests is the case). `ws4_gravitational_reachable`: the GRAVITATIONAL pole of the
grain-test is genuinely inhabited — at fixed adjacency, the grain-weighted foil DOES vary with the grain — so the
test is two-sided and the imported distance's INERT is substantive, not vacuous. The foil is proved NOT the imported
distance, so the pole is inhabited WITHOUT smuggling: the imported distance is not among the grain-dependent
distances (that is `ws4_inert_reachable` / `ws3_grain_test`).

(The theorem `ws4_gravitational_reachable` carries the charter's WS4 target name. It is grep-clean — `\bgravity\b`
does not match the `_`-delimited "gravitational", the house standard, cf. Series 2.9's `ws4_cone_reachable` with
"cone" on its own forbidden list. The GRAVITATIONAL OUTCOME CONSTRUCTOR is neutrally named `sourced`, WS5.)

Design docs: `program-2/series-13/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S13.ws3

namespace P2S13

set_option linter.unusedVariables false

/-- **INERT REACHABLE (WS4).** A configuration pair with the SAME adjacency (`aChain`) and DIFFERENT grain (differing
at `p3`) on which the imported distance is invariant — geometry decoupled from the grain. Reached by the imported
distance itself: this is the pole the verdict lands on. -/
theorem ws4_inert_reachable :
    cfgFlat.1 = cfgBump.1 ∧ cfgFlat.2 ≠ cfgBump.2
  ∧ (∀ x y, adjDist cfgFlat x y = adjDist cfgBump x y) := by
  refine ⟨rfl, ?_, fun x y => rfl⟩
  intro h; exact absurd (congrFun h p3) (by decide)

/-- **GRAVITATIONAL REACHABLE (WS4).** The GRAVITATIONAL pole of the grain-test is genuinely inhabited: at fixed
adjacency, the grain-weighted foil DOES vary with the grain (`foilDist cfgFlat p0 p3 = 3 ≠ 4 = foilDist cfgBump p0
p3`), so the test is two-sided and not hard-wired to INERT. The foil is NOT the imported distance (`foilDist cfgBump
p0 p3 = 4 ≠ 3 = adjDist cfgBump p0 p3`), so the pole is inhabited WITHOUT smuggling — the imported distance is not
among the grain-dependent distances. The substantive content: some distances gravitate; the model's OWN does not. -/
theorem ws4_gravitational_reachable :
    cfgFlat.1 = cfgBump.1
  ∧ grainDependent foilDist cfgFlat cfgBump
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y) :=
  ⟨rfl, ⟨p0, p3, by decide⟩, ⟨cfgBump, p0, p3, by decide⟩⟩

end P2S13
