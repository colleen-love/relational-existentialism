/-
`program-2/series-9/formal/P2S9/ws2.lean`

WS2 - The cone. Program 2 Series 9 (2.9), THE CONE.

The cone of a source at a given depth is the rate-bounded reachable set (`ws2_cone`: `y` is in the cone iff its
lateral distance is at most `rate × depth`), and it is NON-TRIVIAL on the witnessing carrier `attSlow` (rate 1):
`p1` is inside the depth-1 cone of `p0`, but `p4` (at lateral distance 4) is strictly OUTSIDE — causally disconnected
within one tick. A genuine finite speed: some events reachable, some in an elsewhere no single tick can touch.

Design docs: `program-2/series-9/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S9.ws1

namespace P2S9

set_option linter.unusedVariables false

/-- **THE CONE IS THE RATE-BOUNDED REACHABLE SET (WS2).** `y` is in the cone of `x` at depth `depth` iff its lateral
distance is within `rate × depth`: within is reachable, beyond is causally disconnected. -/
theorem ws2_cone (att : S → Finset S) (x y : S) (depth : ℕ) :
    y ∈ ball att x depth ↔ dist x y ≤ rate att * depth := by
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **THE CONE IS NON-TRIVIAL.** On `attSlow` (rate 1), the depth-1 cone of `p0` contains `p1` (distance 1) but NOT
`p4` (distance 4 > 1): some event inside, some strictly outside. A genuine finite speed. -/
theorem ws2_cone_nontrivial : p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1 := by
  refine ⟨?_, ?_⟩ <;> decide

end P2S9
