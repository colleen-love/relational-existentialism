/-
`program-2/series-5/formal/P2S5/ws2.lean`

WS2 - The relating loops (attention is cyclic). Program 2 Series 5 (2.5).

The RELATING genuinely cycles: the tick carrier `TCar` (reached from `P2S1`) carries a directed attention cycle
`p0 ⇄ p1` between DISTINCT base relata, and that cycle reifies into the composite `kA`, sectioning its pattern
(`attendsT (reifyT cycleA) = cycleA`). The base relata `p0`, `p1` are NOT reified composites, so no causal edge
runs among them (WS3's `causalDep` requires the target be a composite): the relating loops where causation does
not. Built on Series 2.0/2.1's `ws1_cycle_reifies`.

Design docs: `program-2/series-5/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S5.ws1

universe u

namespace P2S5

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-- **THE RELATING GENUINELY CYCLES (WS2).** A directed 2-cycle between distinct base relata (`p1 ∈ attendsT p0
∧ p0 ∈ attendsT p1`) exists and reifies to the composite `kA` (`reifyT cycleA = kA`), which attends exactly its
cycle (`attendsT (reifyT cycleA) = cycleA`, a real section). The loop lives in the bare relating; whether it is
CAUSAL is the WS3/WS4 question. From `ws1_cycle_reifies`. -/
theorem ws2_relating_cycles :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1)
  ∧ reifyT cycleA = kA
  ∧ attendsT (reifyT cycleA) = cycleA := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end P2S5
