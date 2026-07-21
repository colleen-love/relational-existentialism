/-
`program-2/series-11/formal/P2S11/ws4.lean`

WS4 - The fork (INTERFERING vs ADDITIVE-ONLY, the knot). Program 2 Series 11 (2.11).

The two sides of the interference fork, both reachable on directed-attention carriers, neither by fiat.
`ws4_interfering_reachable`: the FRUSTRATED ring `attTri` (holonomy `3`, odd) has opposite path signs, so the combined
weight is STRICTLY below the parts (`0 < 2`) — genuine destructive interference.
`ws4_additive_reachable`: the GLUABLE star `attStar` (holonomy `0`, even) has equal path signs, so the combined weight
is NOT below the parts (`2 ≤ 4`, the ordinary sum times a constructive factor) — no destructive cancellation, the
classical/additive pole.

Interference is not built into the sign/weight (the star gives `4 ≥ 2`); the additive pole is not built in (the ring
gives `0 < 2`): same `amp`, same `combinedWeight`/`partsWeight`, only the directed attention differs. By
`ws3_destructive_iff` the fork is decided EXACTLY by the parity of the holonomy — the same Series 2.8 fork (frustrated
vs gluable) read one level up: the holonomy that made the common good frustrated now makes two paths cancel.

Design docs: `program-2/series-11/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11.ws1
import P2S11.ws3

universe u

namespace P2S11

open P2S8

set_option linter.unusedVariables false

/-! ## Interfering: the frustrated ring (odd holonomy) -/

/-- **INTERFERING-REACHABLE (WS4).** The frustrated ring `attTri` (holonomy `3`, odd) destructively interferes: the
combined weight is STRICTLY below the parts (`0 < 2`). Genuine destructive interference on a directed-attention
carrier. -/
theorem ws4_interfering_reachable : combinedWeight attTri < partsWeight attTri :=
  ws3_destructive

/-! ## Additive: the gluable star (even holonomy) -/

/-- **ADDITIVE-REACHABLE (WS4).** The gluable star `attStar` (holonomy `0`, even) does NOT destructively interfere: the
combined weight is the ordinary sum times a constructive factor (`combinedWeight = 4`, `partsWeight = 2`), so
`partsWeight ≤ combinedWeight` and the combined weight is NOT below the parts. The classical/additive pole. -/
theorem ws4_additive_reachable :
    partsWeight attStar ≤ combinedWeight attStar
  ∧ combinedWeight attStar = 4 ∧ partsWeight attStar = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold combinedWeight partsWeight; simp only [directAmp_eq, loopAmp_attStar]; norm_num
  · unfold combinedWeight; simp only [directAmp_eq, loopAmp_attStar]; norm_num
  · unfold partsWeight; simp only [directAmp_eq, loopAmp_attStar]; norm_num

end P2S11
