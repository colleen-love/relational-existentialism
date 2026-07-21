/-
`program-2/series-7/formal/P2S7/ws2.lean`

WS2 - The tick preserves `Q` in the self's sight (conserved-relative). Program 2 Series 7 (2.7).

Imports `P2S7.ws1`. Proves that a reification-tick PRESERVES the measure within what the self can see: the tick's
product `e1 = reifyM {e0}` is plain-bisimilar to its constituent `e0` (the collapse engine `ws1_atomless_bisim`
identifies them in the plain relating), so IN-SIGHT — over the plain-bisimulation quotient — the reification adds NO
distinction. The full rank does change at the label level (`rankM e1 = 1 ≠ 0`); the in-sight measure does not. This
is general relativity's local conservation, the global failing. The conservation is a THEOREM about the independent
`rankM` (the plain-bisimilarity), resting on the collapse engine, not a definitional triviality.

Design docs: `program-2/series-7/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws1

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE TICK CONSERVES `Q` IN-SIGHT (WS2, conserved-relative).** The tick genuinely reifies `{e0}` (the pointwise
section `attendsM (reifyM {e0}) = {e0}`, `reifyM {e0} = e1`), and its product `e1` is plain-bisimilar to its
constituent `e0` (the collapse engine `ws1_atomless_bisim`, both `SHNE`): in the self's plain sight `e1` and `e0`
are identified, so any in-sight measure agrees on them and the tick adds no in-sight distinction. The full-measure
change (`rankM e1 = 1 ≠ 0`, WS1) is the import (WS3), invisible in-sight. Conserved-relative, never global. -/
theorem ws2_tick_conserves (hinf : ℵ₀ ≤ κ) :
    attendsM (reifyM {e0}) = {e0}
  ∧ reifyM {e0} = e1
  ∧ (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0) := by
  refine ⟨sectionM_e0, reifyM_e0, ?_⟩
  rw [reifyM_e0, destML, plainOf_rankLiftM]
  exact ws1_atomless_bisim (outDest hinf attendsM) e1 e0 (SHNE_M hinf e1) (SHNE_M hinf e0)

end P2S7
