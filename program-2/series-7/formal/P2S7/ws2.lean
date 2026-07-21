/-
`program-2/series-7/formal/P2S7/ws2.lean`

WS2 - The tick RAISES `Q` (the arrow). Program 2 Series 7 (2.7).

Imports `P2S7.ws1`. Proves the honest, Q-SPECIFIC fact about the measure under the tick: a reification-tick STRICTLY
RAISES `rankM` (`rankM (reifyM {e0}) = rankM e0 + 1`, and again at the next step). The measure is NOT conserved. The
reified product IS plain-bisimilar to its constituent (the collapse engine identifies the states in-sight) — but
that is a fact about the STATES, not about `Q`: the collapse HIDES the arrow, it does not conserve the measure. The
in-sight-invisible increase is exactly the manufactured import (WS3, WS4). This replaces the earlier
`ws2_tick_conserves`, which proved only the state-bisimilarity and was a costume (a "conservation" that held for any
measure because in-sight the atomless carrier is one class); see `charter-status.md` finding T1-S1 (Tier-1 landing
review). The genuine content is the ARROW: `rankM` rises.

Design docs: `program-2/series-7/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws1

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE TICK RAISES `Q` (WS2, the arrow).** A reification-tick STRICTLY raises the measure: `rankM (reifyM {e0}) =
rankM e0 + 1`, and again `rankM (reifyM {e1}) = rankM e1 + 1`. The measure is not conserved — it rises. The reified
product `e1` is plain-bisimilar to its constituent `e0` (`AttentionDistinguishes`, the collapse engine identifies the
states in-sight), so the rise is INVISIBLE in-sight — but that is a fact about the states, not a conservation of `Q`:
the collapse hides the arrow. The in-sight-invisible increase is the manufactured import (WS3/WS4). -/
theorem ws2_tick_raises (hinf : ℵ₀ ≤ κ) :
    rankM (reifyM {e0}) = rankM e0 + 1
  ∧ rankM (reifyM {e1}) = rankM e1 + 1
  ∧ AttentionDistinguishes (destML hinf) (reifyM {e0}) e0 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [reifyM_e0]
  exact (ws1_rank_nontrivial hinf).2.1

end P2S7
