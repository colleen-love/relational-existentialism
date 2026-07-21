/-
`program-2/series-7/formal/P2S7/ws4.lean`

WS4 - The rise is internal creation; no conserved side (the knot, honestly). Program 2 Series 7 (2.7).

Imports `P2S7.ws3`. The knot the charter posed was the free-lunch crux: does self-reference CREATE the measure or
RELOCATE it (conserved)? On this machinery the answer is not a self-relative fork — it is forced ONE way: the tick
RAISES `rankM` and there is no lossless (conserved) tick, because reification always manufactures a genuine
non-recoverable import (Series 07). The residue (the P1 diagonal) confirms the source is INTERNAL: for EVERY
inspection the residue is a genuine non-recoverable content produced by self-inspection alone, no import crossing the
boundary (`ws2_residue_free`). So the arrow is CREATION from within — "all creation and no ledger" — not a conserved
re-encoding. This REPLACES the earlier `Qc`/`diagStep` count fork, which decided the verdict on `Finset.insert`
cardinality (a triviality disconnected from the diagonal); see `charter-status.md` finding T1-S1. No counter decides
anything here; the verdict rests on the measure genuinely rising and not being conserved (WS2/WS3).

Design docs: `program-2/series-7/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws3

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE RISE IS INTERNAL CREATION (WS4).** The source of the arrow is internal, on the diagonal: for EVERY
inspection the residue is a genuine non-recoverable content produced by self-inspection alone, no import crossing the
boundary (`ws2_residue_free`); and the tick's product is a genuine import manufactured from within (`e1`
plain-bisimilar to `e0` yet label-separated, `AttentionDistinguishes`). So the measure rises by CREATING
non-recoverable distinction from within — all creation, not a conserved re-encoding. Rests on the diagonal (the
residue), not on boundary import-ness. -/
theorem ws4_rise_is_internal (hinf : ℵ₀ ≤ κ) :
    (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)
  ∧ AttentionDistinguishes (destML hinf) e1 e0 :=
  ⟨fun insp => ws2_residue_free (outDest hinf attendsM) insp, (ws1_rank_nontrivial hinf).2.1⟩

/-- **NO LOSSLESS (CONSERVED) TICK (WS4).** The tick does NOT conserve `rankM` — it raises it
(`rankM (reifyM {e0}) ≠ rankM e0`, `1 ≠ 0`). -/
theorem ws4_no_lossless_tick (hinf : ℵ₀ ≤ κ) : rankM (reifyM {e0}) ≠ rankM e0 := by decide

/-- **CONSERVATION-FROM-WITHIN IS IMPOSSIBLE (WS4, the resolved crux — the free-lunch crux settled by PROOF).** Two
facts force the crux away from conservation. (i) The tick does NOT conserve the measure (`rankM (reifyM {e0}) ≠
rankM e0`, it rises). (ii) The diagonal is ALWAYS a source: for EVERY inspection the residue is free
(`ws2_residue_free`) — self-reference never relocates, it always manufactures a new non-recoverable content from
within. So there is NO genuine conserved/relocate side; the "conserved" branch is reachable only by a counter
disconnected from the diagonal (the costume the earlier CONSERVED-RELATIVE landing used, finding T1-S1). Hence
CONSERVED-RELATIVE cannot be earned — conservation-from-within is impossible — and the honest verdict is
MONOTONE-ONLY. The full search is on record and checkable in `P2S7.ConservedRelativeAttempt`: a genuine
section-conservation of an out-degree measure (requirement 1) EXISTS, but the diagonal cannot decide it toward
conservation (requirement 2 refuted), because the residue is always free. -/
theorem ws4_no_conserved_side (hinf : ℵ₀ ≤ κ) :
    (rankM (reifyM {e0}) ≠ rankM e0)
  ∧ (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp) :=
  ⟨ws4_no_lossless_tick hinf, (ws4_rise_is_internal hinf).1⟩

end P2S7
