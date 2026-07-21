> **CORRECTION (finding T1-S1, Tier-1 landing review).** The CONSERVED-RELATIVE design described below was OVERTURNED as a costume: its "in-sight conservation" (`ws2_tick_conserves`) was the collapse engine (a state-bisimilarity holding for any measure), not a `Q`-invariance, and its free-lunch fork was decided by a `Finset.card` counter disconnected from the diagonal. The series was reground to the honest, computed verdict **MONOTONE-ONLY**: the measure `Q := rankM` is non-trivial but RISES under the tick and is not conserved, and conservation-from-within is IMPOSSIBLE (the diagonal is always a source, `ws2_residue_free`). The authoritative record is the built `formal/P2S7/` (verdict `ws5_verdict_eq = monotoneOnly`), `summary.md` / `summary-technical.md`, and `charter-status.md` §4 (T1-S1, T1-A1). The CONSERVED-RELATIVE attempt is on record and checkable in `formal/P2S7/ConservedRelativeAttempt.lean`. This design file is kept as the pre-reground record of the original intent.

---

# WS2 design — the tick preserves `Q` in the self's sight (conserved-relative) (2.7)

**Prove that a reification-tick PRESERVES the measure within what the self can see: the tick's product `e1 =
reifyM {e0}` is plain-bisimilar to its constituent `e0` (the collapse engine identifies them in the plain
relating), so IN-SIGHT — over the plain-bisimulation quotient, everything the self can read off the bare relating —
the reification adds NO distinction. The rank does change at the label level (`rankM e1 = 1 ≠ 0`), the full measure
is not globally conserved (the phase thesis), but the in-sight measure is: this is general relativity's local
conservation `∇_μ T^{μν} = 0`, the global failing. The conservation is a THEOREM about the independent `rankM`
(the plain-bisimilarity), resting on the collapse engine, not a definitional triviality (charter §2 WS2, §4.c).**

## 1. Candidate constructions

1. **`Q` conserved because defined invariant.** REJECTED: rigged (§4.c). `rankM` is not tick-invariant at the label
   level; only the in-sight reading is conserved, and that is a theorem.
2. **`Q` conserved globally (`rankM (reifyM s) = rankM (constituent)`).** REJECTED and FALSE: `rankM e1 = 1 ≠ 0`.
   Asserting it would be the phase sin (§4.a). The full measure is NOT globally conserved.
3. **`Q` conserved IN-SIGHT: the tick's product is plain-bisimilar to its constituent (CHOSEN).** The reified relatum
   `e1` and its constituent `e0` are plain-bisimilar (`ws1_atomless_bisim`, both `SHNE`), so the plain relating — the
   self's sight — cannot distinguish them: any quantity read off the plain relating agrees on `e1` and `e0`. The tick
   re-encodes a latent relation as an actual relatum without adding in-sight distinction. The rank increase is exactly
   the import, invisible in-sight. Genuine (rests on the collapse engine), not built into `rankM`.

## 2. Triage

- **Conserved-relative, not global (audit a).** The payoff conserves `Q` IN-SIGHT (plain-bisimilarity), never
  globally. No theorem asserts `rankM` globally tick-invariant (it is not). The conservation is FOR the self's sight.
- **Genuine, not rigged (audit b).** `rankM` was free to jump in-sight and does not: the plain-bisimilarity is a
  theorem about the independent measure, resting on `ws1_atomless_bisim`.
- **Strip test.** `ws2_tick_conserves` → "`reifyM {e0}` and its constituent `e0` are plain-bisimilar, and `reifyM`
  sections its pattern" — a bare bisimulation + section fact. The interpretive term "conservation" strips cleanly
  (charter §0.3, the WS2 annotation).
- **Names-not-terms (audit e).** `ws2_tick_conserves` embeds no forbidden content-word.

## 3. Winning construction — typed signatures

```
-- the tick genuinely reifies (the section), and its product is plain-bisimilar to its constituent (in-sight same)
theorem ws2_tick_conserves {κ} (hinf : ℵ₀ ≤ κ) :
    attendsM (reifyM {e0}) = {e0}                                   -- the tick genuinely reifies {e0}
  ∧ reifyM {e0} = e1
  ∧ (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)  -- IN-SIGHT: product ≈ constituent
```

The plain-bisimilarity via `plainOf_rankLiftM` (so `plainOf (destML hinf) = outDest hinf attendsM`) then
`ws1_atomless_bisim (outDest hinf attendsM) (reifyM {e0}) e0` with `SHNE_M` on both (after `reifyM_e0`).

The reading (prose, not a term): because `reifyM {e0}` and `e0` are plain-bisimilar, no in-sight measure separates
them, so the tick conserves the in-sight measure. The full-measure change (`rankM e1 = 1 ≠ 0`) is the import (WS3).

## 4. Outcome classes

- The in-sight conservation is the `inSightConserved` flag (WS5). `!inSightConserved` in `verdict` returns
  `monotoneOnly` (nothing conserved even in-sight, only an arrow rises).
- If the tick's product were plain-DIStinguishable from its constituent (it is not), the tick would add in-sight
  distinction and the conserved-relative reading would fail toward MONOTONE-ONLY. Pre-registered, not reached.
