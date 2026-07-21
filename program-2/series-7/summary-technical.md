# Series 2.7 — Technical summary

**THE LEDGER, the physics capstone. Series 2.7 constructs a self-relative measure of distinction `Q := rankM` (the
reification rank) FRESH, and finds — honestly, after an independent Tier-1 landing review overturned a first
CONSERVED-RELATIVE landing as a costume — that the measure is NOT conserved. The tick strictly RAISES it (WS2, the
arrow); `rankM` is not plain-bisimulation-invariant, so the only conserved measures are trivial (WS3, no ledger);
and conservation-from-within is IMPOSSIBLE by proof (WS4): the diagonal is always a source (`ws2_residue_free`, the
residue free for every inspection), so self-reference always creates and never relocates. The verdict is computed
(WS5): MONOTONE-ONLY. Namespace `P2S7`, importing `P2S6` only. Sorry-free, axiom-clean on the standard three,
gate-green, names clean. The MONOTONE-ONLY rebuild passed an independent blind code review (zero SERIOUS).**

## The correction (finding T1-S1)

A first landing computed CONSERVED-RELATIVE. The Tier-1 landing review found it a costume, on three grounds, each
checkable: (i) `ws2_tick_conserves` proved only that the tick's product is plain-bisimilar to its constituent — the
COLLAPSE ENGINE (`ws1_atomless_bisim`), which holds for ANY measure because in-sight the atomless carrier is one
bisimulation class, NOT a `Q`-invariance (indeed a conserved-in-sight measure would be plain-invariant, which
`rankM` is not: `rankM e1 = 1 ≠ 0` yet `e1 ~ e0`); (ii) WS2 and WS3 were one fact (a `Q`-change is an import, Series
07); (iii) the free-lunch fork was decided by a `Finset.card` counter (`Qc`/`diagStep`) disconnected from the
diagonal. Graded SERIOUS; closed **Relabeled** to MONOTONE-ONLY per protocol §0.2a. The gate had missed it because
nothing checked that `inSightConserved` was a genuine `Q`-invariance rather than the collapse — fixed here by
`ws5_audit_not_conserved`.

## The CONSERVED-RELATIVE attempt, on record (finding T1-A1)

Before accepting MONOTONE-ONLY, CONSERVED-RELATIVE was genuinely attempted on the charter's own intended
"latent-and-actual" measure — a lossless re-encoding conserved via the SECTION, not the collapse
(`formal/P2S7/ConservedRelativeAttempt.lean`, standalone, checkable). Requirement 1 (a genuine Q-specific
conservation) is MET: `Qout := out-degree` satisfies `Qout (reifyC s) = s.card` via the section `attendsC (reifyC s)
= s` (`attempt_ws2_lossless`), and its differences are genuine imports (out-degree is not plain-bisimulation-invariant,
`attempt_ws1_content_apart`). Requirement 2 (the diagonal genuinely deciding `Q`) is REFUTED
(`attempt_diagonal_always_creates`): the residue is free for every inspection (`ws2_residue_free`), so the diagonal
always CREATES and the conserved side is reachable only by a disconnected counter. Proving CONSERVED-RELATIVE cannot
be earned is itself the result; it is promoted into the verdict build as `ws4_no_conserved_side`.

## The imported machinery (reached transitively through `P2S6`, never imported directly)

| Piece | Origin (transitive) |
|---|---|
| `Recoverable`, `plainOf`, `ws4_recoverable_not_import` (Series 07), `ws1_atomless_bisim` (collapse engine), `IsBisim`/`IsBisimL`, `LkObj`/`PkObj`, `SHNE` | `P1.Core` / `P2S0` |
| `rankLift`, `AttentionDistinguishes` | `P1.Reader` / `P2S0` |
| The P1 diagonal: `Hold`, `HoldPred`, `residue`, `ResidueRecoverable`, `ws2_residue_free` | `P1.Core` |
| The tick (reification-under-attention), `outDest`, `finsetToPk` | `P2S1` / `P2S0` |

## What Series 2.7 adds

The measure `Q := rankM` on `MCar = Fin 4` (`e0`, `e0'` bases at rank 0; `e1 = reifyM {e0}` at rank 1; `e2 = reifyM
{e1}` at rank 2), the measure lift `destML = rankLift (outDest attendsM) rankM`, and the finding that it rises and is
not conserved. `rankM` is structural (`if x = e1 then 1 else if x = e2 then 2 else 0`), no conservation clause.

## The workstreams

- **WS1 — the measure, non-trivial (`ws1_rank_nontrivial`).** `rankM e1 = 1 ≠ 0 = rankM e0`, not constant, and the
  difference is a genuine import: `AttentionDistinguishes (destML) e1 e0` (plain-bisimilar via the collapse engine,
  rank-lift-separated via `rankM_sep_general`). A non-trivial measure exists — so NOT DISCONNECTED.
- **WS2 — the tick RAISES `Q` (`ws2_tick_raises`).** `rankM (reifyM {e0}) = rankM e0 + 1` (and again at the next
  step) — a genuine `rankM` increase, the arrow. The reified product is plain-bisimilar to its constituent, so the
  rise is in-sight-invisible; but that is a fact about the states, not a conservation of `Q` (the earlier costume).
- **WS3 — NOT conserved (`ws3_not_conserved`), the rise is genuine import-content (`ws3_change_is_source`).** `rankM`
  is not plain-bisimulation-invariant (`e1 ~ e0` plainly yet `rankM e1 ≠ rankM e0`), and any plain-invariant `f`
  agrees on `e1`, `e0` (conserved measures are trivial on the tick pair). Every `Q`-change is a genuine import (via
  `ws4_recoverable_not_import`, Series 07): the rise is real creation of import-content, not a bookkeeping artifact.
- **WS4 — conservation-from-within is impossible (`ws4_no_conserved_side`, `ws4_rise_is_internal`,
  `ws4_no_lossless_tick`).** The tick does not conserve `rankM` (it rises), and the diagonal is always a source (for
  every inspection the residue is free, `ws2_residue_free`) — self-reference never relocates. So there is no genuine
  conserved side; the crux is settled by proof, not a counter.

## The computed verdict

`ws5_verdict_eq : verdict true false true true false false = Outcome.monotoneOnly` by `rfl` — the `inSightConserved`
flag is honestly FALSE (earned by `ws3_not_conserved`). `ws5_verdict_discriminates` reaches all six outcomes.
`ws5_flags_justified` earns the flags from WS1–WS4. **The computed verdict is MONOTONE-ONLY**: a non-trivial measure
that only rises, nothing conserved, the conserved outcome proven unreachable.

## Audit / hygiene

- **(a) no conservation asserted** (`ws5_audit_no_global`): not even local conservation holds; `global` only under
  `globalForced = true` (false).
- **(b) not by fiat** (`ws5_audit_arrow_genuine`): non-trivial (not DISCONNECTED), genuinely rises, not conserved.
- **(c) the crux is the diagonal, not import-ness** (`ws5_audit_source_is_diagonal`, `ws5_audit_no_conserved_side`):
  the impossibility rests on `ws2_residue_free`, not a counter. **The gate-gap fix** `ws5_audit_not_conserved`
  checks a conserved-in-sight measure would be plain-invariant and exhibits `rankM` is not — the check the earlier
  landing lacked.
- **(d) change is an import** (`ws5_audit_change_is_source`): rests on Series 07.
- **(e) names-not-terms** (`ws5_audit_names_not_terms : True`, placeholder): the §6 grep is clean of forbidden
  identifiers across `formal/` including the on-record attempt.
- **Build:** `lake build P2S7 P2S7.AxiomCheck` compiles; sorry-free; axioms a subset of `propext` /
  `Classical.choice` / `Quot.sound` (the `verdict`/`decide` theorems use none); gate green (`(P2S6|P2S7)`).

## What is not done (by design)

No conservation is asserted at any scope — the honest finding is that none exists (the measure of distinction rises,
conservation-from-within is impossible). The measure is a measure FOR a self; the import that sources it stays
quantified, never named. Program 1's four permanent opens are untouched: Series 2.7 adds none and closes none. It
draws the arrow, and the impossibility of the ledger, exactly.
