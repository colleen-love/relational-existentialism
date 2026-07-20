# Relational Existentialism, Program 2, Charter Status

**The living ledger, at the PROGRAM level. The program charter (`charter.md`) is the fixed bar; this file records which series exist, what each proved, how each landed, every Charter Extension, and where the program verdict stands. It is the program-level analogue of a series' `charter-status.md`: §0 snapshot, §1 the stack, §2 the series roster with verdicts, §3 program audit clauses, §4 the extensions ledger, §5 deviations, §6 permanent opens, §7 the series log. It never edits a target to record progress; the program verdict accumulates from the series verdicts as they land (protocol §0.6).**

*Current program phase: Series 2.0–2.2 landed and accepted; Series 2.3 chartered (Phase A), not built. Program verdict: ACCUMULATING (three rungs consistent with CONSTRUCTED-AND-WALLED; not read off until 2.3 lands). The P1 foundation and Series 2.0–2.2 are built, axiom-clean, and gate-green.*

---

## 0. Snapshot

- **Tiers.** Tier 1 (this persistent design/review conversation) has authored the program charter and the Series 2.0–2.3 triads, reviewed the S0/S1/S2 landings, and written the S0/S1 Charter Extensions. Tier 2 executors have run S0, S1, S2 to computed verdicts.
- **Program verdict:** ACCUMULATING. Three landed rungs (GROUND-ESTABLISHED, TWO-ZONE, TWO-FACING) are each consistent with the expected CONSTRUCTED-AND-WALLED; the program standing is not read off until Series 2.3 (the edge) lands.
- **Build state:** `P1`, `P2S0`, `P2S1`, `P2S2` built and registered in `lake/lakefile.toml` `defaultTargets`. Series 2.3 has no `formal/` yet (charter-only).
- **Axiom state:** every built layer is axiom-clean on Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`), verified per layer via its `AxiomCheck`.
- **Gate state:** green. The layered chain `P1 → S0 → S1 → S2 (→ S3)` is enforced by per-series `scripts/gate.sh` closure lines; each series imports only its predecessor plus its own roots plus Mathlib.
- **Open SERIOUS program findings:** none. (S0/S1 under-gradings were caught by Tier 1 and closed via Charter Extensions to Fixed.)
- **PR open:** #95 (whole of Program 2 through S2 + S3 charter), branch `claude/p2s2-protocol-execution-dj1jhv`.

## 1. The stack — the layered import chain (protocol §0.3)

Program 2 relaxes Program 1's transcribe-only rule into a LAYERED IMPORT CHAIN. Each layer is built and axiom-checked before the next imports it; each series imports ONLY its immediate predecessor plus Mathlib, reaching the rest transitively.

| Layer | Namespace | Role | Reaches |
|---|---|---|---|
| P1 foundation | `P1.Core` / `P1.Reader` | Program 1 prior art (Series 12 WS1/WS2 verbatim, re-namespaced); the collapse engine, the diagonal, the mint, the bounded reader, recoverability. PR1-S1/PR1-S2 machinery DELIBERATELY EXCLUDED (guardrail banner). | Mathlib |
| Series 2.0 | `P2S0` | The ground: relating IS finite attention. Re-seats P1's κ-free machinery on the attention carrier. | P1 |
| Series 2.1 | `P2S1` | The tick: endogenous time, reification-under-attention. | P2S0 |
| Series 2.2 | `P2S2` | The other: the second attending locus, genuinely two reader-wise. | P2S1 |
| Series 2.3 | `P2S3` | The coherence: `Converges₂`, the two-zone fork (charter only). | P2S2 |

Nothing downstream reaches behind its predecessor to raw machinery the predecessor corrects (nothing reaches behind S0 to P1's κ-bounded carrier). The chain is the program's spine (protocol §5).

## 2. The series roster (verdicts computed, never hand-set)

| Series | The knot | Verdict | Landed | Key payoff (named theorem) |
|---|---|---|---|---|
| 2.0 the ground | relating = finite attention; the unreturned gaze | **GROUND-ESTABLISHED** | accepted | `ws1_first_other`, `ws3_direction_not_recoverable`, `ws4_import_quantified` |
| 2.1 the tick | endogenous time without a smuggled clock | **TWO-ZONE** | accepted | `ws4_causal_order_endogenous`, `ws4_linearization_import`, `ws5_verdict_eq = twoZone` |
| 2.2 the other | genuinely two reader-wise, not label-wise | **TWO-FACING** | accepted | `ws2_other_reader_wise` (named `slfReader`), `ws4_mutual_residue`, `ws5_verdict_eq = twoFacing` |
| 2.3 the coherence | `Converges₂` a genuine fork on the import boundary | **TBD** (charter-only) | — | targets OPEN; direction of convergence never decided |
| later population | the dynamic population stretch | not owed | — | recorded if reached |

Each series verdict is a discriminating `Bool^n → Outcome` computed at its WS5, with pre-registered alternatives reachable (S1's `twoZone` vs alternatives; S2's `ws5_verdict_discriminates` reaching ONE and TOTALIZED). The program verdict accumulates from this column (protocol §0.6, §5).

## 3. Program audit clauses (protocol §0; UNVERIFIED-per-landing until each series is accepted)

- (a) THE BAR ONLY RISES — every Charter Extension strengthened a target; none weakened one. VERIFIED for S0 Ext1, S1 Ext1.
- (b) INDEPENDENT LANDING REVIEW — each accepted series was re-derived by Tier 1, not trusted from the executor's own review. VERIFIED for S0, S1, S2.
- (c) THE CHAIN IS SOUND AND ENFORCED — every layer built and axiom-checked before the next imports it; gate green; nothing reaches behind its predecessor. VERIFIED through S2.
- (d) THE EXCLUDED MACHINERY STAYS EXCLUDED — no series re-imported or reconstructed PR1-S1's `Compass`/`Converges` or PR1-S2's `Many`-as-payoff. VERIFIED through S2; S3 is the central watch-point (it rebuilds convergence FRESH and constrained).
- (e) THE VERDICT IS COMPOSED — each series verdict computed; the program verdict read off the sequence, not asserted ahead of it. IN PROGRESS (accumulating).
- (f) THE PERMANENT OPENS ARE NEVER FILLED — roster of four unchanged across S0/S1/S2; S3 draws the direction of convergence sharper and fills it never. VERIFIED through S2.

## 4. Charter Extensions ledger (protocol §3)

Extensions are Tier 1's bar-raising instrument, written after an independent landing review found a target too generous. Each only ever raises the bar; each triggered an executor E/F/G re-run to closure.

| Series | Extension | What it caught | Raised to | Closure |
|---|---|---|---|---|
| 2.0 | Ext 1 | inert reification (WS1); bare-conjunction asymmetry (WS3) | `ws1_first_other` (reify the self-loop → the first other, non-recoverable); WS3 a load-bearing implication (knowing-asymmetry) | C1-S1 / C3-S1 closed **Fixed** |
| 2.1 | Ext 1 | non-directional arrow; generic stream; bare residue | R1 directional causal arrow; R2 tick-specific stream on `TCar`; R3 load-bearing residue (attention ⊊ relating) | EXT-F1 / F2 / F3 closed **Fixed** |
| 2.2 | — | (landing review found the verdict earned; the named-reader C1-S1 repair `slfReader` and the load-bearing `ws4_mutual_residue` were already in the executor's build) | — | accepted without extension |
| 2.3 | — | not yet built | — | — |

Series-level findings ledgers live in each `series-N/charter-status.md` §4; this table records only that a program-level extension happened.

## 5. Deviations from the program charter (disclosed)

- **Layered import chain vs Program 1's transcribe-only rule.** The program charter §2 "The import stack (discipline)" states this deviation openly: Program 2 imports built layers rather than transcribing them, sound because each is axiom-checked before the next imports it, and it removes transcription drift as a failure mode. Not a narrowing; a deliberate, disclosed relaxation.
- No other deviation. Any narrowing between the program charter's series decomposition (§2) and a series' actual charter is disclosed in that series' status §5 at the moment it happens; none has occurred that revises the decomposition.

## 6. Permanent opens (inherited from Program 1, carried untouched)

- The content of the compass / orientation.
- The direction of convergence (the coherence of self and other) — Series 2.3 draws it exactly and fills it never.
- The differentiating act.
- The classification of the out-of-image imports.

Program 2 adds none and closes none. Every series confirms the count is four (protocol §0.5, audit (f)).

## 7. Series log

- **2026-07-20 — Program charter.** Hybrid spine fixed; σ-as-exogenous-stream; K1–K4 false escapes; §2 series decomposition; the layered import chain codified. Tier 1 established.
- **P1 foundation.** Series 12 WS1/WS2 transcribed verbatim, re-namespaced `P1.Core` / `P1.Reader`; `AxiomCheck` green; guardrail banner excluding PR1-S1/PR1-S2 machinery. Built and registered.
- **Series 2.0 — the ground.** Executor ran A→G to a first verdict; Tier 1's landing review caught inert reification and bare-conjunction asymmetry; Ext 1 written; executor re-ran to **GROUND-ESTABLISHED** (C1-S1/C3-S1 Fixed). Accepted.
- **Series 2.1 — the tick.** Executor built `TCar = Fin 7`; Tier 1's review caught non-directional arrow, generic stream, bare residue; Ext 1 written; executor re-ran to **TWO-ZONE** (EXT-F1/F2/F3 Fixed). Accepted.
- **Series 2.2 — the other.** Executor built `RCar = Fin 5` with the named reader `slfReader` (the PR1-S2 repair) and the load-bearing `ws4_mutual_residue`; Tier 1's review found the verdict earned, no extension needed. **TWO-FACING**. Accepted. Forward-note **PX-1** recorded (the twoness is rank-based; S3 may lift rank → import).
- **Series 2.3 — the coherence.** Tier 1 authored `charter.md` / `charter-status.md` / `protocol.md`: `Converges₂` over the S2 pair, the two-zone fork SHAPE-DRAWN, the direction of convergence never decided, PR1-S1 the promoted first-class watch-point, convergence built FRESH (not Series 12's excluded machinery). Phase A complete; awaiting executor for Phase B. PR #95 opened.
- **2026-07-20 — Program status + protocol.** Tier 1 wrote the program-level `protocol.md` (the two-tier workflow) and this `charter-status.md` (the program ledger), as program-level analogues of the series triad.
