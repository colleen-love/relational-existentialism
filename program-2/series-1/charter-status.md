# Program 2 Series 1 (2.1), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress. At program close it is the honest account of where Series 2.1 landed against its own charter.**

*Current phase: A (charter written). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN.*

---

## 0. Snapshot

- **Phase:** A complete (charter committed). B (design) not started.
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The **P1 foundation** (`program-2/formal/P1`) is built and
  registered in `lake/` (`P1`, `P1.AxiomCheck`).
- **Axiom state:** foundation clean — every headline carrier theorem on the standard three (`propext` /
  `Classical.choice` / `Quot.sound`); `ws_witness_rank_noninjective` on `propext` / `Quot.sound`. Series build N/A.
- **Gate state:** green (`scripts/gate.sh` passes; the `P1` library imports only `P1.*` + Mathlib).
- **Open SERIOUS findings:** none (no review has run).

## 1. The carrier — the P1 foundation (built and verified)

**S1 now stands on the Series 2.0 ground** (`program-2/series-0`, relating is finite attending), which supplies the carrier and imports the Program 1 prior art below. S1's Phase B may only begin once S0 has landed. The pieces below are the ultimate (P1) source of that machinery.

The carrier is consolidated in the **P1 foundation** at `program-2/formal/P1`, built green (sorry-free,
axiom-clean on the standard three; `P1.AxiomCheck`). At Phase E the series builds on it: **Program 2 permits
importing** (`import P1`, using `P1.Core.*` / `P1.Reader.*` directly — sound because the foundation is
axiom-checked), or transcribing into `P2S1` where a workstream wants to restate at its own strength. See §5
for the discipline decision. Source map:

| Carrier piece | Location |
|---|---|
| κ-bounded powerset functor `PkObj` / `PkMap` / `toPk` | `P1.Core` |
| Reaching, `SHNE`, bisimulation `IsBisim`, `BehaviorallyIdentified` | `P1.Core` |
| Collapse engine: `ws1_atomless_bisim` (atomless states bisimilar) | `P1.Core` |
| Import Theorem: `ws2_import_theorem`, `ws2_import_theorem_static`, `ws3_atomless_distinct_is_import` | `P1.Core` |
| Labelled functor `LkObj`, `IsBisimL`, `plainOf`, `Recoverable`; `labelLoop` + `ws4_labelLoop_not_recoverable` | `P1.Core` |
| Diagonal: `Hold`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`; `residue`, `ResidueRecoverable`, `ws2_residue_free` | `P1.Core` |
| Reification: `IsReify`, `ws1_reify_injective`; tower `reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`, `ws3_order_endogenous` | `P1.Core` |
| The `Opening` shape and the coincidence (`ws1_shape_coincidence`, `ws1_coincidence_not_identity_witness`) | `P1.Core` |
| Bounded reader: `FiniteAttention` (`focus`/`reads`/`fin`/`grounded`), `AttentionDistinguishes`, `RealFor` | `P1.Reader` |
| General rank-separation `ws2_many_general`; reader-load-bearing plurality `ws2_attention_makes_real` (PR1-S2 fix) | `P1.Reader` |
| The worked witness carrier (`WCar`, `destW`, `reifyW`, `rankW`, `destWL`) and `ws2_distinction_free` | `P1.Reader` |

`P1.Core` is Series 12 WS1 verbatim; `P1.Reader` is Series 12 WS2 verbatim; both re-namespaced. **Deliberately
excluded** (guardrails, see `program-2/formal/P1.lean`): Series 12 WS3/WS4 compass/convergence (PR1-S1) is not
transcribed; `Many` is present but is not a payoff template (use `RealFor`, PR1-S2). Transcription fidelity
into `P2S1` is a Phase F check.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_cycle_reifies`, `ws1_composite_attention_finite` | OPEN | — |
| WS2 | `ws2_composite_residue`, `ws2_composite_real_for`, `ws2_tick_irreversible` | OPEN | — |
| WS3 | `ws3_stream_exogenous`, `ws3_tick_needs_stream` | OPEN | — |
| WS4 | `ws4_causal_order_endogenous`, `ws4_linearization_import` | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, audit clauses a–e) | OPEN | — |

Theorem names are the charter's provisional targets; the Phase B designs fix the exact signatures, and any rename is recorded here with its reason (never to record progress, only to fix a design error).

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO SMUGGLED CLOCK — strip test over every temporal fact. UNVERIFIED.
- (b) THE STREAM IS EXOGENOUS — `ws3_stream_exogenous` a proof term. UNVERIFIED.
- (c) THE READER IS LOAD-BEARING — `ws2_composite_real_for` names a genuine attention. UNVERIFIED.
- (d) THE FORK IS GENUINE — both WS4 arms witnessed, order structurally constrained, concurrent pair non-empty. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Findings from Phase C (design review) and Phase F (code review) are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed: original target built, name it; or Relabeled: obstruction recorded, payoff demoted to a pre-registered outcome). A finding closed by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count.

No Series 2.1 design/code findings yet (Phase C/F not run). One out-of-band verification recorded:

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| FND-1 | Foundation | COSMETIC | Delegated transcription audit of `program-2/formal/P1`: 0 SERIOUS, 0 REAL. Fidelity confirmed (body byte-identical to Series 12 WS1/WS2 modulo the intended renames), build green + axiom-clean, guardrails accurate (S1 absent, S2 fix present and reader-load-bearing, `Many` demoted). One forward-note: `gate.sh` does not yet cover future `program-2/series-NN/formal/` trees. | Handled — the Phase E registration recipe adds the per-series `check program-2/series-1 …` line when the series formal lands. Fidelity + guardrail claims independently spot-checked (diffs, greps). |

## 5. Deviations from charter (disclosed)

**Discipline decision (2026-07-20): layered import chain.** Program 1 held a transcribe-only discipline (each
series standalone, prior results transcribed not imported). Program 2 relaxes it into a layered chain
`P1 → S0 → S1 → S2 → S3` (program charter §2): each series imports the one before it. S1 imports S0 only; the
P1 prior art is reached transitively through S0, not imported directly, so all Program 1 machinery stays
mediated by S0's finite-attention ground. Sound because every layer is built and axiom-checked before the next
imports it. It changes the *provenance* of the carrier, not any target; not a target narrowing. Importing
outside the chain remains forbidden (gate-enforced).

Otherwise none yet. Any narrowing of a target between charter and design, or between design and build, is
disclosed here at the moment it happens; an undisclosed narrowing is the PR1-S2 defect and is prohibited.

## 6. Permanent opens (inherited from Program 1, untouched)

- The content of the compass.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.1 adds none and closes none of these.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series scaffold created (`spec/`, `formal/`). Status initialized.
- **2026-07-20 — Foundation.** The P1 foundation (`program-2/formal/P1`: `P1.Core` = Series 12 WS1 verbatim, `P1.Reader` = Series 12 WS2 verbatim) transcribed, registered in `lake/lakefile.toml` + `scripts/gate.sh`, built green (sorry-free, axiom-clean). Guardrails documented in `P1.lean` (PR1-S1 machinery excluded; `RealFor` not `Many`, PR1-S2). Grain preorder explored on paper (`spec/grain-exploration.md`) ahead of Phase B.
- **2026-07-20 — Import permitted.** Program 2 relaxes Program 1's transcribe-only discipline: a series may `import P1`. Recorded in §5; banner/protocol/charter updated.
- **2026-07-20 — Foundation audit (FND-1).** Delegated transcription review returned 0 SERIOUS / 0 REAL / 1 COSMETIC (see §4); fidelity and guardrails independently spot-checked and confirmed. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build.
