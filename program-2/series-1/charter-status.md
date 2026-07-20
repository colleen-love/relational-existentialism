# Program 2 Series 1 (2.1), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress. At program close it is the honest account of where Series 2.1 landed against its own charter.**

*Current phase: A (charter written). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN.*

---

## 0. Snapshot

- **Phase:** A complete (charter committed). B (design) not started.
- **Verdict:** TBD.
- **Build state:** no `formal/` sources yet. Not registered in `lake/`.
- **Axiom state:** N/A (no build).
- **Gate state:** N/A (no cross-series imports yet; gate applies once `formal/` exists).
- **Open SERIOUS findings:** none (no review has run).

## 1. The carrier (to be transcribed, not imported, at Phase E)

Transcribed unchanged from Program 1, sources to be named in the WS designs at Phase B:

- Reification tower and the fixed-point relating (Ω ≅ F(Ω)).
- Diagonal apparatus: `residue`, `diag`, `ws2_residue_free` (from Series 12 / Series 13).
- Bounded reader: `FiniteAttention` (`reads` / `fin` / `grounded`), `RealFor`, `AttentionDistinguishes` (from Series 12).
- Recoverability: `Recoverable`, `plainOf` (from Series 07 / Series 12).
- Labelled lift and `labelLoop` (the quarantined point-tag failure shape).
- Collapse engine: atomless states are bisimilar (from Series 07).

Transcription fidelity is a Phase F check: every transcribed name matches its Program 1 source by name and content.

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

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| — | — | — | (none yet) | — |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing of a target between charter and design, or between design and build, is disclosed here at the moment it happens; an undisclosed narrowing is the PR1-S2 defect and is prohibited.

## 6. Permanent opens (inherited from Program 1, untouched)

- The content of the compass.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.1 adds none and closes none of these.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series scaffold created (`spec/`, `formal/`). Status initialized. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any build.
