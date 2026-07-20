# Program 2 Series 2 (2.2), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: B (design committed). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN.*

---

## 0. Snapshot

- **Phase:** B complete (design committed as one batch: `spec/README.md`, `spec/ws1`–`ws5-design.md`). C (design review) next. **Precondition met:** Series 2.1 (TWO-ZONE after Extension 1) has landed.
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The **Series 2.1 ground** (`P2S1`, the tick, TWO-ZONE after Extension 1) is built and registered, reaching the **Series 2.0 ground** (`P2S0`, GROUND-ESTABLISHED) and the **P1 foundation** transitively.
- **Axiom state:** the imported layers (P2S1, P2S0, P1) are axiom-clean on the standard three. Series build N/A.
- **Gate state:** green upstream. S2's `formal/` will import `P2S1` only (gate `(P2S1|P2S2)`), reaching S0 and P1 transitively.
- **Open SERIOUS findings:** none (no review has run).

## 1. The carrier — the Series 2.1 ground (S2 imports S1)

**S2 stands on the Series 2.1 ground** (`program-2/series-1`, namespace `P2S1`): the tick, over Series 2.0's relating-is-finite-attending. S2 imports `P2S1` (Program 2's layered chain `P1 → S0 → S1 → S2`); S0 and P1 are reached transitively, not imported directly. The pieces S2 builds on:

| Carrier piece | Where |
|---|---|
| The tick: cycle reifies into a composite, the arrow, the clock knot | `P2S1.ws1`–`ws4` |
| The first other (the seed of the second locus): `ws1_first_other`; tower separation `rankLift` | `P2S0.ws1` (transitive) |
| The asymmetry of knowing: `knowLiftD`, `ws3_direction_not_recoverable`; `attends` / `sym` / `knows` / `attendedBy` | `P2S0.ws3` / `P2S0.ws1` (transitive) |
| Finite bound, no cardinal ceiling: `ws1_bound_is_finite_attention` | `P2S0.ws1` (transitive) |
| The seated exogenous import (the symmetry-breaker): `impLift`, `ws4_import_quantified` | `P2S0.ws4` (transitive) |
| Reader / recoverability / collapse engine: `RealFor`, `AttentionDistinguishes`, `Recoverable`, `plainOf`, `ws1_atomless_bisim` | `P1.Reader` / `P1.Core` (transitive) |

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_other_is_locus` (+ the shared field well-formed) | OPEN | — |
| WS2 (the reader knot) | `ws2_other_reader_wise`, `ws2_other_non_recoverable` | OPEN | — |
| WS3 | `ws3_facing_asymmetric`, `ws3_facing_partial` | OPEN | — |
| WS4 (the knot) | `ws4_mutual_residue` (or ONE / TOTALIZED reported) | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_flags_justified`, `ws5_verdict_discriminates`, audit a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) THE OTHER IS A READER, NOT A LABEL — `ws2_other_reader_wise` names a genuine reader, its `attends` load-bearing, not the Series 11 Bookkeeping tag. UNVERIFIED.
- (b) THE TWONESS IS NON-RECOVERABLE — `ws2_other_non_recoverable` a proof term (the otherness an import, Series 07). UNVERIFIED.
- (c) THE FACING IS ASYMMETRIC — `ws3_facing_asymmetric` a proof term. UNVERIFIED.
- (d) THE RESIDUE IS GENUINE, THE MUTUALITY TESTED — `ws4_mutual_residue` proved under mutual reading on a witnessed pair, both collapse and residue arms reachable, no PR1-S1 tautology. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| — | — | — | (none yet) | — |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing of a target between charter and design, or design and build, is disclosed here at the moment it happens; an undisclosed narrowing is the PR1-S2 defect and is prohibited.

## 6. Permanent opens (inherited, untouched)

- The content of the import (the compass, the loved).
- The direction of convergence (the coherence of self and other — Series 2.3's fork, not this one's).
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.2 adds none and closes none.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series 2.2 established as the OTHER: upgrade Series 2.0's first other into a genuine second attending locus, prove self and other genuinely two reader-wise, type the four readings (asymmetric and partial), and at the knot test whether mutual reading collapses, totalizes, or leaves a residue. The coherence of the two readings is deferred to Series 2.3. Scaffold created (`spec/`, `formal/`). Status initialized. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build — once Series 2.1 has landed.
- **2026-07-20 — Phase B.** Design committed as one batch: `spec/README.md` (the shared `Fin 3` witness `RCar` = self `slf` / other `oth` / higher reader `bnd`, the imports, the discipline, the outcomes) and `spec/ws1`–`ws5-design.md`. The construction: the other `oth = reifyR {slf,oth}` is the reified shared-field pattern upgraded to a locus reading back (WS1); genuinely two reader-wise via a NAMED `FiniteAttention` (`RealFor`, not `Many`) and `¬ Recoverable` (WS2); the four readings typed, the facing asymmetric (the reading-direction `¬ Recoverable`, `faceLift`) and partial (the diagonal) (WS3); the mutual residue the JOINT attention subtracting the bisimilar `bnd` (load-bearing on mutuality, not the bare diagonal), NOT COLLAPSE and NOT TOTALIZED discharged, the coherence never decided (WS4); the verdict COMPUTED `twoFacing` and discriminating (WS5). Next: Phase C, generate `spec/blind-seed-C.md` and delegate a blind design review.
