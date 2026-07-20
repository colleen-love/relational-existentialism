# Program 2 Series 0 (2.0), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: B (design committed). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN.*

---

## 0. Snapshot

- **Phase:** B complete (six design files committed as one batch, gate honored). C (blind design review) next.
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. Design settled in `spec/` (`README.md`, `ws1-design.md`…`ws5-design.md`). The **P1 foundation** (`program-2/formal/P1`) is built and axiom-clean, available to import (Program 2 permits importing); verified building cleanly at Phase B start.
- **Module naming (fixed at Phase B):** namespace `P2S0`; layout `formal/P2S0.lean` + `formal/P2S0/{ws1..ws5,AxiomCheck}.lean`, mirroring `program-1/series-13/formal/Series13/`. Registration recipe (lakefile `[[lean_lib]] P2S0`, gate `check program-2/series-0 "^import (P1|P2S0)…"`) applied at Phase E, never earlier.
- **Design decisions (fixed at Phase B, normative):** the ONE new carrier `attends : X → Finset X` (finite out-attention the sole bound), viewed as a `PkObj κ`-coalgebra via `finsetToPk` (out-neighborhoods finite, `< ℵ₀ ≤ κ`, so κ never bounds the world); the symmetric reduct `symDest` uses `hcar : mk X < κ` as AMBIENT CARRIER SIZE only (audit a); the ONE new distinction, the knowing-labelled lift `knowLift` with `plainOf knowLift = symDest`. Reification is on the FINITE functor (`FinReify : ∀ s : Finset X, attends (reify s) = s`), NOT total `IsReify` on `PkObj κ` (unsatisfiable for the finite functor; disclosed, §5 below).
- **Axiom state:** N/A (no series build). Prior art (P1) is axiom-clean on the standard three.
- **Gate state:** N/A until `formal/` exists; the Phase E recipe adds `check program-2/series-0` allowing `(P1|P2S0)`.
- **Open SERIOUS findings:** none (no review has run).

## 1. The prior art (imported from the P1 foundation, Program 2 permits it)

Series 0 imports the κ-free Program 1 machinery from `program-2/formal/P1` and builds its own carrier over it. Used pieces:

- Diagonal / residue: `P1.Core.ws1_no_self_total_hold`, `residue`, `ws2_residue_free`.
- Reification section machinery: `P1.Core.IsReify`, `ws1_reify_injective`, `reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`.
- Recoverability test: `P1.Core.Recoverable`, `plainOf`.
- Collapse engine: `P1.Core.ws1_atomless_bisim`, `ws2_import_theorem_static` (transcribed as the inherited baseline, WS2).

What Series 0 does NOT reuse: `PkObj κ` as the ontology. Series 0's ontological carrier is `attends : X → Finset X` (finite out-attention, no cardinal ceiling); κ, where the collapse engine needs it for the symmetric reduct's neighborhoods, is ambient carrier size only (audit (a)).

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_reification_exists`, `ws1_bound_is_finite_attention` | OPEN | — |
| WS2 | `ws2_collapse_inherited` (baseline, transcribed) | OPEN | — |
| WS3 (the knot) | `ws3_direction_not_recoverable`, `ws3_passive_constitution`, `ws3_active_passive_distinct` | OPEN | — |
| WS4 | `ws4_import_breaks_baseline`, `ws4_import_quantified` | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, audit clauses a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO CARDINAL CEILING — ontological bound is finite attention; any κ is ambient carrier size. UNVERIFIED.
- (b) THE ASYMMETRY IS NOT A LABEL — directed structure load-bearing, `ws3_passive_constitution` a genuine reader (not Series 11 Bookkeeping). UNVERIFIED.
- (c) DIRECTION IS NON-RECOVERABLE — `ws3_direction_not_recoverable` a proof term. UNVERIFIED.
- (d) COLLAPSE INHERITED, NOT RELITIGATED — `ws2_collapse_inherited` transcribed, no verdict hinges on it. UNVERIFIED.
- (e) IMPORT QUANTIFIED, NOT NAMED — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades, and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| — | — | — | (none yet) | — |

## 5. Deviations from charter (disclosed)

- **Reification is on the FINITE functor, not total `IsReify` on `PkObj κ` (Phase B, WS1).** The charter (§2 WS1) asks for "the finite-attention functor's reification section." The design realizes this as `FinReify attends reify := ∀ s : Finset X, attends (reify s) = s` (a section of the FINITE-powerset functor `F = Finset`), NOT as `P1.Core.IsReify (outDest hinf attends) reify` (a section of the full `PkObj κ`-coalgebra). The latter is UNSATISFIABLE for the finite functor: `outDest`'s images are finite while `PkObj κ` carries infinite sets, so `outDest _ (reify s) = s` fails for any infinite `s`. This mirrors `P1.Reader`'s disclosed "total `IsReify` unsatisfiable here." `ws1_reification_exists` is discharged non-vacuously on a carrier where `Finset X ≃ X` (infinite `X`), giving a bijective section. Not a narrowing of the target: it is the HONEST reading of "the finite-attention functor's section." Recorded so Phase C/F review it as the intended object.
- **κ as ambient carrier size (Phase B, WS2/WS3).** `symDest` and the general `knowLift` carry `hcar : mk X < κ` for the symmetric reduct's possibly-infinite in-attention neighborhoods (audit a): κ is the carrier's own size, never an ontological ceiling. The out-attention is finite for every κ (`ws1_bound_is_finite_attention`). The WS3 and WS4 witnesses use FINITE carriers (`ULift Bool`), so `hcar` comes free there and no κ hypothesis beyond `ℵ₀ ≤ κ` is needed.

## 6. Permanent opens (inherited from Program 1, untouched)

- The content of the import (the compass, the loved).
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 0 adds none and closes none.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series 0 established as the Program 2 ground: relating is finite attending, with the asymmetry of knowing as the knot, the collapse inherited as baseline, and the import seated as a quantified ingredient. Scaffold created (`spec/`, `formal/`). Status initialized. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build.
- **2026-07-20 — Phase B.** Read the canonical templates (`program-1/series-13/spec/*` for design-doc format, `program-1/series-13/formal/Series13/*` and `program-2/formal/P1/{Core,Reader}.lean` for Lean house style; `program-2/series-1/` for the sibling Tick framing). Verified the P1 foundation builds clean and axiom-clean. Wrote and committed the six design files as one batch (gate honored, before any `formal/` file): `spec/README.md` (design index, the imported prior art, the one new carrier `attends`, the one new distinction `knowLift`, the five disciplines, the strip annotations) and `spec/ws1-design.md`…`spec/ws5-design.md` (candidate triage, winning signatures, outcome classes, strip tests). Fixed the `P2S0` module naming (recorded in §0). Two disclosures recorded (§5): reification on the finite functor (not total `IsReify`), and κ as ambient carrier size. Next: Phase C, generate `spec/blind-seed-C.md` and spawn a blind reviewer against the design signatures only.
