# Relational Existentialism — Series 4: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: in Series 3 the charter accumulated REV-A through REV-H amendments inline, until the design document and its change-log were the same polluted artifact. Series 4 keeps them apart. `charter.md` is the stable statement of intent and is edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds: what each workstream reported, what discharged, what reopened, what is owed. When you want to know "what does Series 4 claim," read the charter. When you want to know "where is Series 4," read this.*

---

## How to read this file

- **Status vocabulary** (from charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success) · **Partial** (part proved, obstruction made precise) · **Failed** (not achieved, documented why) · **Trivialized** (the WS7-only verdict: an elegant unification that turned out definitional — a success, not a failure) · **Not started**.
- **Coincidence status** (from charter §5, the coincidence rule): for each §5.3 payoff, whether the definitional form and an independently forced form were separately proved and shown to coincide. Values: **Coincidence proved** · **Definitional-only** (cheap form holds, forced form open) · **N/A** (payoff has no cheap form) · **Pending**.
- **Naming discipline** (inherited from Series 3 ws4/ws5): a bundle is named by its parts, never `*_resolved` / `series4_resolved`, while any hole remains.
- Every claim of "sorry-free / axiom-free" is provisional until a machine-checked `#print axioms` against a pinned Lean/Mathlib is recorded in the axiom-check row below. Static source audits are marked *(static)*.

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (pre-report; no workstream has reported) |
| **This status file** | v0 — initialized from the charter and the seven design docs |
| **Central question** (charter §4) | Open. Can the bound be made endogenous via restriction-quality; do the five fractures heal / relocate / relabel? |
| **Headline positive on the table** | Endogenous bound (WS5) + no-top-as-real-wall (WS4) → "grain, not wall" |
| **Signature risk live** | Trivialization (WS7); the existential weak-pullback gate (WS1) |
| **Blocking item** | WS1 gate — everything downstream is conditional on it |
| **Verdict (WS7)** | Not started |

---

## Workstream status

### WS1 — The world and its faces  ·  *blocking*
**Status: Not started.** · Carrier decision pending (R2 derived-face vs R3 functor-face).

| Obligation | Target | Status |
|---|---|---|
| Face is forced, not annotated (lossiness thesis) | `ws1_face_forced` | Not started |
| **The weak-pullback gate** (existential) | `ws1_weak_pullback_inherited` = `ws2_weak_pullback` | Not started |
| Ω recovered with improper self-face | `ws1_omega_face` | Not started |

*Design bet:* R2 (face as a derived operation on the Series 3 `νPk κ` carrier) makes the gate a one-line re-export and the lossiness thesis trivial. R3 (genuine face-functor, new carrier `νRF`) is the typed fallback, escalated only if a downstream payoff provably needs faces as independent data.
*Escalation watch:* WS3 is expected to force R3 (see below). If so, the gate becomes a real obligation on `RF` and this row reopens.
*Open on entry:* none yet.

### WS2 — The collapse, and the forced answer  ·  *the spine*
**Status: Not started.**

| Obligation | Target | Status |
|---|---|---|
| Collapse Theorem (import) | `ws2_collapse` ⇐ `ws10_unlabeled_atomless_collapses` | Not started |
| Imported-weight leak, general form | `ws2_leak` (all ⊥-divisor quantales) + `ws2_botfree_safe` (boundary) | Not started |
| Restriction introduces no leak | `ws2_restriction_no_leak` (F1) | Not started |
| **Forced-answer dichotomy** | `ws2_forced_answer` (F2) | Not started |

*Pre-registered hedge (charter §9):* F2's External branch is expected to fully discharge (it is the leak + the "forbidden-not-unable" observation); the `Internal → IsRestrictionQuality` rigidity is expected to land only under a canonicity hypothesis, with general rigidity the named open. Anticipated status: **Partial** (dichotomy proved, internal-rigidity conditional).
*Exports for downstream:* `ws2_collapse` under a stable name — WS3 must cite it as the forced counterweight for its coincidence theorem.

### WS3 — Plurality without atoms
**Status: Not started.** · **Coincidence: Pending** (P3 is the coincidence theorem).

| Obligation | Target | Status |
|---|---|---|
| Central dichotomy: do faces distinguish beyond `str`? | paper-decidable | **Pre-resolved on paper: (I) holds on R2** — faces are `str`-derived, so R2 cannot carry plurality. **Escalation to R3 is forced.** |
| Plurality witness (distinct faces) | `ws3_loopface_ne` (P1) | Not started |
| Coincidence: distinct on `νRF`, equal on `νPk` | `ws3_same_succ_diff_face` (P3) + `ws2_collapse` | Not started |
| Atomless plurality bundle | `ws3_plurality_core` (P4) | Not started |
| Composition stays atom-free | `ws3_faces_never_annihilate` (unconditional target) / C-split fallback | Not started |

*Consequence for the program:* WS3 is the workstream that triggers WS1's R3 escalation. This is by design (the cheap carrier tried first, the payoff that needs more escalates deliberately), but it means the WS1 weak-pullback gate must be discharged for `RF` before WS3's witnesses are sound. **Dependency: WS3 ⟵ WS1(R3).**
*Optimistic sub-bet:* internality may make composition *unconditionally* atom-free (no external ⊥ to reach), stronger than Series 3's ws14 which genuinely leaked at nilpotent `Luk`. Fallback is the ws14-style split.

### WS4 — No top, no view from nowhere  ·  *carries the facing-injectivity crux*
**Status: Not started.** · **Coincidence: Pending** (two duties: no-top wall vs cap; V1 vs V2).

| Obligation | Target | Status |
|---|---|---|
| Facing-injectivity (the crux) | `FacingInjective` | Not started — **named crux; may be false cofinally** |
| No-top as face-counting wall | `ws4_no_top_facing` (N2, conditional) | Not started |
| No-top, hypothesis-free | `ws4_no_top_cofinal` (N3, reach goal) | Not started |
| No global observer | `ws4_no_global_observer` (V2) | Not started |
| View is positioned (definitional) | `ws4_view_is_positioned` (V1) | Not started |
| Substantive standpoints | `ws4_substantive_standpoints` (V3) | Not started |
| Pole-coincidence residue (one remark) | `ws4_pole_coincidence_residue` | Not started |

*Crux flag:* if `FacingInjective` fails cofinally, no-top falls back to Series 3's cardinality fiat and the "grain, not wall" headline fails — demoting Series 4's flagship to the incompleteness bifurcation (WS6). Reportable as **Failed** for this payoff, an honest negative.
*Audit hook:* each proof carries a `noResortToFiat` note (does it route through face-counting, not `ws12_no_hereditary_maximal`'s bare cap?) for WS7.

### WS5 — The self-bounding of the world  ·  *the "grain not wall" thesis*
**Status: Not started.**

| Obligation | Target | Status |
|---|---|---|
| M1 (contraction) as a **negative** | `ws5_not_size_increasing` refuted | Not started — *faces tame quality, not branching* |
| M2 (congruence collapse) as a **negative** | `ws5_quotient` insufficient | Not started — *tames edges, not state-count* |
| M3 groundless-diagonal witness | `GroundlessDiagonal`, `shrinkingWitness`, `ws5_witness_groundless_diagonal` | Not started |
| Endogenous bound | `ws5_endogenous_bound` | Not started |

*Consistency question (the crux):* `GroundlessDiagonal` requires faces to shrink off the diagonal (well-founded in quality) while objects stay groundless (ill-founded in states), decoupling on the self-loops. Consistent in principle (two distinct relations); the witness must not force all groundless states onto the diagonal (which would kill plurality).
*Alternative outcomes pre-registered:* **Partial** (bound endogenous on the loop-spine, plurality-bearing states still need the cap) or **Impossibility proved** (shrink + groundless forces collapse of plurality — the bound *cannot* be freed from fiat while keeping plurality; a major negative answering the central question).

### WS6 — The two incompletenesses  ·  *clearest expected win*
**Status: Not started.** · **Coincidence: Pending** (Part A is a coincidence theorem by design).

| Obligation | Target | Status |
|---|---|---|
| Self-face proper (definitional) | `ws6_selfface_proper` (A1) | Not started |
| Lawvere diagonal (forced, import) | `ws6_lawvere_incomplete` ⇐ `ws5_carrier_incomplete` | Not started |
| **Coincidence: blind spot = diagonal** | `ws6_blindspot_is_diagonal` (A3) | Not started |
| Ω non-termination (new) | `ws6_omega_nonterminating` (B2) | Not started — *no cheap form; the distinctive result* |
| Attention as face-thickening | `attend`, `ws6_selfmodel_is_attention_fixedpoint` (C1/C2) | Not started |
| Convergence characterization | re-export ws8/ws9 over face-mass | Not started |

*Design intent:* Part C defines `attend` so the induced face-mass map *is* the Series 3 replicator, making the ws8/ws9 convergence characterization (pitchfork μ⋆ = ½) transfer as a relabeling, not a re-proof — dissolving the "bolted-on" caveat.
*Likeliest to resist:* A3 (blind-spot/diagonal *equality*); fallback report "blind spot ⊆ diagonal, equality open."

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Not started.**

| Obligation | Target | Status |
|---|---|---|
| Per-payoff independence checklist | decidable dependency inspection | Not started |
| One-finitude reduction | `ws7_one_finitude` (T2) | Not started |
| Distinctness ledger (makes T2 honest) | `ws7_distinct_deductions` (T3) | Not started |
| Trivialized verdict (alternative outcome) | `ws7_trivialized` (T4) | Not started |

*Verdict outcomes, equally weighted:* **one finitude, substantively** (T2 + T3) or **Trivialized** (T4). Both are program successes.
*Self-audit disclosure (inherited from Series 3 ws9/ws10):* the audit is Claude-auditing-Claude — a disclosed limitation, not claimed independence. The distinctness ledger (T3) is the objective anchor (a dependency-graph fact, not a judgement call).

---

## The five fractures / payoffs — headline tracker

*The charter's central question is whether restriction-quality heals, relocates, or relabels each. This table is the one-glance answer as it fills in.*

| Payoff (charter §5.3) | Workstream | Verdict: healed / relocated / definitional-only / failed | Coincidence |
|---|---|---|---|
| Plurality without atoms | WS3 | Pending | Pending |
| No top | WS4 | Pending (crux: facing-injectivity) | Pending |
| No view from nowhere | WS4 | Pending | Pending |
| Endogenous bound (grain not wall) | WS5 | Pending (crux: groundless-diagonal consistency) | N/A |
| Incompleteness — blind spot | WS6 | Pending | Pending |
| Incompleteness — non-termination | WS6 | Pending | N/A (new, no cheap form) |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Nothing here is hidden in prose; when an item closes, move it to the Closed log with the discharging theorem.*

1. **Weak-pullback gate on the chosen carrier** — WS1. Existential for the program. Closes when `ws1_weak_pullback_inherited` (R2) or the `RF` preservation proof (R3) is recorded.
2. **General internal-rigidity for the forced-answer claim** — WS2. Closes with unconditional `Internal → IsRestrictionQuality` (currently expected only under a canonicity hypothesis). May remain a defended heuristic (charter §9).
3. **R3 carrier + its gate** — WS1/WS3. Triggered by WS3's forced escalation. Closes when `νRF` and its `bisim_eq` are built and weak-pullback preservation is discharged.
4. **Composition atom-freeness** — WS3. Closes with `ws3_faces_never_annihilate` (unconditional) or the C-split (conditional + failure witness).
5. **Facing-injectivity cofinality** — WS4. The no-top crux. Closes with `ws4_no_top_cofinal` (N3) or is reported Failed for the no-top payoff.
6. **GroundlessDiagonal consistency + witness** — WS5. Closes with `ws5_witness_groundless_diagonal`, or Impossibility-proved if inconsistent-with-plurality.
7. **Blind-spot = diagonal equality** — WS6. Closes with `ws6_blindspot_is_diagonal` (A3), or downgraded to containment.
8. **Distinctness ledger** — WS7. The trivialization guard. Closes with `ws7_distinct_deductions` (T3), or the program returns Trivialized.
9. **Machine-checked axiom pass** — all. Standing operational obligation: `#print axioms` against a pinned Lean/Mathlib for every headline theorem before any "sorry-free / axiom-free" claim is made without the *(static)* qualifier. Cite commit hash + clean-build log in any publication.

---

## Closed log

*Empty. When an open obligation closes, record it here with: date, workstream, discharging theorem, and status class. When a workstream reports, append a dated entry summarizing what discharged, what reopened, and any methodology note (a correction or hand-off — never a redefinition of a charter target).*

<!--
Template for a workstream report entry:

### [date] WSn reported — Status: {Discharged | Impossibility proved | Partial | Failed}
- Discharged: {theorems}
- Impossibility proved: {theorems, why they count as success}
- Open / routed: {obligation → owning workstream}
- Coincidence: {proved | definitional-only | N/A}
- Methodology note: {correction or hand-off, if any}
- Axiom check: {run against pinned build | static | owed}
- Charter touched? {no — status-only | yes, and why the charter design itself needed a fix}
-->

---

## Charter-change log

*Distinct from workstream progress: this logs edits to `charter.md` itself. Per the Series 4 discipline, the charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress — progress lives above. Each entry: what changed in the charter, why it was a design error and not a status update, and the date.*

- **REV-0 (initial):** charter created; no changes yet. All seven workstream design docs drafted under `spec/wsN/design.md`.

---

*Status file v0. Maintained alongside `charter.md` (stable) and `spec/wsN/design.md` (per-workstream designs). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem; keep charter edits in the charter-change log and out of the workstream progress. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
