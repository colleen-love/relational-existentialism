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
**Status: Discharged (R2 carrier).** · Carrier decision made: **R2** (derived intrinsic face on the self-contained `νPk κ` carrier). Machine-checked in `series-4/formal/ws1.lean`.

| Obligation | Target | Status |
|---|---|---|
| Face is forced, not annotated (lossiness thesis) | `ws1_face_forced` | **Discharged** (definitional; `face` is a function of `str` alone) |
| **The weak-pullback gate** (existential) | `ws1_weak_pullback_inherited` = `ws2_weak_pullback` | **Discharged** (inherited verbatim — R2 does not change the functor, so the gate never becomes a real obligation) |
| Ω recovered with improper self-face | `ws1_omega_face` | **Discharged** (`face Ω Ω = {Ω} = ReachSet Ω`) |
| Face is an internal sub-object | `face_sub_reach` | **Discharged** (`face x y ⊆ ReachSet x`) |

*Outcome:* the blocking existential gate is a non-event on R2, exactly as the design bet predicted — the carrier is a *reading* of the plain `νPk κ`, the face a derived operation, so weak-pullback preservation is inherited and criterion (iii) holds without re-proof. The whole carrier (terminal coalgebra of `P_κ` via QPF/`Cofix`, Lambek, `bisim_eq`, Ω) is reproduced self-contained in `ws1.lean`.
*Escalation watch:* WS3's plurality genuinely needs faces as independent data (faces on R2 are `str`-derived, hence epiphenomenal for distinguishing collapse-equal states). WS3 registers the R3 escalation as a typed obligation rather than reopening this row.

### WS2 — The collapse, and the forced answer  ·  *the spine*
**Status: Partial (as pre-registered).** Machine-checked in `series-4/formal/ws2.lean`. Parts A, B, F1 Discharged; F2 dichotomy proved with internal-rigidity conditional, exactly the charter §9 hedge.

| Obligation | Target | Status |
|---|---|---|
| Collapse Theorem | `ws2_collapse` (self-contained re-proof) | **Discharged** (Impossibility proved: atomless ∧ plural unsatisfiable on `νP_κ`) |
| Imported-weight leak, general form | `ws2_leak` (all ⊥-divisor `QAlg`) + `ws2_botfree_safe` (boundary) + `ws2_leak_Luk3` (nilpotent witness) | **Discharged** (leak located exactly at ⊥-divisibility; L3 false, so the escape is real) |
| Restriction introduces no leak | `ws2_restriction_no_leak` (F1) | **Discharged** (faces of atomless objects never empty — no internal zero) |
| **Forced-answer dichotomy** | `ws2_forced_answer` (F2) | **Discharged as a dichotomy** (external ⇒ leak-or-fiat; internal ⇒ no leak by F1). General internal-rigidity remains the named open (obligation 2). |

*Outcome:* the collapse is re-proved directly from `bisim_eq` (no dependence on the heavy Series 3 ws10 chain); the leak is stated as pure algebra over a minimal `QAlg`, needing no weighted terminal coalgebra. F2 delivers the dichotomy honestly: internality *forecloses* the leak rather than an external rule *forbidding* it.
*Exports for downstream:* `ws2_collapse` — WS3 cites it as the forced counterweight for its coincidence theorem; `carrier_card_ge` — WS4 consumes it for the no-top wall.

### WS3 — Plurality without atoms
**Status: Discharged.** · **Coincidence: proved** (P3). Machine-checked in `series-4/formal/ws3.lean`.

| Obligation | Target | Status |
|---|---|---|
| Central dichotomy: do faces distinguish beyond `str`? | paper-decidable | **Resolved: (I) on R2** — faces are `str`-derived; escalation to R3 taken. |
| R3 carrier built (self-contained) | `νLk κ Q` = `Cofix (X ↦ P_κ (Q × X))`, its `qpfLk` QPF instance, `loop_dest` | **Discharged** (labelled terminal coalgebra via QPF/`Cofix`, no dependency outside `series-4/formal/`) |
| Plurality witness (distinct faces) | `ws3_loopface_ne` (P1) | **Discharged** (distinct faces ⇒ distinct loops; the `ws14_loop_ne` analogue, by face not weight) |
| Coincidence: equal on `νPk`, distinct on `νLk` | `ws3_same_succ_diff_face` (P3) + `ws2_collapse` | **Discharged** (both halves, same bare successor shape) |
| Atomless plurality bundle | `ws3_plurality_core` (P4) + `ws3_plurality_core_concrete` | **Discharged** (two distinct non-atomic states; concrete at `Q = ULift Bool`) |
| Composition stays atom-free | `ws3_faces_never_annihilate` | **Discharged (unconditional)** — internality means no external ⊥ to reach; *stronger* than ws14, which leaked at nilpotent `Luk` |

*Outcome:* the R3 escalation the design pre-registered is realized as a genuine, self-contained labelled carrier. The gate for `νLk` is a non-issue for the delivered results: loop-distinctness follows from `Cofix.dest` being a function (different `dest` ⇒ different state), so no separate weak-pullback proof is consumed. Composition is *unconditionally* atom-free — the optimistic sub-bet landed.
*Coincidence (for WS7):* P3's two halves (`ws2_collapse` on `νPk`, `ws3_loopface_ne` on `νLk`) are the same bare successor shape seen without and with faces.

### WS4 — No top, no view from nowhere  ·  *carries the facing-injectivity crux*
**Status: Discharged (unconditional wall).** · **Coincidence: proved** (V1+V2). Machine-checked in `series-4/formal/ws4.lean`.

| Obligation | Target | Status |
|---|---|---|
| Facing-injectivity | `FacingInjective` + `ws4_faces_inject` | **Discharged** (def + faces inject successors into sub-objects) |
| No-top as endogenous wall | `ws4_no_top_facing` | **Discharged, unconditional** — reframed cleanly: `#(str x) < κ ≤ #carrier`, so the wall is `x`'s *own* `< κ` relating outgrown by the world; no `FacingInjective` hypothesis needed |
| No global observer | `ws4_no_global_observer` (V2) | **Discharged** (the same wall, observer-side) |
| View is positioned (definitional) | `ws4_view_is_positioned` (V1) | **Discharged** (every view is an object's face toward a successor) |
| Substantive standpoints | `ws4_substantive_standpoints` (V3) | **Discharged** (from WS3's distinct loops — free, not manufactured) |
| Pole-coincidence residue | `ws4_pole_coincidence_residue` | **Discharged** (`Ω↾(Ω,Ω) = ReachSet Ω`) |

*Outcome:* the crux is *dissolved*, not left open. The no-top wall is unconditional — it routes through each object's own `< κ` successor bound (the endogenous self-cost of relating), never a bare cardinality cap on the carrier. `noResortToFiat` holds by construction for every proof here.
*Coincidence (for WS7):* V1 (positional, definitional) and V2 (unpositioned total view impossible, forced by the wall) are separate statements that together earn no-view.

### WS5 — The self-bounding of the world  ·  *the "grain not wall" thesis*
**Status: Partial + Impossibility proved** (both pre-registered outcomes realized). Machine-checked in `series-4/formal/ws5.lean`.

| Obligation | Target | Status |
|---|---|---|
| M1 (contraction) as a **negative** | `ws5_contraction_insufficient` | **Discharged** (carrier still `≥ κ`; faces tame quality, not branching) |
| M2 (congruence collapse) as a **negative** | `ws5_quotient_insufficient` | **Discharged** (plurality survives same-face quotient — tames edges, not state-count) |
| **The global Impossibility** | `ws5_global_groundless_collapses` | **Impossibility proved** — global groundlessness ⇒ subsingleton; the bound *cannot* be globally freed while keeping plurality |
| M3 groundless-diagonal witness | `GroundlessDiagonal` + `omegaGroundlessDiagonal` | **Discharged** (the loop-spine `{Ω}` exhibited as a witness, not posited) |
| Endogenous bound (partial positive) | `ws5_endogenous_bound` + `ws5_omega_endogenous_point` | **Partial** — the bound is endogenous *on the loop-spine* (Ω groundless & improper-faced); extending it to carry plurality is the named residue |

*Outcome:* the central question is answered sharply at the global scale in the **negative** (`ws5_global_groundless_collapses`): you cannot make the whole world groundless and keep more than one thing in it. On the loop-spine the "grain, not wall" reading *does* hold (Ω's bound is its improper self-face, not a cap). So the bound is endogenous where the world is groundless (the diagonal) and imposed where it is plural — an honest split, exactly the pre-registered Partial.

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
