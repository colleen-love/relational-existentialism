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
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v1 — all seven workstreams reported and machine-checked |
| **Formalization** | `series-4/formal/ws1.lean … ws7.lean`, `Series4.lean`, `AxiomCheck.lean` — builds `sorry`-free, no custom axioms (34 headline theorems on Mathlib's standard three only). **Self-contained**: nothing imported from `archive/`. |
| **Central question** (charter §4) | **Answered, split.** No-top is a *real endogenous wall* (WS4, unconditional). The bound is endogenous on the loop-spine (WS5, Partial) but **globally** groundlessness collapses plurality (WS5, Impossibility) — so "grain, not wall" holds locally, not globally. |
| **Headline positive** | No-top-as-real-wall (WS4) ✓; plurality without atoms via internal faces (WS3) ✓; the two incompletenesses (WS6) ✓ |
| **Signature risk** | Trivialization — **refuted** (WS7: one finitude, substantively; `ws7_deductions_dont_collapse`). Weak-pullback gate (WS1) — **non-event** on the R2 carrier. |
| **Blocking item** | WS1 gate — **discharged** (inherited). |
| **Verdict (WS7)** | **One finitude, substantively** (`ws7_verdict = oneFinitude`). |

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
**Status: Discharged (A3 downgraded to coexistence; Part C convergence deferred).** Machine-checked in `series-4/formal/ws6.lean`.

| Obligation | Target | Status |
|---|---|---|
| Self-face proper (definitional) | `ws6_selfface_proper` (A1) | **Discharged** (`face x x ⊂ ReachSet x` for non-self-loop `x`) |
| Lawvere diagonal (forced) | `ws6_lawvere_incomplete` (A2) | **Discharged** (Cantor diagonal on the support; no cardinality fact consumed) |
| **Coincidence: blind spot vs diagonal** | `ws6_blindspot_nonempty` (A3) | **Partial** — both blind spots proved *nonempty* (geometric + logical); their **equality** is the named open (obligation 7), delivered as coexistence per the pre-registered fallback |
| Ω non-termination (new) | `ws6_omega_nonterminating` (B2) | **Discharged** (complete in extent `face Ω Ω = ReachSet Ω`, yet self-membered `Ω ∈ str Ω` — closed at no depth) |
| Attention as face-thickening | `attend`, `selfModel`, `ws6_selfmodel_is_attention_fixedpoint` (C) | **Discharged (definitional)** — self-model = inward face = attention's fixed point |
| Convergence characterization | ws8/ws9 replicator over face-mass | **Deferred** — the quantitative Series 3 dynamics (pitchfork `μ⋆ = ½`) are not reproduced in this self-contained pass; the inherited-dynamics residue |

*Outcome:* the distinctive new result — B2, the on-diagonal non-termination — lands cleanly (the founding "self is a paradox" made a theorem). A3's *equality* is the one crux that resisted, exactly as flagged; it is reported honestly as coexistence with equality open, not laundered.

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Discharged — one finitude, substantively.** Machine-checked in `series-4/formal/ws7.lean`.

| Obligation | Target | Status |
|---|---|---|
| The single finitude | `FinitudeOfFacing` + `ws7_finitude_of_facing` | **Discharged** (face proper off-diagonal, improper on it) |
| One-finitude reduction | `ws7_one_finitude` (T2) | **Discharged** (six payoffs assembled as distinct consequences) |
| Distinctness anchor (makes T2 honest) | `ws7_deductions_dont_collapse` (T3) | **Discharged** — the off-diagonal (proper) and on-diagonal (improper) deductions apply to *provably disjoint* states; a structural impossibility, not a judgement call |
| Verdict (typed) | `ProgramVerdict` + `ws7_verdict` + `ws7_not_trivialized` (T4) | **Discharged** — verdict is **one finitude, substantively**; `Trivialized` remains a reachable typed alternative that T3 refutes |

*Verdict:* **one finitude, substantively.** The five/six payoffs are distinct consequences of the single finitude of facing, and the distinctness is anchored objectively (proper ≠ improper for a single object). The audit was genuinely capable of returning *Trivialized* — that outcome is a typed constructor refuted by `ws7_deductions_dont_collapse`, not an absent option.
*Self-audit disclosure:* Claude-auditing-Claude — a disclosed limitation; T3 is the objective structural anchor.

---

## The five fractures / payoffs — headline tracker

*The charter's central question is whether restriction-quality heals, relocates, or relabels each. This table is the one-glance answer as it fills in.*

| Payoff (charter §5.3) | Workstream | Verdict: healed / relocated / definitional-only / failed | Coincidence |
|---|---|---|---|
| Plurality without atoms | WS3 | **Healed** (labelled carrier; distinct faces ⇒ distinct loops) | **Proved** (P3: collapse on `νPk`, split on `νLk`) |
| No top | WS4 | **Healed** (unconditional endogenous wall, `#(str x) < κ ≤ #carrier`) | **Proved** (wall routes through self-cost, not fiat) |
| No view from nowhere | WS4 | **Healed** (same wall, observer-side) | **Proved** (V1 definitional + V2 forced) |
| Endogenous bound (grain not wall) | WS5 | **Relocated** — endogenous on the loop-spine; **globally impossible** while keeping plurality (Impossibility proved) | N/A |
| Incompleteness — blind spot | WS6 | **Healed** (self-face proper + Lawvere diagonal); equality of blind spots open | **Coexistence** (equality the named open) |
| Incompleteness — non-termination | WS6 | **Healed** (Ω complete-yet-unclosed) | N/A (new, no cheap form) |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Nothing here is hidden in prose; when an item closes, move it to the Closed log with the discharging theorem.*

1. ~~**Weak-pullback gate on the chosen carrier** — WS1.~~ **CLOSED** — `ws1_weak_pullback_inherited` (R2; the functor is unchanged, so the gate is inherited).
2. **General internal-rigidity for the forced-answer claim** — WS2. **OPEN.** The F2 dichotomy is proved; unconditional `Internal → IsRestrictionQuality` remains a defended heuristic (charter §9), delivered here under the canonicity witness (the reachable face + F1).
3. ~~**R3 carrier + its gate** — WS1/WS3.~~ **CLOSED** — the labelled carrier `νLk κ Q` (`Cofix (X ↦ P_κ (Q × X))`) is built self-contained; loop-distinctness needs no separate weak-pullback proof (it follows from `Cofix.dest` being a function).
4. ~~**Composition atom-freeness** — WS3.~~ **CLOSED** — `ws3_faces_never_annihilate` (unconditional; internality leaves no external ⊥ to reach).
5. ~~**Facing-injectivity cofinality** — WS4.~~ **CLOSED (dissolved)** — the no-top wall is unconditional (`ws4_no_top_facing`, via `#(str x) < κ ≤ #carrier`), so it never depended on facing-injectivity cofinality.
6. **GroundlessDiagonal consistency + witness** — WS5. **PARTIAL.** Witness exhibited on the loop-spine (`omegaGroundlessDiagonal`); the *global* extension is refuted (`ws5_global_groundless_collapses` — Impossibility proved). Extending the endogenous bound to carry plurality off the spine remains the named residue.
7. **Blind-spot = diagonal equality** — WS6. **OPEN.** Both blind spots proved nonempty (`ws6_blindspot_nonempty` + `ws6_lawvere_incomplete`); their *equality* (A3) is downgraded to coexistence per the pre-registered fallback.
8. ~~**Distinctness ledger** — WS7.~~ **CLOSED** — `ws7_deductions_dont_collapse` (proper ≠ improper for one object): the payoffs are distinct consequences, verdict *one finitude, substantively*.
9. ~~**Machine-checked axiom pass** — all.~~ **CLOSED (this build)** — `AxiomCheck.lean` records all 34 headline theorems on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free. Cite commit hash + clean-build log in any publication.

**Residual opens (not blocking any discharged result):** #2 (general internal-rigidity), #6 (off-spine endogenous bound), #7 (blind-spot/diagonal equality); plus the Part C quantitative convergence characterization (the Series 3 replicator/pitchfork, not reproduced in this self-contained pass).

---

## Closed log

### WS1–WS7 reported — first full machine-checked pass (`series-4/formal/`)
- **Discharged:** WS1 (carrier + faces + inherited gate); WS2 Parts A/B/F1 and the F2 dichotomy; WS3 (labelled carrier, plurality, coincidence, unconditional composition-closure); WS4 (unconditional no-top wall, no-observer, positioned + substantive views, pole residue); WS6 A1/A2/B2/C; WS7 (one finitude with distinctness anchor; verdict = one finitude, substantively).
- **Impossibility proved (success):** WS2 collapse (atomless ∧ plural unsatisfiable on `νP_κ`); WS5 global-groundlessness collapse (the bound cannot be globally freed while keeping plurality); WS2 leak located exactly at ⊥-divisors.
- **Partial:** WS2 general internal-rigidity (heuristic under canonicity); WS5 endogenous bound (loop-spine only); WS6 A3 (blind spots coexist, equality open).
- **Deferred:** WS6 Part C quantitative convergence (Series 3 replicator/pitchfork; not reproduced in the self-contained pass).
- **Coincidence:** proved for WS3 (P3), WS4 (V1+V2); coexistence for WS6 A3.
- **Axiom check:** run against the pinned Lean 4.15.0 / Mathlib v4.15.0 build — 34 headline theorems, all on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free (`AxiomCheck.lean`).
- **Charter touched?** No — status-only. The charter design is unchanged; all shortfalls are stated as explicit hypotheses/typed structures, never relabelled as goals.

*Template for future entries:*

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
