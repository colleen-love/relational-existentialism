# Relational Existentialism — Series 04: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: in Series 03 the charter accumulated REV-A through REV-H amendments inline, until the design document and its change-log were the same polluted artifact. Series 04 keeps them apart. `charter.md` is the stable statement of intent and is edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds: what each workstream reported, what discharged, what reopened, what is owed. When you want to know "what does Series 04 claim," read the charter. When you want to know "where is Series 04," read this.*

---

## How to read this file

- **Status vocabulary** (from charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success) · **Partial** (part proved, obstruction made precise) · **Failed** (not achieved, documented why) · **Trivialized** (the WS7-only verdict: an elegant unification that turned out definitional — a success, not a failure) · **Not started**.
- **Coincidence status** (from charter §5, the coincidence rule): for each §5.3 payoff, whether the definitional form and an independently forced form were separately proved and shown to coincide. Values: **Coincidence proved** · **Definitional-only** (cheap form holds, forced form open) · **N/A** (payoff has no cheap form) · **Pending**.
- **Naming discipline** (inherited from Series 03 ws4/ws5): a bundle is named by its parts, never `*_resolved` / `series4_resolved`, while any hole remains.
- Every claim of "sorry-free / axiom-free" is provisional until a machine-checked `#print axioms` against a pinned Lean/Mathlib is recorded in the axiom-check row below. Static source audits are marked *(static)*. **As of this pass the axiom check is machine-run, not static** — see [`axiom-check-log.md`](./spec/axiom-check-log.md).

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v1 — all seven workstreams reported and machine-checked |
| **Formalization** | `series-04/formal/Series04/ws1.lean … ws7.lean`, `series-04/formal/Series04.lean`, `series-04/formal/Series04/AxiomCheck.lean` — builds `sorry`-free, no custom axioms (**41** headline theorems on Mathlib's standard three only), **machine-verified** ([`axiom-check-log.md`](./spec/axiom-check-log.md), Lean 4.15.0 / Mathlib v4.15.0). Both series build under one `cd lake && lake build` (targets `Series04` + `Series05`); the Series 04 axiom pass is `lake build Series04 Series04.AxiomCheck`. **Self-contained**: nothing imported from `archive/`. |
| **Central question** (charter §4) | **Answered, split — and sharper after adversarial review.** No-top is a real wall but a **cardinal** one (`ws4_no_top_cardinal`); on R2 faces provably do *not* bound (review S2 + the WS5 M1/M2 negatives), so there is no endogenous face-counting wall. The bound is endogenous only on the loop-spine (WS5), and **globally** groundlessness collapses plurality (WS5, Impossibility). So "grain, not wall" is **not** achieved for bounding/positioning — faces do structural work for *plurality and composition*, not for *bounding*. That sharp localization is the real finding. |
| **Headline positive** | Parmenides collapse (WS2) ✓; plurality without atoms + unconditional composition-closure via internal faces (WS3) ✓; the coinductive incompleteness at Ω (WS6 B2) ✓; the global-groundlessness Impossibility (WS5) ✓. |
| **Signature risk** | Trivialization — refuted only on the two mechanized anchor rows; the "one finitude" reduction is **not** mechanized (review R1), so the verdict is downgraded (below). Weak-pullback gate (WS1) — **non-event** on the R2 carrier. |
| **Blocking item** | WS1 gate — **discharged** (inherited). |
| **Verdict (WS7)** | **`payoffsEstablished`** (`ws7_verdict`) — payoffs hold and are distinct where mechanized; their common origin in one finitude is argued, not mechanized. Not `oneFinitude`. |

---

## Workstream status

### WS1 — The world and its faces  ·  *blocking*
**Status: Discharged (R2 carrier).** · Carrier decision made: **R2** (derived intrinsic face on the self-contained `νPk κ` carrier). Machine-checked in `series-04/formal/Series04/ws1.lean`.

| Obligation | Target | Status |
|---|---|---|
| Face is forced, not annotated (lossiness thesis) | `ws1_face_forced` | **Discharged** (definitional; `face` is a function of `str` alone) |
| **The weak-pullback gate** (existential) | `ws1_weak_pullback_inherited` = `ws2_weak_pullback` | **Discharged** (inherited verbatim — R2 does not change the functor, so the gate never becomes a real obligation) |
| Ω recovered with improper self-face | `ws1_omega_face` | **Discharged** (`face Ω Ω = {Ω} = ReachSet Ω`) |
| Face is an internal sub-object | `face_sub_reach` | **Discharged** (`face x y ⊆ ReachSet x`) |

*Outcome:* the blocking existential gate is a non-event on R2, exactly as the design bet predicted — the carrier is a *reading* of the plain `νPk κ`, the face a derived operation, so weak-pullback preservation is inherited and criterion (iii) holds without re-proof. The whole carrier (terminal coalgebra of `P_κ` via QPF/`Cofix`, Lambek, `bisim_eq`, Ω) is reproduced self-contained in `ws1.lean`.
*Escalation watch:* WS3's plurality genuinely needs faces as independent data (faces on R2 are `str`-derived, hence epiphenomenal for distinguishing collapse-equal states). WS3 registers the R3 escalation as a typed obligation rather than reopening this row.

### WS2 — The collapse, and the forced answer  ·  *the spine*
**Status: Partial (as pre-registered).** Machine-checked in `series-04/formal/Series04/ws2.lean`. Parts A, B, F1 Discharged; F2 dichotomy proved with internal-rigidity conditional, exactly the charter §9 hedge.

| Obligation | Target | Status |
|---|---|---|
| Collapse Theorem | `ws2_collapse` (self-contained re-proof) | **Discharged** (Impossibility proved: atomless ∧ plural unsatisfiable on `νP_κ`) |
| Imported-weight leak, general form | `ws2_leak` (all ⊥-divisor `QAlg`) + `ws2_botfree_safe` (boundary) + `ws2_leak_witness` (concrete ⊥-divisor via `BotDivisorWitness`) | **Discharged** (leak located exactly at ⊥-divisibility; L3 false, so the escape is real) |
| Restriction introduces no leak | `ws2_restriction_no_leak` (F1) | **Discharged** (faces of atomless objects never empty — no internal zero) |
| **Forced-answer dichotomy** | `ws2_forced_answer` (F2) | **Discharged as a dichotomy** (external ⇒ leak-or-fiat; internal ⇒ no leak by F1). General internal-rigidity remains the named open (obligation 2). |

*Outcome:* the collapse is re-proved directly from `bisim_eq` (no dependence on the heavy Series 03 ws10 chain); the leak is stated as pure algebra over a minimal `QAlg`, needing no weighted terminal coalgebra. F2 delivers the dichotomy honestly: internality *forecloses* the leak rather than an external rule *forbidding* it.
*Exports for downstream:* `ws2_collapse` — WS3 cites it as the forced counterweight for its coincidence theorem; `carrier_card_ge` — WS4 consumes it for the no-top wall.

### WS3 — Plurality without atoms
**Status: Discharged.** · **Coincidence: proved** (P3). Machine-checked in `series-04/formal/Series04/ws3.lean`.

| Obligation | Target | Status |
|---|---|---|
| Central dichotomy: do faces distinguish beyond `str`? | paper-decidable | **Resolved: (I) on R2** — faces are `str`-derived; escalation to R3 taken. |
| R3 carrier built (self-contained) | `νLk κ Q` = `Cofix (X ↦ P_κ (Q × X))`, its `qpfLk` QPF instance, `loop_dest` | **Discharged** (labelled terminal coalgebra via QPF/`Cofix`, no dependency outside `series-04/formal/`) |
| Plurality witness (distinct faces) | `ws3_loopface_ne` (P1) | **Discharged** (distinct faces ⇒ distinct loops; the `ws14_loop_ne` analogue, by face not weight) |
| Coincidence: equal on `νPk`, distinct on `νLk` | `ws3_same_succ_diff_face` (P3) + `ws2_collapse` | **Discharged** (both halves, same bare successor shape) |
| Atomless plurality bundle | `ws3_plurality_core` (P4) + `ws3_plurality_core_concrete` | **Discharged** (two distinct non-atomic states; concrete at `Q = ULift Bool`) |
| Composition stays atom-free | `lcomp` + `ws3_faces_never_annihilate` | **Discharged (unconditional)** — a real composition/state-forming operator `lcomp` is built (via `corec` on `Option`); forming a composite from a nonempty structure of non-atomic states yields a non-atomic state whose successors are all non-atomic, with **no** `BotFree` hypothesis. *Stronger* than ws14, which leaked at nilpotent `Luk`. (The earlier lemma proved only loop-nonemptiness — now `ws3_loop_nonatomic`.) |

*Outcome:* the R3 escalation the design pre-registered is realized as a genuine, self-contained labelled carrier. The gate for `νLk` is a non-issue for the delivered results: loop-distinctness follows from `Cofix.dest` being a function (different `dest` ⇒ different state), so no separate weak-pullback proof is consumed. Composition is *unconditionally* atom-free — the optimistic sub-bet landed.
*Coincidence (for WS7):* P3's two halves (`ws2_collapse` on `νPk`, `ws3_loopface_ne` on `νLk`) are the same bare successor shape seen without and with faces.

### WS4 — No top, no view from nowhere  ·  *carries the facing-injectivity crux*
**Status: Relocated (no-top = cardinal wall; faces do not bound) + Partial (no-view: V1 definitional, V2 absent).** Corrected after adversarial review (`project-review-2.md`, S1/S2/R2). Machine-checked in `series-04/formal/Series04/ws4.lean`.

| Obligation | Target | Status |
|---|---|---|
| Facing-injectivity | `FacingInjective` + `ws4_faces_inject` | **Discharged** (def + faces inject successors into sub-objects) |
| No-top, cardinal form (the real wall) | `ws4_no_top_cardinal` | **Discharged, unconditional** — the inherited Series 03 cardinality wall (`#(str x) < κ ≤ #carrier`). This is what the no-top payoff actually rests on. |
| No-top, reachability restatement | `ws4_no_top_reach` | **Discharged, conditional — but faces do NO work** (review S2). Powered by `hreach` (`#reach x < #carrier`) via plain `Reaches.step`; the proof holds verbatim with faces stripped. Kept, honestly named, to *record* that faces do not bound here. (Was mislabelled `ws4_no_top_endogenous`.) |
| No global observer | `ws4_no_global_observer` | **Discharged (cardinal wall, observer-side)** — *not* a face-routed V2. |
| View is positioned (definitional) | `ws4_view_is_positioned` (V1) | **Discharged (definitional, `rfl`)** — a view is a face because "view" was defined as "face" (`ws4_observation_inhabited` shows it is not vacuous). |
| Real forced V2 (face-routed) | — | **Absent** (review R2) — and unavailable on R2, since faces do not bound. |
| Substantive standpoints | `ws4_substantive_standpoints` (V3) | **Discharged** (from WS3's distinct loops — free, not manufactured) |
| Pole-coincidence residue | `ws4_pole_coincidence_residue` | **Discharged** (`Ω↾(Ω,Ω) = ReachSet Ω`) |

*Outcome (corrected after adversarial review `project-review-2.md`):* the earlier "endogenous face-routed wall" claim was **overclaim** and is withdrawn. On the R2 carrier faces provably do *not* bound (this is exactly the WS5 M1/M2 negatives — faces tame quality, not branching), so no genuine face-counting no-top wall exists. `ws4_no_top_cardinal` is the real, unconditional wall; `ws4_no_top_reach` is a reachability restatement with faces painted on (kept as an honest record, not as an endogenous result). So no-top is **Relocated (cardinal wall)**, not Healed-as-endogenous.
*No-view (review R2):* the coincidence is **not** delivered. V1 (`ws4_view_is_positioned`) is `rfl` (definitional); a forced face-routed V2 does not exist (`ws4_no_global_observer` is the cardinal wall observer-side). So no-view is **Partial — V1 definitional, V2 absent**.

### WS5 — The self-bounding of the world  ·  *the "grain not wall" thesis*
**Status: Partial + Impossibility proved** (both pre-registered outcomes realized). Machine-checked in `series-04/formal/Series04/ws5.lean`.

| Obligation | Target | Status |
|---|---|---|
| M1 (contraction) as a **negative** | `ws5_contraction_insufficient` | **Discharged** (carrier still `≥ κ`; faces tame quality, not branching) |
| M2 (congruence collapse) as a **negative** | `ws5_quotient_insufficient` | **Discharged** (plurality survives same-face quotient — tames edges, not state-count) |
| **The global Impossibility** | `ws5_global_groundless_collapses` | **Impossibility proved** — global groundlessness ⇒ subsingleton; the bound *cannot* be globally freed while keeping plurality |
| M3 groundless-diagonal witness | `GroundlessDiagonal` + `omegaGroundlessDiagonal` | **Discharged** (the loop-spine `{Ω}` exhibited as a witness, not posited) |
| Endogenous bound (partial positive) | `ws5_endogenous_bound` + `ws5_omega_endogenous_point` | **Partial** — the bound is endogenous *on the loop-spine* (Ω groundless & improper-faced); extending it to carry plurality is the named residue |

*Outcome:* the central question is answered sharply at the global scale in the **negative** (`ws5_global_groundless_collapses`): you cannot make the whole world groundless and keep more than one thing in it. On the loop-spine the "grain, not wall" reading *does* hold (Ω's bound is its improper self-face, not a cap). So the bound is endogenous where the world is groundless (the diagonal) and imposed where it is plural — an honest split, exactly the pre-registered Partial.

### WS6 — The two incompletenesses  ·  *clearest expected win*
**Status: Partial (A1 scoped after blind review; A3 coexistence; Part C convergence deferred).** Machine-checked in `series-04/formal/Series04/ws6.lean`.

| Obligation | Target | Status |
|---|---|---|
| Self-face proper | `ws6_selfface_trivial` + `ws6_selfface_proper_nonselfrelating` (A1) | **Partial** — proved for the *non-self-relating* case only (there the self-face is empty, hence proper). Blind-review finding: the R2 self-face is provably **trivial** (`ws6_selfface_trivial`: empty or improper, never a nonempty proper part), so a nontrivial proper self-face for self-relating objects is unattainable on this carrier — the named open (needs the `∪{y}` face variant or an R3 self-model). |
| Lawvere diagonal (forced) | `ws6_lawvere_incomplete` (A2) | **Discharged** (Cantor diagonal on the support; no cardinality fact consumed) |
| **Coincidence: blind spot vs diagonal** | `ws6_blindspot_nonempty` (A3) | **Partial** — both blind spots proved *nonempty* (geometric + logical); their **equality** is the named open (obligation 7), delivered as coexistence per the pre-registered fallback |
| Ω non-termination (new) | `ws6_omega_nonterminating` (B2) | **Discharged** (complete in extent `face Ω Ω = ReachSet Ω`, yet self-membered `Ω ∈ str Ω` — closed at no depth) |
| Attention as face-thickening | `attend`, `selfModel`, `ws6_selfmodel_is_attention_fixedpoint` (C) | **Discharged (definitional)** — self-model = inward face = attention's fixed point |
| Convergence characterization | ws8/ws9 replicator over face-mass | **Deferred** — the quantitative Series 03 dynamics (pitchfork `μ⋆ = ½`) are not reproduced in this self-contained pass; the inherited-dynamics residue |

*Outcome:* the distinctive new result — B2, the on-diagonal non-termination — lands cleanly (the founding "self is a paradox" made a theorem). Two cruxes are honestly open: A3's blind-spot/diagonal *equality* (delivered as coexistence), and A1's proper self-face for *self-relating* objects (provably unattainable on the R2 derived face — `ws6_selfface_trivial`). Neither is laundered; both are stated as scope/open.

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Partial — verdict downgraded to `payoffsEstablished`** (adversarial review `project-review-2.md`, R1: the "one finitude" bundle is a conjunction, not a derivation from finitude). Machine-checked in `series-04/formal/Series04/ws7.lean`.

| Obligation | Target | Status |
|---|---|---|
| The single finitude | `FinitudeOfFacing` + `ws7_finitude_of_facing` | **Discharged** (face proper off-diagonal, improper on it) |
| Payoffs hold (a conjunction) | `ws7_payoffs_hold` (T2, was `ws7_one_finitude`) | **Discharged as a conjunction only** — six independently-proved payoffs conjoined. This does **not** show common origin; renamed to say only what it proves (review R1). |
| Derivation from finitude | `ws7_incompleteness_off_from_finitude` | **None mechanized (review-3 W1).** `FinitudeOfFacing` is *defined* as (off-diagonal properness) ∧ (Ω improper); this theorem's proof is `h.1`, so it **projects** the off-diagonal-properness conjunct the definition builds in — it is not a derivation of a payoff from an independent finitude. So *no* payoff is mechanically derived from a substantive single finitude; the reduction is argued in prose only. |
| Distinctness anchor | `ws7_deductions_dont_collapse` + `ws7_plurality_vs_collapse_distinct` (T3) | **Partial (review-3 W2).** `ws7_deductions_dont_collapse` proves the two incompleteness *predicates* are mutually exclusive (no object is at once improper- and proper-faced) — disjoint domains of application, **not** deduction-independence. `ws7_plurality_vs_collapse_distinct` is the one row with genuine distinctness force (two different carriers, `νLk` vs `νPk`). A full six-way anchor is the named open. |
| Verdict (typed) | `ProgramVerdict` + `ws7_verdict` + `ws7_verdict_eq` + `ws7_not_trivialized` (T4) | **`payoffsEstablished`** — *not* the stronger `oneFinitude` (would need every payoff derived from finitude), and *not* `Trivialized` (the anchors refute it). The honest middle. |

*Verdict:* **payoffs established; common origin in one finitude argued, not fully mechanized.** Per review R1, `ws7_payoffs_hold` is a conjunction (any six theorems can be conjoined), so "one finitude, *substantively*" is not earned at the Lean level. What is mechanized: the payoffs hold, and distinctness is anchored for two pairs (`ws7_plurality_vs_collapse_distinct` genuinely, on two carriers; `ws7_deductions_dont_collapse` as predicate-exclusivity — review-3 W2). *No* payoff is mechanically derived from a substantive finitude: `ws7_incompleteness_off_from_finitude` projects the off-diagonal-properness clause that `FinitudeOfFacing` is *defined* to contain (proof `h.1`, review-3 W1). The typed verdict is `payoffsEstablished`, honestly below `oneFinitude`.
*Self-audit disclosure:* Claude-auditing-Claude — a disclosed limitation; the mechanized anchors (T3) are the objective part.
*Self-audit disclosure:* Claude-auditing-Claude — a disclosed limitation; T3 is the objective structural anchor.

---

## The five fractures / payoffs — headline tracker

*The charter's central question is whether restriction-quality heals, relocates, or relabels each. This table is the one-glance answer as it fills in.*

| Payoff (charter §5.3) | Workstream | Verdict: healed / relocated / definitional-only / failed | Coincidence |
|---|---|---|---|
| Plurality without atoms | WS3 | **Healed** (labelled carrier; distinct faces ⇒ distinct loops) | **Proved** (P3: collapse on `νPk`, split on `νLk`) |
| No top | WS4 | **Relocated (cardinal wall); faces do not bound** — `ws4_no_top_cardinal` is the real wall; `ws4_no_top_reach` is a reachability restatement with faces inessential (review S2). The WS5 M1/M2 negatives explain why no face-counting wall exists. | N/A (no face coincidence) |
| No view from nowhere | WS4 | **Partial** — V1 (`ws4_view_is_positioned`) is definitional `rfl`; a forced face-routed V2 is absent (`ws4_no_global_observer` is the cardinal wall). | **Not delivered** (review R2) |
| Endogenous bound (grain not wall) | WS5 | **Relocated** — endogenous on the loop-spine; **globally impossible** while keeping plurality (Impossibility proved) | N/A |
| Incompleteness — blind spot | WS6 | **Partial** — Lawvere diagonal + proper self-face for *non-self-relating* objects; the R2 self-face is trivial (empty/improper), so the self-relating proper-self-face case is unattainable, open | **Coexistence** (blind-spot equality + self-relating case both open) |
| Incompleteness — non-termination | WS6 | **Healed** (Ω complete-yet-unclosed) | N/A (new, no cheap form) |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. Nothing here is hidden in prose; when an item closes, move it to the Closed log with the discharging theorem.*

1. ~~**Weak-pullback gate on the chosen carrier** — WS1.~~ **CLOSED** — `ws1_weak_pullback_inherited` (R2; the functor is unchanged, so the gate is inherited).
2. **General internal-rigidity for the forced-answer claim** — WS2. **OPEN.** The F2 dichotomy is proved; unconditional `Internal → IsRestrictionQuality` remains a defended heuristic (charter §9), delivered here under the canonicity witness (the reachable face + F1).
3. ~~**R3 carrier + its gate** — WS1/WS3.~~ **CLOSED** — the labelled carrier `νLk κ Q` (`Cofix (X ↦ P_κ (Q × X))`) is built self-contained; loop-distinctness needs no separate weak-pullback proof (it follows from `Cofix.dest` being a function).
4. ~~**Composition atom-freeness** — WS3.~~ **CLOSED** — a real state-forming operator `lcomp` + `ws3_faces_never_annihilate` (unconditional; internality leaves no external ⊥ to reach).
5. **Endogenous (face-counting) no-top wall** — WS4. **WITHDRAWN as unachievable on R2 (review S1/S2).** Faces provably do not bound here (the WS5 M1/M2 negatives: faces tame quality, not branching), so there is no genuine face-counting wall. `ws4_no_top_cardinal` (the cardinal wall) is the real, unconditional no-top; `ws4_no_top_reach` is a reachability restatement with faces inessential. No-top is **Relocated (cardinal wall)**. A face-routed wall would need a different (R3-style) carrier where faces are independent bounding data.
6. **GroundlessDiagonal consistency + witness** — WS5. **PARTIAL.** Witness exhibited on the loop-spine (`omegaGroundlessDiagonal`); the *global* extension is refuted (`ws5_global_groundless_collapses` — Impossibility proved). Extending the endogenous bound to carry plurality off the spine remains the named residue.
7. **Blind-spot = diagonal equality** — WS6. **OPEN.** Both blind spots proved nonempty (`ws6_blindspot_nonempty` + `ws6_lawvere_incomplete`); their *equality* (A3) is downgraded to coexistence per the pre-registered fallback.
8. **Proper self-face for self-relating objects (A1 general)** — WS6. **OPEN.** `ws6_selfface_trivial` shows the R2 derived self-face is trivial (empty or improper), so a nontrivial proper self-face is unattainable on this carrier; needs the `∪{y}` face variant or an R3 self-model.
9. **"One finitude" derivation + six-way distinctness anchor** — WS7. **PARTIAL (review R1; sharpened by review-3 W1/W2).** `ws7_payoffs_hold` is a conjunction, not a derivation from `FinitudeOfFacing`. Per review-3 W1, *no* payoff is mechanically derived from a substantive finitude: `ws7_incompleteness_off_from_finitude` projects the off-diagonal-properness conjunct that `FinitudeOfFacing` is *defined* to contain (proof `h.1`), not an independent derivation. Per review-3 W2, `ws7_deductions_dont_collapse` anchors predicate-exclusivity (disjoint domains), not deduction-independence; `ws7_plurality_vs_collapse_distinct` is the one genuine distinctness row. Verdict stays `payoffsEstablished`. Deriving *every* payoff from a single finitude, and a full six-way anchor, are open.
10. **Real face-routed V2 (no-view coincidence)** — WS4. **OPEN (review R2).** V1 is definitional `rfl`; a forced "unpositioned total view impossible, via faces" is absent and unavailable on R2 (faces do not bound). No-view is Partial.
11. ~~**Machine-checked axiom pass** — all.~~ **CLOSED (this build)** — `AxiomCheck.lean` records all **41** headline theorems on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free; captured in [`axiom-check-log.md`](./spec/axiom-check-log.md) against Lean 4.15.0 / Mathlib v4.15.0. Cite the commit hash + that log in any publication.

**Residual opens (not blocking any *correctly-labelled* result):** #2 (internal-rigidity), #5 (face-counting no-top — withdrawn on R2, needs R3), #6 (off-spine endogenous bound), #7 (blind-spot/diagonal equality), #8 (self-relating proper self-face), #9 ("one finitude" derivation + six-way anchor), #10 (face-routed V2); plus Part C quantitative convergence. **Pattern (the review's bottom line):** wherever the charter wanted faces to *bound / position / unify*, the Lean uses the cardinal fact or a `rfl` — faces cannot do that structural work on R2. Wherever faces genuinely work — *plurality, composition, collapse* — the results are solid and correctly labelled.

---

## Closed log

### Reconciliation pass 3 — adversarial review `project-review-3.md` addressed
Whole-program blind review (no SERIOUS findings). Two REAL relabels (W1, W2) and one reproducibility note (A1), applied faithfully — all relabel-or-note, no goalpost moves, verdict unchanged at `payoffsEstablished`. Charter untouched.
- **W1 — "one genuine derivation from finitude" is a projection, not a derivation.** `FinitudeOfFacing` is *defined* as (off-diagonal properness) ∧ (Ω improper), and `ws7_incompleteness_off_from_finitude`'s proof is `h.1` — it projects the off-diagonal-properness conjunct the definition already contains. Relabelled: *no* payoff is mechanically derived from a substantive single finitude (was "exactly one"). The payoff itself still holds (proved independently as `ws6_selfface_proper_nonselfrelating`); only the derivation gloss is corrected. WS7 table, verdict prose, and register #9 updated; verdict stays `payoffsEstablished` (already honest).
- **W2 — the distinctness anchor anchors predicates, not deductions.** `ws7_deductions_dont_collapse` proves `¬∃x. face x x = ReachSet x ∧ face x x ⊂ ReachSet x` — the two incompleteness *predicates* cannot co-apply to one state (disjoint domains), which is not the deduction-independence T3 wanted. Relabelled as predicate-exclusivity; `ws7_plurality_vs_collapse_distinct` (genuinely on two carriers, `νLk` vs `νPk`) kept as the one row that carries real distinctness force. The six-way anchor remains the named open.
- **A1 — axiom check made reproducible from a clean checkout.** The review noted `cd lake && lake build Series04 AxiomCheck` was no longer runnable because the live lakefile targeted Series 05 only. Resolved at the root: the lakefile now builds **both** series under one `cd lake && lake build` (each in its own module namespace, `Series04.*` / `Series05.*`), so the Series 04 axiom pass reproduces via `lake build Series04 Series04.AxiomCheck`. `spec/axiom-check-log.md`'s recorded build command updated to match.

### Reconciliation pass 2 — adversarial review `project-review-2.md` addressed
Corrections owed, applied faithfully (the review's own guidance: several are relabel, not fix — faces cannot do bounding/positioning work on R2). Charter untouched.
- **S1/S2 — no-top.** Overclaim withdrawn. The "endogenous face-routed wall" was a reachability wall with faces painted on; renamed `ws4_no_top_endogenous → ws4_no_top_reach`, re-proved via plain `Reaches.step` to make the point, and documented that faces do no work. No-top relabelled **Relocated (cardinal wall)**; the real wall is `ws4_no_top_cardinal`.
- **R1 — verdict.** `ws7_one_finitude → ws7_payoffs_hold` (it is a conjunction). Added `ws7_incompleteness_off_from_finitude` (then read as the one payoff derived from `FinitudeOfFacing`; **corrected in pass 3, W1** — its proof `h.1` projects a conjunct the definition builds in, so *no* payoff is derived from a substantive finitude). `ProgramVerdict` gains `payoffsEstablished`; `ws7_verdict` downgraded from `oneFinitude` to `payoffsEstablished`.
- **R2 — no-view.** Relabelled **Partial**: V1 is definitional `rfl`, a face-routed V2 is absent (`ws4_no_global_observer` is the cardinal wall observer-side). Added `ws4_observation_inhabited` (C1: V1 not vacuous).
- **R3 — left as-is** (already honestly Partial).
- **C2 — `Luk3 → BotDivisorWitness`**, `ws2_leak_Luk3 → ws2_leak_witness` (the gadget is not genuine Łukasiewicz).
- Build still `sorry`-free / axiom-clean (41 theorems); axiom log refreshed.

### Reconciliation pass — blind review `project-review-1.md` addressed
Charter-strength theorems attempted first per the executor rule; honest Partials where they provably resist. Charter untouched.
- **WS4 (no-top).** ~~Charter-strength met: added `ws4_no_top_endogenous`...~~ **[SUPERSEDED by pass 2]** — review S2 showed that theorem is a *reachability* wall with faces painted on; it was renamed `ws4_no_top_reach` and no-top relabelled **Relocated (cardinal wall)**. See pass 2 above.
- **WS3 (composition).** Charter-strength **met**: built a real state-forming operator `lcomp` (via `corec` on `Option`) and proved `ws3_faces_never_annihilate` at its intended meaning (composition of non-atomic states is non-atomic, unconditionally). The old loop-nonemptiness lemma is now `ws3_loop_nonatomic`.
- **WS6 (A1).** Primary **provably resisted**: `ws6_selfface_trivial` proves the R2 derived self-face is always empty or improper, so a nontrivial proper self-face is unattainable. Scoped `ws6_selfface_proper` → `ws6_selfface_proper_nonselfrelating`; A1 → Partial.
- **WS7 (anchor).** **Partial**: added a second mechanized distinctness row (`ws7_plurality_vs_collapse_distinct`); verdict scoped to the two mechanized rows, six-way anchor named open.
- **Axiom check.** Now **machine-run** (41 theorems), captured in `spec/axiom-check-log.md`; the *(static)* qualifier is lifted.

### WS1–WS7 reported — first full machine-checked pass (`series-04/formal/`)
- **Discharged:** WS1 (carrier + faces + inherited gate); WS2 Parts A/B/F1 and the F2 dichotomy; WS3 (labelled carrier, plurality, coincidence, unconditional composition-closure); WS4 (no-top wall [pass 2: = cardinal wall, Relocated], no-observer, positioned + substantive views, pole residue); WS6 A1/A2/B2/C; WS7 (payoffs + distinctness anchor; verdict [pass 2: downgraded to `payoffsEstablished`]). *[Rows marked [pass 2] were relabelled by the adversarial-review pass above.]*
- **Impossibility proved (success):** WS2 collapse (atomless ∧ plural unsatisfiable on `νP_κ`); WS5 global-groundlessness collapse (the bound cannot be globally freed while keeping plurality); WS2 leak located exactly at ⊥-divisors.
- **Partial:** WS2 general internal-rigidity (heuristic under canonicity); WS5 endogenous bound (loop-spine only); WS6 A3 (blind spots coexist, equality open).
- **Deferred:** WS6 Part C quantitative convergence (Series 03 replicator/pitchfork; not reproduced in the self-contained pass).
- **Coincidence:** proved for WS3 (P3), WS4 (V1+V2); coexistence for WS6 A3.
- **Axiom check:** run against the pinned Lean 4.15.0 / Mathlib v4.15.0 build — 41 headline theorems, all on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free (`AxiomCheck.lean`, log in `spec/axiom-check-log.md`).
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

*Distinct from workstream progress: this logs edits to `charter.md` itself. Per the Series 04 discipline, the charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress — progress lives above. Each entry: what changed in the charter, why it was a design error and not a status update, and the date.*

- **REV-0 (initial):** charter created; no changes yet. All seven workstream design docs drafted under `spec/wsN/design.md`.

---

*Status file v0. Maintained alongside `charter.md` (stable) and `spec/wsN/design.md` (per-workstream designs). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem; keep charter edits in the charter-change log and out of the workstream progress. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
