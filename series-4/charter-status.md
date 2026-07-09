# Relational Existentialism — Series 4: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: in Series 3 the charter accumulated REV-A through REV-H amendments inline, until the design document and its change-log were the same polluted artifact. Series 4 keeps them apart. `charter.md` is the stable statement of intent and is edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds: what each workstream reported, what discharged, what reopened, what is owed. When you want to know "what does Series 4 claim," read the charter. When you want to know "where is Series 4," read this.*

---

## How to read this file

- **Status vocabulary** (from charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success) · **Partial** (part proved, obstruction made precise) · **Failed** (not achieved, documented why) · **Trivialized** (the WS7-only verdict: an elegant unification that turned out definitional — a success, not a failure) · **Not started**.
- **Coincidence status** (from charter §5, the coincidence rule): for each §5.3 payoff, whether the definitional form and an independently forced form were separately proved and shown to coincide. Values: **Coincidence proved** · **Definitional-only** (cheap form holds, forced form open) · **N/A** (payoff has no cheap form) · **Pending**.
- **Naming discipline** (inherited from Series 3 ws4/ws5): a bundle is named by its parts, never `*_resolved` / `series4_resolved`, while any hole remains.
- Every claim of "sorry-free / axiom-free" is provisional until a machine-checked `#print axioms` against a pinned Lean/Mathlib is recorded in the axiom-check row below. Static source audits are marked *(static)*. **As of this pass the axiom check is machine-run, not static** — see [`axiom-check-log.md`](./axiom-check-log.md).

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v1 — all seven workstreams reported and machine-checked |
| **Formalization** | `series-4/formal/ws1.lean … ws7.lean`, `Series4.lean`, `AxiomCheck.lean` — builds `sorry`-free, no custom axioms (**39** headline theorems on Mathlib's standard three only), **machine-verified** ([`axiom-check-log.md`](./axiom-check-log.md), Lean 4.15.0 / Mathlib v4.15.0). **Self-contained**: nothing imported from `archive/`. |
| **Central question** (charter §4) | **Answered, split.** No-top is a real wall: the endogenous face-routed form (`ws4_no_top_endogenous`) holds conditional on reach-properness (true at ℵ₀), the cardinal form unconditionally. The bound is endogenous on the loop-spine (WS5, Partial) but **globally** groundlessness collapses plurality (WS5, Impossibility) — so "grain, not wall" holds locally, not globally. |
| **Headline positive** | No-top-as-real-wall (WS4) ✓; plurality without atoms via internal faces (WS3) ✓; the two incompletenesses (WS6) ✓ |
| **Signature risk** | Trivialization — **refuted** on the mechanized anchor rows (WS7: one finitude, substantively; `ws7_deductions_dont_collapse` + `ws7_plurality_vs_collapse_distinct`); the full six-way anchor is the named open. Weak-pullback gate (WS1) — **non-event** on the R2 carrier. |
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
| Composition stays atom-free | `lcomp` + `ws3_faces_never_annihilate` | **Discharged (unconditional)** — a real composition/state-forming operator `lcomp` is built (via `corec` on `Option`); forming a composite from a nonempty structure of non-atomic states yields a non-atomic state whose successors are all non-atomic, with **no** `BotFree` hypothesis. *Stronger* than ws14, which leaked at nilpotent `Luk`. (The earlier lemma proved only loop-nonemptiness — now `ws3_loop_nonatomic`.) |

*Outcome:* the R3 escalation the design pre-registered is realized as a genuine, self-contained labelled carrier. The gate for `νLk` is a non-issue for the delivered results: loop-distinctness follows from `Cofix.dest` being a function (different `dest` ⇒ different state), so no separate weak-pullback proof is consumed. Composition is *unconditionally* atom-free — the optimistic sub-bet landed.
*Coincidence (for WS7):* P3's two halves (`ws2_collapse` on `νPk`, `ws3_loopface_ne` on `νLk`) are the same bare successor shape seen without and with faces.

### WS4 — No top, no view from nowhere  ·  *carries the facing-injectivity crux*
**Status: Discharged (unconditional wall).** · **Coincidence: proved** (V1+V2). Machine-checked in `series-4/formal/ws4.lean`.

| Obligation | Target | Status |
|---|---|---|
| Facing-injectivity | `FacingInjective` + `ws4_faces_inject` | **Discharged** (def + faces inject successors into sub-objects) |
| No-top, cardinal form | `ws4_no_top_cardinal` | **Discharged, unconditional** — the inherited Series 3 cardinality wall (`#(str x) < κ ≤ #carrier`). Honestly *not* face-derived. |
| No-top, endogenous (face-routed) form | `ws4_no_top_endogenous` | **Discharged, conditional** — proved *through faces*: facing everything ⇒ your faces cover the world ⇒ your reach = the world, contradicting `hreach` (your reach is a proper part). Conditioned on the endogenous premise `#reach x < #carrier` (true at ℵ₀; the continuum bound is deferred). This is the charter-strength self-cost wall. |
| No global observer | `ws4_no_global_observer` (V2) | **Discharged** (the same wall, observer-side) |
| View is positioned (definitional) | `ws4_view_is_positioned` (V1) | **Discharged** (every view is an object's face toward a successor) |
| Substantive standpoints | `ws4_substantive_standpoints` (V3) | **Discharged** (from WS3's distinct loops — free, not manufactured) |
| Pole-coincidence residue | `ws4_pole_coincidence_residue` | **Discharged** (`Ω↾(Ω,Ω) = ReachSet Ω`) |

*Outcome (corrected after blind review):* there are now **two** no-top theorems, honestly labelled. `ws4_no_top_cardinal` is the unconditional inherited cardinality wall (faces nowhere in its proof — the earlier "endogenous/`noResortToFiat`" label on it was drift, now removed). `ws4_no_top_endogenous` is the charter-strength wall: it routes through faces (`face_sub_reach`, `mem_face_self`) and `x`'s *own reach*, conditioned on the endogenous premise that a state's reach is a proper part of the world (`hreach`, true at ℵ₀). `FacingInjective` / `ws4_faces_inject` state the sharper "distinct faces" self-cost — whether facing is cofinally injective is the charter §9 crux, left open.
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
**Status: Partial (A1 scoped after blind review; A3 coexistence; Part C convergence deferred).** Machine-checked in `series-4/formal/ws6.lean`.

| Obligation | Target | Status |
|---|---|---|
| Self-face proper | `ws6_selfface_trivial` + `ws6_selfface_proper_nonselfrelating` (A1) | **Partial** — proved for the *non-self-relating* case only (there the self-face is empty, hence proper). Blind-review finding: the R2 self-face is provably **trivial** (`ws6_selfface_trivial`: empty or improper, never a nonempty proper part), so a nontrivial proper self-face for self-relating objects is unattainable on this carrier — the named open (needs the `∪{y}` face variant or an R3 self-model). |
| Lawvere diagonal (forced) | `ws6_lawvere_incomplete` (A2) | **Discharged** (Cantor diagonal on the support; no cardinality fact consumed) |
| **Coincidence: blind spot vs diagonal** | `ws6_blindspot_nonempty` (A3) | **Partial** — both blind spots proved *nonempty* (geometric + logical); their **equality** is the named open (obligation 7), delivered as coexistence per the pre-registered fallback |
| Ω non-termination (new) | `ws6_omega_nonterminating` (B2) | **Discharged** (complete in extent `face Ω Ω = ReachSet Ω`, yet self-membered `Ω ∈ str Ω` — closed at no depth) |
| Attention as face-thickening | `attend`, `selfModel`, `ws6_selfmodel_is_attention_fixedpoint` (C) | **Discharged (definitional)** — self-model = inward face = attention's fixed point |
| Convergence characterization | ws8/ws9 replicator over face-mass | **Deferred** — the quantitative Series 3 dynamics (pitchfork `μ⋆ = ½`) are not reproduced in this self-contained pass; the inherited-dynamics residue |

*Outcome:* the distinctive new result — B2, the on-diagonal non-termination — lands cleanly (the founding "self is a paradox" made a theorem). Two cruxes are honestly open: A3's blind-spot/diagonal *equality* (delivered as coexistence), and A1's proper self-face for *self-relating* objects (provably unattainable on the R2 derived face — `ws6_selfface_trivial`). Neither is laundered; both are stated as scope/open.

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Discharged — one finitude, substantively (anchor scoped to two mechanized rows).** Machine-checked in `series-4/formal/ws7.lean`.

| Obligation | Target | Status |
|---|---|---|
| The single finitude | `FinitudeOfFacing` + `ws7_finitude_of_facing` | **Discharged** (face proper off-diagonal, improper on it) |
| One-finitude reduction | `ws7_one_finitude` (T2) | **Discharged** (six payoffs assembled as consequences) |
| Distinctness anchor (makes T2 honest) | `ws7_deductions_dont_collapse` + `ws7_plurality_vs_collapse_distinct` (T3) | **Partial (scoped after blind review)** — mechanized for **two** rows: the incompleteness pair (proper vs improper, same object impossible) and the plurality/collapse pair (different carriers). The remaining pairwise rows are argued structurally, not mechanized; a full **six-way** anchor is the named open. |
| Verdict (typed) | `ProgramVerdict` + `ws7_verdict` + `ws7_not_trivialized` (T4) | **Discharged, scoped** — verdict is **one finitude, substantively**, earned by the two mechanized anchor rows; `Trivialized` remains a reachable typed alternative they refute |

*Verdict:* **one finitude, substantively** — with the distinctness anchor honestly scoped. It is *mechanized* for two rows (the incompleteness pair and the plurality/collapse pair) and *structural* for the rest; full six-way pairwise distinctness is the named open. The audit was genuinely capable of returning *Trivialized* — a typed constructor the mechanized anchors refute, not an absent option.
*Self-audit disclosure:* Claude-auditing-Claude — a disclosed limitation; T3 is the objective structural anchor.

---

## The five fractures / payoffs — headline tracker

*The charter's central question is whether restriction-quality heals, relocates, or relabels each. This table is the one-glance answer as it fills in.*

| Payoff (charter §5.3) | Workstream | Verdict: healed / relocated / definitional-only / failed | Coincidence |
|---|---|---|---|
| Plurality without atoms | WS3 | **Healed** (labelled carrier; distinct faces ⇒ distinct loops) | **Proved** (P3: collapse on `νPk`, split on `νLk`) |
| No top | WS4 | **Healed** — endogenous face-routed wall (`ws4_no_top_endogenous`) conditional on reach-properness (true at ℵ₀); cardinal wall (`ws4_no_top_cardinal`) unconditional | **Proved** (endogenous wall routes through faces + own reach, not the bare cap) |
| No view from nowhere | WS4 | **Healed** (same wall, observer-side) | **Proved** (V1 definitional + V2 forced) |
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
5. **Facing-injectivity cofinality (the endogenous no-top crux)** — WS4. **PARTIAL.** The endogenous face-routed wall `ws4_no_top_endogenous` is proved conditional on reach-properness `#reach x < #carrier` (true at ℵ₀; the continuum bound `#carrier > ℵ₀`, transcribable from Series 3 `ws12`, is deferred). The unconditional cardinal wall `ws4_no_top_cardinal` is inherited. Whether facing is *cofinally injective* (`FacingInjective`) — the sharper "distinct faces" self-cost — remains the charter §9 open crux.
6. **GroundlessDiagonal consistency + witness** — WS5. **PARTIAL.** Witness exhibited on the loop-spine (`omegaGroundlessDiagonal`); the *global* extension is refuted (`ws5_global_groundless_collapses` — Impossibility proved). Extending the endogenous bound to carry plurality off the spine remains the named residue.
7. **Blind-spot = diagonal equality** — WS6. **OPEN.** Both blind spots proved nonempty (`ws6_blindspot_nonempty` + `ws6_lawvere_incomplete`); their *equality* (A3) is downgraded to coexistence per the pre-registered fallback.
8. **Proper self-face for self-relating objects (A1 general)** — WS6. **OPEN.** `ws6_selfface_trivial` shows the R2 derived self-face is trivial (empty or improper), so a nontrivial proper self-face is unattainable on this carrier; needs the `∪{y}` face variant or an R3 self-model.
9. **Full six-way distinctness anchor** — WS7. **PARTIAL.** Mechanized for two rows (`ws7_deductions_dont_collapse`, `ws7_plurality_vs_collapse_distinct`); the remaining pairwise rows are structural, not mechanized. Verdict scoped accordingly.
10. ~~**Machine-checked axiom pass** — all.~~ **CLOSED (this build)** — `AxiomCheck.lean` records all **39** headline theorems on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free; the run is captured in [`axiom-check-log.md`](./axiom-check-log.md) against Lean 4.15.0 / Mathlib v4.15.0. Cite the commit hash + that log in any publication.

**Residual opens (not blocking any discharged result):** #2 (general internal-rigidity), #5 (facing-injectivity cofinality / unconditional endogenous no-top), #6 (off-spine endogenous bound), #7 (blind-spot/diagonal equality), #8 (self-relating proper self-face), #9 (six-way distinctness anchor); plus the Part C quantitative convergence characterization (the Series 3 replicator/pitchfork, not reproduced in this self-contained pass).

---

## Closed log

### Reconciliation pass — blind review `project-review-1.md` addressed
Charter-strength theorems attempted first per the executor rule; honest Partials where they provably resist. Charter untouched.
- **WS4 (no-top).** Charter-strength **met**: added `ws4_no_top_endogenous`, routing the wall through faces (`face_sub_reach`, `mem_face_self`) and `x`'s own reach, conditional on reach-properness. Renamed the old proof `ws4_no_top_cardinal` and stripped its false "endogenous / `noResortToFiat`" label. `FacingInjective`-cofinality is the remaining sharper crux.
- **WS3 (composition).** Charter-strength **met**: built a real state-forming operator `lcomp` (via `corec` on `Option`) and proved `ws3_faces_never_annihilate` at its intended meaning (composition of non-atomic states is non-atomic, unconditionally). The old loop-nonemptiness lemma is now `ws3_loop_nonatomic`.
- **WS6 (A1).** Primary **provably resisted**: `ws6_selfface_trivial` proves the R2 derived self-face is always empty or improper, so a nontrivial proper self-face is unattainable. Scoped `ws6_selfface_proper` → `ws6_selfface_proper_nonselfrelating`; A1 → Partial.
- **WS7 (anchor).** **Partial**: added a second mechanized distinctness row (`ws7_plurality_vs_collapse_distinct`); verdict scoped to the two mechanized rows, six-way anchor named open.
- **Axiom check.** Now **machine-run** (39 theorems), captured in `axiom-check-log.md`; the *(static)* qualifier is lifted.

### WS1–WS7 reported — first full machine-checked pass (`series-4/formal/`)
- **Discharged:** WS1 (carrier + faces + inherited gate); WS2 Parts A/B/F1 and the F2 dichotomy; WS3 (labelled carrier, plurality, coincidence, unconditional composition-closure); WS4 (unconditional no-top wall, no-observer, positioned + substantive views, pole residue); WS6 A1/A2/B2/C; WS7 (one finitude with distinctness anchor; verdict = one finitude, substantively).
- **Impossibility proved (success):** WS2 collapse (atomless ∧ plural unsatisfiable on `νP_κ`); WS5 global-groundlessness collapse (the bound cannot be globally freed while keeping plurality); WS2 leak located exactly at ⊥-divisors.
- **Partial:** WS2 general internal-rigidity (heuristic under canonicity); WS5 endogenous bound (loop-spine only); WS6 A3 (blind spots coexist, equality open).
- **Deferred:** WS6 Part C quantitative convergence (Series 3 replicator/pitchfork; not reproduced in the self-contained pass).
- **Coincidence:** proved for WS3 (P3), WS4 (V1+V2); coexistence for WS6 A3.
- **Axiom check:** run against the pinned Lean 4.15.0 / Mathlib v4.15.0 build — 39 headline theorems, all on `propext` / `Classical.choice` / `Quot.sound` only, `sorry`-free (`AxiomCheck.lean`, log in `axiom-check-log.md`).
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
