# Relational Existentialism — Series 6: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: the charter is the stable statement of intent, edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds. When you want to know "what does Series 6 claim," read the charter. When you want to know "where is Series 6," read this. (Series 4 introduced this split after Series 3 let REV-A…REV-H amendments pollute its charter inline; Series 5 and 6 keep the discipline.)*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success) · **Partial** (part proved, obstruction made precise) · **Failed** (not achieved, documented why) · **Trivialized** (the WS7-only verdict: the §5.5 unification turned out definitional — a success, a sharp negative about the conjecture) · **Not started**.
- **Design status** (Series 6 batches like Series 5): each workstream first reaches **Design committed** (a stable contract, no Lean) before any proof status. See `protocol.md` §2.
- **Coincidence status** (charter §7, the coincidence rule): for each §5.5 payoff, whether the definitional form and an independently forced form were separately proved and shown to coincide. Values: **Coincidence proved** · **Definitional-only** (cheap form holds, forced form open) · **N/A** (no cheap form) · **Pending**.
- **Strip-test discipline** (charter §7, inherited from Series 4/5 review): every payoff carries a strip test — delete the load-bearing word ("diagonal," "self-survey," "face," "later," "residue") and check whether the theorem still goes through as a bare fixed-point / cardinality / order fact. A payoff that survives the strip is such a fact honestly flagged, not an earned process theorem. The strip-test column is load-bearing for WS3/WS4/WS5/WS6/WS7.
- **Naming discipline** (inherited): a bundle is named by its parts, never `*_resolved` / `series6_resolved`, while any hole remains.
- Every claim of "sorry-free / axiom-clean" is provisional until a machine-checked `#print axioms` against the pinned Lean/Mathlib is recorded in `spec/axiom-check-log.md`. **No build exists yet** (the series has just been chartered).

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v0 — charter written (Phase A). Protocol written. No designs, no build. |
| **Design docs** | **Not started.** To be written as a batch under `series-6/spec/ws01…ws07-design.md` + `README.md` (protocol §2, Phase B). |
| **Formalization** | **Not started.** Target layout `series-6/formal/ws1.lean … ws7.lean`, `Series6.lean`, `AxiomCheck.lean`, self-contained (transcribe Series 4/5 machinery; import nothing from `series-5/`, `series-4/`, or `archive/`), pinned Lean/Mathlib per `lake/`. |
| **Central question** (charter §8) | **Open — the series has just been chartered.** Can a *process* be globally atomless and plural at once (the thing §3 proves no finished object can be), driven from within by the diagonal, with a directed endogenous arrow, and with the one-arrow-or-many question decided by the mathematics? None of this is built. |
| **Headline target (positive)** | A genuinely built, non-collapsing diagonal-driven process (WS1) that is **globally atomless and plural** (WS6, the achievement the Static Collapse forbids to any static object); the **engine identity** fixed-point-freeness = incompleteness = non-termination (WS3); the **endogenous arrow** (WS4); and the **relativity verdict** on `≺` decided by the two-sided face (WS5). |
| **Headline target (negative, first-class)** | The **Static Collapse Theorem** (WS2, Impossibility): no static globally-atomless construction is plural, subsuming Parmenides (S4) and the tower (S5). This is the motivating engine, as the Parmenides collapse and Explosion Dilemma were for S4/S5. |
| **Signature risk** | Trivialization — the diagonal *painted on* rather than driving (WS3), and the §5.5 unification a *conjunction* rather than one mechanism (WS6/WS7). The exact failure mode Series 3's attention and Series 5's grade-shift hit. Untested until built. |
| **Blocking item** | **WS1 gate** — the process must exist as a coherent, non-collapsing object with a plurality-keeping notion of sameness that carries the diagonal transition. Existential; settled first (charter §9). **Not started.** |
| **Verdict (WS7)** | **Not started.** Typed `ProgramVerdict ∈ { oneDiagonal, payoffsEstablished, Trivialized }` to be reported only after WS1–WS6. |

---

## Workstream status

*All seven are **Not started.** The rows below record the *pre-registered contract* — the target theorem names and outcome classes from the charter — so the design batch (Phase B) has explicit hooks. Theorem names are provisional design targets, not built artifacts.*

### WS1 — The process and its gate  ·  *blocking*
**Status: Not started.** · Carrier decision **open**: three candidate homes to adjudicate on a paper-decidable gate — **guarded recursion / topos of trees** (lead), **metric completion** (Lawvere-enriched, quality-as-distance), **pro-object / final-chain-without-limit**.

| Obligation | Target (provisional) | Status |
|---|---|---|
| The process exists as a genuine object | `ws1_process_exists` | Not started |
| Productive / non-terminating (well-defined) | `ws1_productive` | Not started |
| **The gate: sameness keeps plurality, does not collapse to limit identity** | `ws1_no_collapse` | Not started (existential — the most likely single point of failure) |
| Ω recovered as the self-knowing-that-never-closes | `ws1_omega_process` | Not started |

### WS2 — The Static Collapse, and the forced answer  ·  *the spine*
**Status: Not started.** · Breadth decision: **Broad** (charter §3.1 target) — any static behaviorally-identified fixed-point object, subsuming single carrier and colimit/tower.

| Obligation | Target (provisional) | Status |
|---|---|---|
| **Static Collapse Theorem (broad)** | `ws2_static_collapse` | Not started (Impossibility target) |
| Subsumes Parmenides (single carrier) | `ws2_subsumes_parmenides` | Not started |
| Subsumes the tower (colimit), diagnoses S5 open-#2 | `ws2_subsumes_tower` | Not started |
| Definition of "static" pinned | `ws2_static_def` | Not started (the definitional spine on which breadth rests) |
| Forced answer: dynamism is the escape | `ws2_forced_answer` | Not started (essential-uniqueness target; heuristic floor pre-authorized, charter §9) |

### WS3 — The engine: incompleteness as fuel
**Status: Not started.** · **Coincidence duty (signature crux):** the diagonal must *drive*, not be painted on.

| Obligation | Target (provisional) | Status · strip test |
|---|---|---|
| **Engine identity** fixed-point-free = incompleteness = non-termination = productive | `ws3_fpf_eq_incompleteness_eq_nontermination` | Not started · *strip "diagonal" — must lose its content* |
| Transition **is** the diagonal residue | `ws3_residue_is_successor` | Not started |
| Ω as the canonical non-terminating orbit | `ws3_omega_orbit` | Not started |
| Coincidence: the diagonal genuinely drives | `ws3_diagonal_drives` | Not started (Trivialized if unearned) |

### WS4 — The arrow: self-knowing gives directionality
**Status: Not started.** · **Strip test:** delete the external time index; a direction must remain.

| Obligation | Target (provisional) | Status · strip test |
|---|---|---|
| Self-survey lossy and proper (the past) | `ws4_survey_lossy` | Not started |
| Residue one-to-many (the future) | `ws4_residue_one_to_many` | Not started |
| Arrow strictly directional | `ws4_arrow_strict` | Not started |
| Arrow endogenous — no imported axis, no first moment | `ws4_arrow_endogenous` | Not started · *strip external time — direction must survive via proper-subobject order* |
| Coincidence: directionality from properness, not a counter | `ws4_arrow_from_properness` | Not started |

### WS5 — One arrow or many: the relativity crux  ·  *"let the math decide"*
**Status: Not started.** · The decidable theorem: is `≺` total (global time) or partial (relativity)?

| Obligation | Target (provisional) | Status · strip test |
|---|---|---|
| `≺` is a definite order | `ws5_precedes_order` | Not started |
| **Totality ⟺ cross-survey agreement** | `ws5_total_iff_agree` | Not started |
| Plurality forbids agreement (via two-sided face + §3) | `ws5_plurality_forbids_agreement` | Not started |
| `≺` is a genuine partial order, incomparability nonempty | `ws5_causal_partial_order` | Not started · *strip "face" — incomparability must not survive as a bare poset* |
| Global time is a frame (non-canonical linearization) | `ws5_global_time_is_frame` | Not started |
| **Branch:** Ω as absolute frame ⇒ total order (Newton) | `ws5_omega_absolute_frame` | Not started (pre-registered honest alternative) |
| **Ceiling:** order-plus-number ⇒ Lorentzian/causal-set metric | `ws5_lorentzian` | Not started (flagged heuristic; likely open) |

### WS6 — Globally atomless and plural, and the one-engine unification
**Status: Not started.** · Owns the headline achievement.

| Obligation | Target (provisional) | Status · coincidence |
|---|---|---|
| **Globally atomless AND plural (the achievement)** | `ws6_atomless_and_plural` | Not started (the success the Static Collapse forbids to any finished object) |
| Groundlessness from the diagonal (no completion ⇒ no atom) | `ws6_groundlessness_from_diagonal` | Not started |
| Plurality from the diagonal (each residue ⇒ new distinction) | `ws6_plurality_from_diagonal` | Not started |
| **Coincidence: one engine, not a conjunction** | `ws6_one_engine` | Not started (the reduction S4/S5 downgraded) |
| No view from nowhere (inhabited, not surveyed) | `ws6_no_view_from_nowhere` | Not started · *strip — must not reduce to "the limit does not exist"* |
| Inherited incompleteness transported, re-read as engine | `ws6_incompleteness_inherited` | Not started |

### WS7 — The anti-trivialization audit  ·  *owns the program verdict*
**Status: Not started.**

| Obligation | Target (provisional) | Status |
|---|---|---|
| The single incompletion | `ws7_one_incompletion` | Not started |
| Payoffs hold (a conjunction, honestly) | `ws7_payoffs_hold` | Not started |
| Genuine derivation from the one diagonal | `ws7_derivation_from_diagonal` | Not started |
| Distinctness anchors | `ws7_distinctness_anchors` | Not started |
| Strip-test ledger aggregated | `ws7_strip_ledger` | Not started |
| Typed verdict | `ProgramVerdict` + `ws7_verdict` | Not started (`oneDiagonal` / `payoffsEstablished` / `Trivialized`) |

---

## The §5.5 payoffs — headline tracker

*The charter's central question is whether the diagonal-driven process earns, relocates, or relabels each payoff. Nothing built yet; every row is Pending.*

| Payoff (charter §5.5) | Workstream | Verdict | Coincidence |
|---|---|---|---|
| Globally atomless AND plural (the achievement) | WS1, WS6 | Pending | N/A |
| Groundlessness and plurality from one engine | WS6 | Pending | Pending |
| Time directed and endogenous | WS4 | Pending | Pending |
| Time plural and relational (relativity) | WS5 | Pending | Pending (or N/A if `≺` total) |
| No view from nowhere (inhabited, not surveyed) | WS6 | Pending | Pending |
| Incompleteness inherited, re-read as engine | WS3, WS6 | Pending | N/A (inherited) |

---

## Open obligations register

*The single list of everything owed. Each item names its owner and its trigger-to-close. At Rev-0 these are the pre-registered cruxes and hazards from charter §5.6 / §9; the register fills in as work proceeds.*

1. **The WS1 gate** — WS1. **OPEN (blocking).** The process must exist as a coherent, non-collapsing object with plurality-keeping sameness that carries the diagonal transition. Trigger-to-close: `ws1_no_collapse` on a chosen carrier (guarded / metric / pro-object), with Ω recovered.
2. **Definition of "static" for the broad collapse** — WS2. **OPEN.** The breadth of `ws2_static_collapse` rests on a precise, non-circular definition of "static" (behavioral identity on a finished fixed-point object, covering colimits). Trigger-to-close: `ws2_static_def` + the two subsumption lemmas.
3. **The diagonal drives, not painted on (signature crux)** — WS3. **OPEN.** Trigger-to-close: `ws3_residue_is_successor` with the transition *definitionally* the residue, surviving the strip of "diagonal"; else **Trivialized**.
4. **The arrow is endogenous, no imported axis** — WS4. **OPEN.** Trigger-to-close: `ws4_arrow_endogenous` surviving the strip of the external time index (direction carried by the proper-subobject order).
5. **The relativity fork** — WS5. **OPEN.** Trigger-to-close: `ws5_total_iff_agree` + `ws5_plurality_forbids_agreement` ⇒ partial order (relativity), OR the honest `ws5_omega_absolute_frame` branch ⇒ total order (Newton). Either resolves the fork.
6. **Relativity not laundered** — WS5. **OPEN.** Trigger-to-close: incomparability in `ws5_causal_partial_order` earned from the two-sided face (fails the strip of "face"), not bare posethood.
7. **The Lorentzian ceiling** — WS5. **OPEN (heuristic, likely long-open).** Order-plus-number ⇒ metric (`ws5_lorentzian`). Flagged heuristic from the start; the bare causal order is the floor.
8. **One-engine unification vs conjunction** — WS6/WS7. **OPEN (signature risk).** Trigger-to-close: `ws6_one_engine` proving groundlessness and plurality the *same* mechanism; else the verdict is `payoffsEstablished`, not `oneDiagonal`.
9. **No view from nowhere earned** — WS6. **OPEN.** Trigger-to-close: `ws6_no_view_from_nowhere` from the inhabited/surveyed asymmetry, not "the limit does not exist" relabelled.
10. **Essential-uniqueness of the forced answer** — WS2. **OPEN (heuristic pre-authorized).** "Dynamism is *the* escape" as a theorem rather than a defended dichotomy (charter §9).
11. **Machine-checked axiom pass** — all. **OPEN.** No build yet; `AxiomCheck.lean` + `spec/axiom-check-log.md` owed once WS1–WS7 build.

**Residual opens at Rev-0:** all of the above — this is a freshly chartered series. **Pattern to watch (the program's recurring lesson):** wherever the charter wants the diagonal to do *unifying* work (one mechanism for groundlessness + plurality + time), expect the same pressure Series 4's "one finitude" and Series 5's "one double-unboundedness" met — a conjunction until proven otherwise. Wherever the diagonal does *local* work (drive the transition, direct the arrow, decide `≺`), expect it to be earnable. The design batch (Phase B) should pre-register that split.

---

## Closed log

*Empty. Entries land here as builds pass review, each with its discharging theorem.*

*Template for future entries:*

<!--
### [date] WSn reported — Status: {Discharged | Impossibility proved | Partial | Failed | Trivialized}
- Discharged: {theorems}
- Impossibility proved: {theorems, why they count as success}
- Open / routed: {obligation → owning workstream}
- Coincidence: {proved | definitional-only | N/A}
- Strip test: {which payoffs survived, which are bare fixed-point/order facts}
- Methodology note: {correction or hand-off, if any}
- Axiom check: {run against pinned build | static | owed}
- Charter touched? {no — status-only | yes, and why the design itself needed a fix}
-->

---

## Series-review log

*Series 6 batches review at the whole-series level (see `protocol.md` §2–§3): a review session reads all built code against all design contracts and charter criteria, blind to motivating prose, and writes `series-review.md`; a code session addresses it; repeat.*

- **Phase A (charter)** complete: `charter.md`, `charter-status.md` (this file), `protocol.md` written. No designs, no build, no review.

*Template:*

<!--
### [date] Series-review pass N — series-review.md written / addressed
- Findings raised: {S# serious, R# real, C# cosmetic}
- Addressed in build pass N: {what changed, relabel vs fix}
- Reopened workstreams: {WS#}
- Charter touched? {no — status-only}
-->

---

## Charter-change log

*Distinct from workstream progress: this logs edits to `charter.md` itself. The charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress. Each entry: what changed, why it was a design error and not a status update, and the date.*

- **REV-0 (initial):** charter created; no changes yet. Design docs (`spec/wsNN-design.md`) not yet drafted.

---

*Status file v0. Maintained alongside `charter.md` (stable), `protocol.md` (the process), and — once written — `spec/wsNN-design.md` (per-workstream designs). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem; keep review passes in the Series-review log and charter edits in the charter-change log, both out of the workstream progress. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
