# Relational Existentialism — Series 7: Charter Status

**The mutable companion to `charter.md`. All progress, revisions, per-workstream status, discharges, and open items live here — the charter itself stays clean.**

*Why this file exists: the charter is the stable statement of intent, edited only to fix errors in the design itself. This file absorbs everything that changes as work proceeds. When you want to know "what does Series 7 claim," read the charter. When you want to know "where is Series 7," read this. (The split is inherited from Series 4/5/6.)*

---

## How to read this file

- **Status vocabulary** (charter §7): **Discharged** (target proved) · **Impossibility proved** (sharp negative, counts as success — and here the *central* deliverable is one) · **Partial** (part proved, obstruction precise) · **Failed** (documented why) · **Circular** (the WS7-only verdict: the theorem holds only because its definitions excluded the escapes — a sharp negative about the result) · **Not started**.
- **Non-circularity status** (charter §7, replacing the coincidence rule): for each escape the theorem rules out, whether it is refuted as a *theorem* (the construction provably imports) or only excluded by a *definition*. Values: **Refuted-by-theorem** · **Excluded-by-fiat** (Circular for that escape) · **Pending**.
- **Strip-test discipline** (inherited): delete "atomless" / "plain" / "import" and check the theorem still goes through without a rigged definition. Load-bearing for WS3/WS5/WS7.
- Every claim of "sorry-free / axiom-clean" is provisional until a machine-checked `#print axioms` against the pinned Lean/Mathlib is recorded. **No build exists yet** (the series has just been chartered).

---

## Program-level snapshot

*Update this block whenever a workstream status changes.*

| | |
|---|---|
| **Charter revision** | REV-0 (charter design unchanged; the build confirmed it). |
| **This status file** | v1 — designs committed (Phase B) and the full build landed (Phase C). All seven `Series7/wsN.lean` + `Series7.lean` + `Series7/AxiomCheck.lean` compile, **sorry-free and axiom-clean** (standard three only; `spec/axiom-check-log.md`). Closure gate passes (self-contained; nothing imported across series). |
| **Design docs** | **Committed.** `spec/ws1…ws7-design.md` + `spec/readme.md` (moved into `spec/`). |
| **Formalization** | **Built.** `series-7/formal/Series7/ws1.lean … ws7.lean`, `Series7.lean`, `Series7/AxiomCheck.lean`. Self-contained. Pinned Lean 4 v4.15.0 / Mathlib v4.15.0. |
| **Central question** (charter §8) | **Answered — YES, non-circularly.** Atomless plurality is impossible without an import: (1) plain relating ∧ (2) behavioral identity ∧ (3) genuine every-moment atomlessness force ¬(4) plurality (`WS2.ws2_import_theorem`), driven by the general engine (`WS1.ws1_atomless_bisim`), recovering the static and dynamic collapses as instances. Non-circular (`WS2.ws2_non_circular`, `WS7.ws7_non_circularity_audit`). The one loophole (limit-atomlessness) is a genuine relaxation, adjudicated import-in-time (WS5). |
| **Headline result (Impossibility, a first-class success)** | **The Import Theorem** — proved and non-circular. The engine `ws1_atomless_bisim` generalizes every prior collapse (the "both-atomless" bisimulation on ANY plain coalgebra). The trichotomy of distinction (WS3) lands on a single coalgebra (Partial across "any construction"). The program is explained (WS4). The loophole isolated (WS5). |
| **Verdict (WS7)** | **`payoffsEstablished`** (`ws7_verdict_eq`, `rfl`). `nonCircular = true`, `stripHolds = true`, `trichotomyExhaustive = false` (exhaustiveness across "any construction" is the pre-registered Partial). `Circular` refuted (`ws7_not_circular`); the `Circular` arm is live (`ws7_circular_if_fiat`). `importForced` reachable if exhaustiveness lands (`ws7_import_forced_if_exhaustive`). |
| **Prior art (transcribed, not imported)** | The `P_κ`/bisimulation machinery + the process (`Approx`/`Proc`/`allNonempty_unique`/`ws1_productive_unique`) + `hneRel`/`hneRel_isBisim`/`Static`/`twoLoop`, all transcribed into `Series7/ws1.lean`, re-namespaced. The engine (WS1) is their generalization. |
| **Signature risk outcome** | **NOT Circular.** Behavioral identity IS the no-import predicate (`NoImportedAtom = BehaviorallyIdentified`, `Iff.rfl`); the escape is refuted as a theorem (the indexed loops are atomless-distinct-yet-bisimilar). Not a rigged "atomless". |
| **Only genuine open** | Trichotomy exhaustiveness across *any construction* (WS3, the un-rangeable quantifier — Partial, per charter §5.3); and the metric `CauchySeq` packaging of the loophole family (WS5, build-owed). Neither is a dependency of the Impossibility. |

---

## Workstream status

*All seven are **built** (`series-7/formal/Series7/wsN.lean`, sorry-free, axiom-clean). Theorem names below are the built artifacts. One realization choice, recorded once and routed to the WS1/WS4 designs: the heavy QPF carriers named in the designs (`νPk`, `νLk`/`loopState`, the tower `Winf`, the S3 weight algebra) are NOT re-transcribed; the identical structural facts are realized via the abstract `Static` (behavioral identity, subsuming `νPk`) and the minimal witness `twoLoop` (two indexed atomless self-loops, bisimilar-yet-unequal — the label/index import at its minimum). A faithful reframing (signatures met by theorem), not a retargeting.*

### WS1 — Atomless behavior is unique  ·  *blocking, the engine*
**Status: Discharged.**

| Obligation | Built theorem | Status |
|---|---|---|
| **General lemma: hne states bisimilar on any plain coalgebra** | `ws1_atomless_bisim` | **Discharged** (the "both-atomless" bisimulation, `hneRel_isBisim`) |
| Recovers the static collapse | `ws1_recovers_static` | **Discharged** (abstract `BehaviorallyIdentified` form, subsumes `νPk`) |
| Recovers the dynamic collapse | `ws1_recovers_dynamic` | **Discharged** (`ws1_productive_unique`, transcribed) |

### WS2 — The Import Theorem, and its non-circularity  ·  *the spine*
**Status: Impossibility proved (the deliverable) + non-circularity Discharged.**

| Obligation | Built theorem | Status |
|---|---|---|
| **The Import Theorem** (1∧2∧3 ⇒ ¬4) | `ws2_import_theorem` | **Impossibility proved** (the headline) |
| Static form / plurality requires a drop | `ws2_import_theorem_static`, `ws2_plurality_requires_drop` | **Discharged** |
| Dynamic instance (cited parallel) | `ws2_dynamic_instance` | **Discharged** |
| **Non-circularity**: escape refuted as a theorem | `ws2_non_circular`, `ws2_escapes_are_imports` | **Discharged** (NoImportedAtom = BehaviorallyIdentified; indexed loops import by theorem) |

### WS3 — The trichotomy of distinction  ·  *the teeth*
**Status: Discharged on a single coalgebra; exhaustiveness Partial across "any construction" (pre-registered).**

| Obligation | Built theorem | Status · strip test |
|---|---|---|
| Distinction on a single coalgebra is leaf or import | `ws3_dichotomy` | **Discharged** (`≠` in hypothesis, disjunction in conclusion — not the C2 trap; honest dichotomy after R1) |
| Atomless-distinct ⇒ import (consumes no-leaf hyp) | `ws3_atomless_distinct_is_import` | **Discharged** (engine-driven; genuinely uses `¬ LeafDiff`, after R2) |
| Third kind (leafy-thread) contentful, inhabited, collapses | `ws3_leafy_thread_inhabited`, `ws3_leafy_thread_collapses`, `ws3_no_same_limit_haecceity` | **Discharged** (on `Proc`; no longer a `False` placeholder, after R1; honestly a leafy-thread diff, with the same-limit haecceity witness structurally absent, after C2) |
| Three kinds genuinely distinct | `ws3_leaf_not_import`, `ws3_import_not_leaf` | **Discharged** (different extensions — not a partition) |

### WS4 — The imports catalogued: the program explained  ·  *the capstone unification*
**Status: Discharged (drop-1 + drop-2 mechanisms); full carriers + S3-weights Partial.**

| Obligation | Built theorem | Status |
|---|---|---|
| **drop (1)** — the label import SURVIVES the quotient | `ws4_labels_are_import`, `ws4_label_survives_quotient` | **Discharged** (labelled `labelLoop` on the non-plain functor: behaviorally identified yet plural; distinction survives the label-bisim quotient — a genuine drop of plainness, after S2/S3) |
| **drop (2)** — plain non-reduction | `ws4_toy_loop_is_drop2` | **Discharged** (`twoLoop`: atomless, plural, bisimilar-yet-unequal; a drop of behavioral identity — NOT equated with drop-1) |
| Levels are the S5 import (via index) | `ws4_levels_are_import` | **Discharged** (the index is a label — same drop-1 mechanism) |
| Weights (S3) / full `νLk`,`Winf` carriers | — | **Partial** — the drop mechanisms are mechanized on minimal witnesses; the full prior CARRIERS remain prior art, not re-transcribed. |
| The theorem predicts each drop | `ws4_program_explained` | **Discharged** (drop-1 + drop-2 witnessed + `ws2_plurality_requires_drop` predicts + S6 collapsed) |

### WS5 — The limit-atomlessness loophole  ·  *the one real escape*
**Status: Discharged (characterization + adjudication); metric family Partial (build-owed).**

| Obligation | Built theorem | Status · strip test |
|---|---|---|
| Limit-atomlessness reintroduces finite-stage leaves | `ws5_limit_reintroduces_leaves` | **Discharged** (a relaxation of (3), not a counterexample) |
| Leafy pair exists (honest: a PERMANENT atom) | `ws5_leafy_pair` | **Discharged** (Ω vs the atom; the atom is a permanent leaf, NOT limit-atomless, after R4) |
| Metric/Cauchy convergent family | — | **Partial** — the distinct-leafy-family-→-Ω `CauchySeq` packaging is build-owed (per S6's typed-but-unbuilt C4). |
| Adjudication: genuine escape or import-in-time (a RULING) | `ws5_loophole_adjudication`, `ws5_adjudication_justified`, `ws5_fork_is_genuine` | **Discharged — import-in-time** (a ruling on the horn-neutral theorem, not forced, after R5); `genuineEscape` retained terminal. |

### WS6 — The heuristic ceiling  ·  *the honest boundary*
**Status: Discharged (core); universal reported heuristic (pre-registered).**

| Obligation | Built theorem | Status |
|---|---|---|
| The provable core (coalgebras + process + trichotomy) | `ws6_provable_core` | **Discharged** |
| The universal "any construction" | `ws6_universal`, `ws6_universal_is_heuristic` | **Partial — heuristic** (defended thesis floored by the core, as S4/S5's forced answers) |

### WS7 — The anti-circularity audit  ·  *owns the verdict*
**Status: Discharged — verdict `payoffsEstablished`.**

| Obligation | Built theorem | Status |
|---|---|---|
| Non-circularity audited on REAL escapes (drop-1 survives quotient + drop-2) | `ws7_non_circularity_audit` | **Discharged** (`Iff.rfl` demoted to prose usage claim, after S4) |
| Kinds genuinely distinct (not a partition) | `ws7_kinds_distinct` | **Discharged** |
| Strip ledger — actual counterexample TERMS | `ws7_strip_ledger` (`leafCoalg`, `labelLoop`, `twoLoop`) | **Discharged** (contingent on the terms typechecking, after R3) |
| **Verdict wired to the audit certificate** | `Audit`, `ws7_audit`, `verdict`, `ws7_verdict_eq` | **`payoffsEstablished`** (`rfl`) — the verdict DEPENDS on the audit theorems; break one and it fails to build (after S1) |
| `Circular` arm live and tied to the audit | `ws7_audited_not_circular`, `verdictNoCertificate` | **Discharged** (with a certificate, never Circular; the only route to Circular is a failed audit) |

---

## The result tracker

*The charter's central question is whether the Import Theorem holds, non-circularly and exhaustively. Built verdict below.*

| Result (charter §5) | Workstream | Verdict | Non-circularity |
|---|---|---|---|
| Atomless behavior is unique (the lemma) | WS1 | **Discharged** (`ws1_atomless_bisim`) | N/A |
| The Import Theorem (1∧2∧3 ⇒ ¬4) | WS2 | **Impossibility proved** (`ws2_import_theorem`) | **Refuted-by-theorem** (`ws2_non_circular`) |
| Trichotomy exhaustive | WS3 | **Discharged (single coalgebra)** / **Partial** (any-construction) | Non-fiat (engine-driven) |
| Program explained (weights/labels/levels forced) | WS4 | **Discharged** (`ws4_program_explained`); S3-weights Partial | Refuted-by-theorem |
| Limit-atomlessness loophole | WS5 | **Discharged — import-in-time**; metric family Partial | N/A (a relaxation, not an escape) |
| Heuristic ceiling drawn | WS6 | **Discharged (core)** / **heuristic** (universal) | N/A |
| The typed verdict | WS7 | **`payoffsEstablished`** | Refuted-by-theorem; `Circular` refuted |

---

## Open obligations register

*The single list of everything owed. At Rev-0 these are the pre-registered cruxes and hazards from charter §5.5 / §9.*

1. **The general lemma** — WS1. **CLOSED.** `ws1_atomless_bisim` + both `recovers` corollaries.
2. **Non-circularity of the ingredients** — WS2/WS7. **CLOSED.** `ws2_non_circular` + `ws7_non_circularity_audit`: behavioral identity IS the no-import predicate; the escape refuted by theorem. Verdict NOT `Circular` (`ws7_not_circular`).
3. **Trichotomy exhaustiveness** — WS3. **PARTIAL (pre-registered, honest).** After pass-1 (R1/R2): on a single plain coalgebra the distinction is a genuine DICHOTOMY (`ws3_dichotomy`: leaf or import), and `ws3_atomless_distinct_is_import` genuinely consumes the no-leaf hypothesis; the third (intensional-history) kind is CONTENTFUL on the process (`ws3_history_kind_inhabited` + `ws3_history_kind_collapses`), no longer a `False` placeholder. Exhaustiveness across *any construction* stays the un-rangeable quantifier (charter §5.3) → verdict `payoffsEstablished` not `importForced`. The "no fourth kind / teeth" overclaim is withdrawn.
4. **The imports catalogued** — WS4. **CLOSED** (label/index/import phenomenon); **S3-weights Partial** (no S3-specific Lean witness transcribed; covered generically).
5. **The loophole adjudication** — WS5. **CLOSED — import-in-time.** `ws5_limit_reintroduces_leaves` forces the distinguisher to a finite-stage atom; `genuineEscape` retained as the terminal alternative if a future reviewer privileges the limit-as-object (headline would weaken to "impossible except in the limit").
6. **The universal quantifier** — WS6. **CLOSED as heuristic** (pre-authorized). `ws6_universal` a defended thesis floored by `ws6_provable_core`.
7. **Machine-checked axiom pass** — all. **CLOSED.** `Series7/AxiomCheck.lean` built; `spec/axiom-check-log.md` records every headline theorem sorry-free on the standard three.

**Residual opens after the build:** #3 (trichotomy exhaustiveness across *any construction* — the un-rangeable quantifier, genuinely Partial) and the metric `CauchySeq` packaging of the loophole family (WS5, build-owed). Neither is a dependency of the Impossibility; both are pre-registered honest Partials. **The program's recurring lesson, confirmed and turned into the deliverable:** the sharpest result is a proved impossibility. Series 7 makes the impossibility the whole point and it lands — non-circular (the risk that mattered), with the trichotomy's completeness the honest ceiling exactly where the charter placed it.

---

## Closed log

### 2026-07-10 Phase B+C — designs committed and the full build landed
- **Impossibility proved (the deliverable, a success):** `WS2.ws2_import_theorem` — no plain, behaviorally-identified, atomless coalgebra is plural. Driven by `WS1.ws1_atomless_bisim` (the "both-atomless" bisimulation on ANY plain coalgebra), the generalization that unifies the static (`ws2_collapse`) and dynamic (`ws1_productive_unique`) collapses.
- **Discharged:** WS1 the engine + both recovered instances; WS2 the static form, corollary, dynamic instance, and non-circularity (`ws2_non_circular`); WS3 `ws3_trichotomy` + `ws3_history_collapses` + exhaustiveness-on-a-single-coalgebra + the three-kinds-distinct witnesses; WS4 `ws4_import_witness`/`ws4_labels_are_import`/`ws4_levels_are_import`/`ws4_program_explained`; WS5 `ws5_limit_reintroduces_leaves`/`ws5_leafy_plurality` and the adjudication (`import-in-time`); WS6 `ws6_provable_core`; WS7 all anchors and the verdict.
- **Partial (obstruction precise, pre-registered):** WS3 exhaustiveness across *any construction* (the un-rangeable quantifier); WS4 S3-weights (no S3-specific Lean witness — the generic import witness covers it); WS5 the metric `CauchySeq` convergent family (build-owed); WS6 the universal (heuristic, defended thesis floored by the core).
- **Non-circularity:** Refuted-by-theorem throughout — `NoImportedAtom = BehaviorallyIdentified` (`Iff.rfl`), the escape refuted by `ws2_escapes_are_imports`. Verdict `payoffsEstablished`, NOT `Circular` (`ws7_not_circular`); the `Circular` arm is live (`ws7_circular_if_fiat`).
- **Strip test:** clean (`ws7_strip_ledger_clean`) — deleting "atomless"/"plain" exhibits real counterexamples; the import refuted by theorem, not fiat.
- **Realization note (routed to WS1/WS4 designs):** the heavy QPF carriers named in the designs (`νPk`, `νLk`/`loopState`, tower `Winf`, S3 weights) are NOT re-transcribed; the identical structural facts are realized via the abstract `Static` (subsuming `νPk`) and the minimal `twoLoop` witness (the label/index import at minimum). A faithful reframing — the signatures are met by theorem — not a retargeting. The design docs carry a BUILD/REALIZATION note; the Lean files carry it in headers.
- **Axiom check:** run (`spec/axiom-check-log.md`) — every headline theorem sorry-free on `propext` / `Classical.choice` / `Quot.sound`. Closure gate passes (self-contained).
- **Charter touched?** No — status-only. The build confirmed the charter's thesis.

---

## Series-review log

- **Phase A (charter)** complete: `charter.md`, `charter-status.md`, and the design batch written.
- **Phase B (design-all)** complete: `spec/ws1…ws7-design.md` + `spec/readme.md` (moved into `spec/`).
- **Phase C (build-all)** complete: all seven `Series7/wsN.lean` + `Series7.lean` + `Series7/AxiomCheck.lean` compile, sorry-free and axiom-clean; closure gate passes.
- **Phase D (blind review), pass 1** complete: `spec/project-review-1.md` — three adversarial reviewers, findings verified line-by-line. Core (the Import Theorem + its engine) confirmed genuine, non-vacuous, sorry-free; the interpretive layer flagged.
- **Phase E (address), pass 1** complete (2026-07-10). Every finding addressed under the executor discipline (prove-more-or-relabel, never lower the bar). Summary:
  - **S1 (verdict hand-set) — FIXED (proved).** The verdict is now a function of a mechanized `Audit` certificate (`WS7.Audit`, `ws7_audit`) whose every field is a theorem; `ws7_verdict` depends on it, so breaking any audit content breaks the build. The `Circular` arm is genuinely tied to the certificate's existence (`ws7_audited_not_circular`: with a certificate, never Circular).
  - **S2/S3 (WS4 mechanizes nothing / wrong mechanism) — FIXED (proved a genuine drop-1).** A labelled coalgebra `WS4.labelLoop` on the NON-plain functor `P_κ(Q×X)` whose distinction SURVIVES the label-bisimulation quotient (`ws4_label_survives_quotient`) — behaviorally identified yet plural, a genuine drop of plainness (1), distinct from `twoLoop`'s drop-(2) non-reduction. The two mechanisms are no longer equated. `twoLoop` relabelled `ws4_toy_loop_is_drop2`. Honest scope: the full `νLk`/`Winf`/weight CARRIERS remain prior art, not re-transcribed.
  - **S4 (non-circularity vacuous) — FIXED.** NC1 (`Iff.rfl`) demoted to a prose usage claim (not a counted anchor); the audit now rests on the real drop-1 label escape + drop-2 refutation, both theorems. The mislabelled "tower drops atomlessness" conjunct removed.
  - **R1/R2 (dichotomy in trichotomy vocabulary) — FIXED (relabel + contentful third kind).** `ws3_trichotomy → ws3_dichotomy` (honest, single coalgebra); `ws3_trichotomy_exhaustive → ws3_atomless_distinct_is_import` (now consumes its no-leaf hypothesis); `HistoryDiff` made contentful on `Proc`, inhabited + collapsing.
  - **R3 (self-fulfilling Bool ledger) — FIXED (real terms).** `ws7_strip_ledger` now carries actual counterexample terms — a behaviorally-identified plural coalgebra WITH a leaf (`WS7.leafCoalg`, `leafCoalg_behav`), the labelled carrier, and `twoLoop`.
  - **R4/R5 (WS5 framing) — FIXED (scope/prose).** `ws5_leafy_plurality → ws5_leafy_pair`, honestly stating `emptyProc` is a PERMANENT atom (not limit-atomless); the convergent metric family stays Partial. The import-in-time adjudication is stated as a RULING, not forced.
  - **R6 (IsImportWitness vacuous) — FIXED (removed).** The empty `IsImportWitness` predicate is gone; WS4 now uses the genuine drop-1/drop-2 statements.
  - **C1/C2 (framing) — acknowledged.** Series 7's delta over Series 6 is honestly a reframing + the general bisimilarity lemma; the "live importForced arm" is gated on the open exhaustiveness flag and not implied to be near.
  Full build re-verified sorry-free, axiom-clean; gate passes.
- **Phase D (blind review), pass 2 — CLEAN, exit criterion met** (`spec/project-review-2.md`, against commit `cdf26d3`): four reviewers (two fix-validators, two fresh from-scratch, one tasked solely with building a counterexample). **No SERIOUS finding remains.** All four pass-1 SERIOUS items independently confirmed genuinely fixed at the term level (S1 fully; S3/S4 fully; S2 re-scoped to an honest Partial); the fresh from-scratch attack could not build a counterexample to the Import Theorem and confirmed *why* (the genuine unlabelled-powerset collapse, not a rigged `IsBisim`); AxiomCheck coverage confirmed to omit none of the load-bearing headlines. Recommendation: **Series 7 closes at `payoffsEstablished`, earned.**
- **Phase E (address), pass 2** complete (2026-07-10). Only cosmetic/terminal items (C1–C4) — all relabels/removals, **no mathematics changed**, verdict unchanged:
  - **C1 — `ws4_levels_are_import → ws4_index_reuses_label_mechanism`.** Renamed (it reuses the label mechanism, never touches `Winf`) and STRENGTHENED to carry the full survives-quotient conjunct.
  - **C2 — `HistoryDiff → LeafyThreadDiff`** (and `ws3_history_kind_* → ws3_leafy_thread_*`): honestly a leafy-thread (leaf) difference, not the design's same-limit haecceity kind. Added `ws3_no_same_limit_haecceity` recording the genuine haecceity witness as **structurally absent** (any two productive threads are equal) — a named open, the sharpest statement of what the program has circled and arguably the seed of a Series 8.
  - **C3 — wording downgrade.** `labelLoop`'s ingredient-(3) is the minimal first-level-nonempty witness, not hereditary; docstring corrected ("atomless" → "first-level nonempty").
  - **C4 — dead scaffolding removed** (`Static`/`HereditarilyAtomless`/`GenuinelyAtomless`, unused); `verdictNoCertificate` docstring softened (the load-bearing content is `ws7_audited_not_circular`).
  Full build re-verified sorry-free, axiom-clean (37 headline theorems, standard three); gate passes.
- **Phase D (blind review), pass 3 — ALIGNMENT-to-charter** (`spec/project-review-2.md`, updated after digging in): a single reviewer graded whether the proved theorems are theorems about the *right object* — the one dimension a term-level audit structurally cannot catch. It disputes no proof and no axiom; it found the build **conflated "labelled" (a `Q` in the signature) with "imported" (the charter's §4.1 "coordinate NOT carried by the relating")**, and that the conflation reaches WS4's catalogue and WS7's audit. This is a genuine, correct finding.
- **Phase E (address), pass 3** complete (2026-07-10). Addressed charter-strength-first (prove the real predicate; re-classify honestly; never a relabelled charter target):
  - **S1/R3 (syntactic vs semantic import) — FIXED (proved the charter-strength predicate).** Added the SEMANTIC import test: `ws4_free_label_is_import` — the plain, label-forgetting relating cannot recover the label (`plainOf`; plain-bisimilar states) yet the label distinguishes (no label-bisimulation relates them), so it is a coordinate *not carried by the relating* (§4.1), not merely "a label in the signature". And `ws4_recoverable_not_import`: a recoverable label (plain-bisimilar ⇒ label-bisimilar) is NOT an import.
  - **S2/R1/R2 (the S4 restriction is not an import) — FIXED (re-classified honestly).** The Series 4 face `x↾(x,y)` is a restriction of the relatum, hence recoverable, hence by `ws4_recoverable_not_import` **NOT an import** — it is a leaf / **faced boundary** (a descent boundary that also carries a quality). Series 4 reached plurality only by ESCALATING the restriction into a FREE label (`loopState q`), which IS a genuine import; the two objects are different, keeping one name. `ws4_program_explained` and its realization note are corrected: the program is explained *for free-label imports*; the endogenous S4 (and possibly S5) cases are recoverable, reclassified. WS3 records the **faced boundary as the candidate FOURTH kind** (`ws3.lean` note) — reducing it to leaf-or-import is the load-bearing open, NOT assumed; it is pass-2's haecceity seen from the label side. The faithfulness gap (minimal free-label witness ≠ the S4 restriction) is now disclosed, not just the coverage gap.
  - **S3 (audit certified the wrong predicate) — FIXED.** `ws7_non_circularity_audit` and `Audit.nonCircular` now consume the SEMANTIC import (`ws4_free_label_is_import`), so the audit certifies against the charter's predicate. Honestly SCOPED: it certifies that genuine free-label imports exist and are non-circular; it does NOT certify that the S4 restriction is an import (it is not). The prior-series catalogue is re-scoped, not certified.
  - **C1/C2 (framing) — acknowledged / propagated** in the docstrings and summaries.
  **Verdict scope, made precise (the honest outcome pass 3 asks for):** the **plain collapse** — the Import Theorem `ws2_import_theorem` and its engine — stays `payoffsEstablished`, untouched and attack-tested. The **free-label import mechanism** is now witnessed at charter strength (semantic). The **prior-series catalogue** (WS4) is honestly **re-classified / Partial**: only free-label imports are certified as imports; the Series 4 restriction is a leaf/faced-boundary, and its plurality is a free-label escalation. The **faced boundary** is a named candidate fourth kind (open). No charter target was relabelled; the charter's §4.1 semantic definition was the fixed bar the build is now aligned to.
  Full build re-verified sorry-free, axiom-clean (38 headline theorems, standard three); gate passes.

---

## Charter-change log

*Distinct from workstream progress: this logs edits to `charter.md` itself. The charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress.*

- **REV-0 (initial):** charter created; no changes yet. Series 7 seeded from Series 6's honest finding (the process collapse, `ws1_productive_unique`) per the program's inter-series discipline (protocol §6): the prior series' hardest pushback becomes the next series' question. Series 6 is **not** rewritten — it stays the honest record of the dynamism attempt; Series 7 is the standalone impossibility that generalizes it.

---

*Status file v0. Maintained alongside `charter.md` (stable). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
