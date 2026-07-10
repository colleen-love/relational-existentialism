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
| **Charter revision** | REV-0 (charter design unchanged) |
| **This status file** | v0 — charter written (Phase A). No protocol yet (inherits Series 6's), no designs, no build. |
| **Design docs** | **Not started.** To be written as a batch under `series-7/spec/ws01…ws07-design.md` + `README.md`. |
| **Formalization** | **Not started.** Target `series-7/formal/Series7/ws1…ws7.lean`, `Series7.lean`, `AxiomCheck.lean`, self-contained (transcribe the `P_κ` / bisimulation machinery from Series 4/6; import nothing across series), pinned Lean/Mathlib. |
| **Central question** (charter §8) | **Open — the series has just been chartered.** Is atomless plurality impossible without an import? Precisely: do (1) plain relating, (2) behavioral identity, and (3) genuine every-moment atomlessness jointly force the negation of (4) plurality — non-circularly, and exhaustively (every distinction a leaf, an import, or a collapsing history)? None of this is built. |
| **Headline target (negative, first-class)** | **The Import Theorem** (WS2, Impossibility): 1∧2∧3 ⇒ ¬4. Every plural relational world drops exactly one of (1)–(3); the drop is its price. This is the deliverable — a proved impossibility, as the Parmenides collapse and Explosion Dilemma were for their series. |
| **Headline target (unification)** | The program explained (WS4): weights (S3), labels (S4), levels (S5) each the *forced* ingredient-1 drop of their series; Series 6's process the drop that failed (collapsed). The capstone reading of 3→4→5→6. |
| **Strong prior art (transcribe / generalize, do not presuppose)** | `ws2_collapse` / `ws5_global_groundless_collapses` (Series 4 — the static instance); `ws1_productive_unique` / `ws1_no_productive_plurality` (Series 6 — the dynamic instance). The general lemma (WS1) is their common root; both are already machine-checked, so WS1/WS2 start from a strong base. |
| **Signature risk** | **Circularity** — the theorem true only because "genuinely atomless / no import" was defined to exclude the escapes. Not trivialization (Series 6's risk) but tautology. Untested until built; WS7 owns it. Secondary: the trichotomy (WS3) may not be exhaustive. |
| **Blocking item** | **WS1 general lemma** — atomless behavior is unique on any plain `P_κ`-coalgebra (the "both-atomless" bisimulation). The engine; settled first. **Not started.** |
| **Verdict (WS7)** | **Not started.** Typed `ProgramVerdict ∈ { importForced, payoffsEstablished, Circular }`, reported only after WS1–WS6. Predicted: `importForced` if non-circularity + trichotomy land; `payoffsEstablished` if the trichotomy or the universal stays partial; `Circular` if the escapes are only excluded by fiat. |

---

## Workstream status

*All seven are **Not started.** The rows record the pre-registered contract — the target theorem names and outcome classes from the charter — so the design batch has explicit hooks. Names are provisional design targets, not built artifacts.*

### WS1 — Atomless behavior is unique  ·  *blocking, the engine*
**Status: Not started.** · Strong prior art: `ws2_collapse` (S4), `ws1_productive_unique` (S6) are the two instances this lemma unifies.

| Obligation | Target (provisional) | Status |
|---|---|---|
| **General lemma: hne states bisimilar on any plain coalgebra** | `ws1_atomless_bisim` | Not started (the "both-atomless" bisimulation) |
| Recovers the static collapse as an instance | `ws1_recovers_static` | Not started (from `ws2_collapse`) |
| Recovers the dynamic collapse as an instance | `ws1_recovers_dynamic` | Not started (from `ws1_productive_unique`) |

### WS2 — The Import Theorem, and its non-circularity  ·  *the spine*
**Status: Not started.**

| Obligation | Target (provisional) | Status |
|---|---|---|
| **The Import Theorem** (1∧2∧3 ⇒ ¬4) | `ws2_import_theorem` | Not started (Impossibility target) |
| Plurality requires dropping an ingredient | `ws2_plurality_requires_drop` | Not started |
| **Non-circularity**: escapes refuted as theorems | `ws2_non_circular` | Not started (νLk carries a label, tower an index — by theorem, not fiat) |
| Ingredients independently motivated | `ws2_ingredients_motivated` | Not started (1, 2 are the program's founding commitments) |

### WS3 — The trichotomy of distinction  ·  *the teeth*
**Status: Not started.** · **Coincidence/exhaustiveness duty:** the three kinds distinct and jointly exhaustive, not a definitional partition.

| Obligation | Target (provisional) | Status · strip test |
|---|---|---|
| Every distinction is leaf / import / history | `ws3_trichotomy` | Not started |
| Intensional history collapses under atomlessness | `ws3_history_collapses` | Not started (transcribe `ws1_productive_unique`) |
| The trichotomy is exhaustive (no fourth kind) | `ws3_trichotomy_exhaustive` | Not started · *the hardest open; a fourth kind demotes to collapse-plus-examples* |

### WS4 — The imports catalogued: the program explained  ·  *the capstone unification*
**Status: Not started.** · Interpretive spine; light Lean, heavy unification.

| Obligation | Target (provisional) | Status |
|---|---|---|
| Weights are the Series 3 import | `ws4_weights_are_import` | Not started |
| Labels/faces are the Series 4 import | `ws4_labels_are_import` | Not started (via `ws3_plurality_core` factoring through `Q`) |
| Levels are the Series 5 import | `ws4_levels_are_import` | Not started (via the tower index) |
| The theorem predicts each drop | `ws4_program_explained` | Not started (the recurring honest negative *was* this theorem) |

### WS5 — The limit-atomlessness loophole  ·  *the one real escape*
**Status: Not started.** · Pre-registered fork; either verdict terminal.

| Obligation | Target (provisional) | Status · strip test |
|---|---|---|
| Limit-atomlessness reintroduces finite-stage leaves | `ws5_limit_reintroduces_leaves` | Not started (so it relaxes ingredient 3, not a counterexample) |
| The metric/Cauchy route carries transient atoms | `ws5_metric_transient_atoms` | Not started |
| Adjudication: genuine escape or import-in-time | `ws5_loophole_adjudication` | Not started (honest fork; either terminal) |

### WS6 — The heuristic ceiling  ·  *the honest boundary*
**Status: Not started.**

| Obligation | Target (provisional) | Status |
|---|---|---|
| The provable core (coalgebras + process + trichotomy) | `ws6_provable_core` | Not started |
| The universal "any construction" | `ws6_universal` | Not started (attempt; report heuristic if it resists) |

### WS7 — The anti-circularity audit  ·  *owns the verdict*
**Status: Not started.**

| Obligation | Target (provisional) | Status |
|---|---|---|
| Non-circularity audited (escapes refuted, not excluded) | `ws7_non_circularity_audit` | Not started |
| Trichotomy is not a definitional partition | `ws7_trichotomy_not_definitional` | Not started |
| Typed verdict | `ProgramVerdict` + `ws7_verdict` | Not started (`importForced` / `payoffsEstablished` / `Circular`) |

---

## The result tracker

*The charter's central question is whether the Import Theorem holds, non-circularly and exhaustively. Nothing built yet; every row Pending.*

| Result (charter §5) | Workstream | Verdict | Non-circularity |
|---|---|---|---|
| Atomless behavior is unique (the lemma) | WS1 | Pending | N/A |
| The Import Theorem (1∧2∧3 ⇒ ¬4) | WS2 | Pending | Pending |
| Trichotomy exhaustive | WS3 | Pending | Pending |
| Program explained (weights/labels/levels forced) | WS4 | Pending | Refuted-by-theorem (target) |
| Limit-atomlessness loophole | WS5 | Pending | N/A (a relaxation, not an escape) |
| Heuristic ceiling drawn | WS6 | Pending | N/A |

---

## Open obligations register

*The single list of everything owed. At Rev-0 these are the pre-registered cruxes and hazards from charter §5.5 / §9.*

1. **The general lemma** — WS1. **OPEN (blocking).** `ws1_atomless_bisim` on any plain `P_κ`-coalgebra; recover both instance-collapses. Trigger-to-close: the "both-atomless" bisimulation + the two `recovers` corollaries.
2. **Non-circularity of the ingredients** — WS2/WS7. **OPEN (signature risk).** The escapes must be refuted as theorems (νLk imports a label, tower an index), the ingredients shown independently motivated. Trigger-to-close: `ws2_non_circular` + `ws7_non_circularity_audit`; else the verdict is `Circular`.
3. **Trichotomy exhaustiveness** — WS3. **OPEN (hardest).** No fourth kind of distinction. Trigger-to-close: `ws3_trichotomy_exhaustive`; a candidate fourth kind that resists classification demotes the impossibility to collapse-plus-examples (honest Partial).
4. **The imports catalogued** — WS4. **OPEN.** Weights/labels/levels each the forced ingredient-1 drop. Trigger-to-close: the three `_are_import` lemmas + `ws4_program_explained`.
5. **The loophole adjudication** — WS5. **OPEN (fork).** Limit-atomlessness a genuine escape or import-in-time. Either verdict terminal; if genuine, the headline weakens to "impossible except in the limit."
6. **The universal quantifier** — WS6. **OPEN (heuristic pre-authorized).** "Any construction faithful to relating" formalizable, or a defended thesis (charter §5.3).
7. **Machine-checked axiom pass** — all. **OPEN.** No build yet; `AxiomCheck.lean` + `spec/axiom-check-log.md` owed once WS1–WS7 build.

**Residual opens at Rev-0:** all of the above — a freshly chartered series, but one that starts from a strong base: both instance-collapses (`ws2_collapse`, `ws1_productive_unique`) are already machine-checked prior art, so the engine (WS1) is a generalization rather than a fresh proof, and the genuinely new work is the abstraction (WS1), the non-circular theorem (WS2), the trichotomy (WS3), the unification (WS4), and the loophole (WS5). **Pattern to watch:** the program's recurring lesson is that the sharpest result is a proved impossibility; Series 7 makes the impossibility the whole point, so the risk shifts from "does the construction escape" (it doesn't) to "is the impossibility genuine or definitional" (WS7's circularity audit).

---

## Closed log

*Empty. Entries land here as builds pass review, each with its discharging theorem.*

---

## Series-review log

- **Phase A (charter)** complete: `charter.md`, `charter-status.md` (this file) written. No protocol doc yet (Series 7 inherits the Series 6 protocol, `series-6/protocol.md`, unless a Series-7 variant is written). No designs, no build, no review.

---

## Charter-change log

*Distinct from workstream progress: this logs edits to `charter.md` itself. The charter is edited only to fix errors in the design (a mis-stated target, an ill-formed signature), never to record progress.*

- **REV-0 (initial):** charter created; no changes yet. Series 7 seeded from Series 6's honest finding (the process collapse, `ws1_productive_unique`) per the program's inter-series discipline (protocol §6): the prior series' hardest pushback becomes the next series' question. Series 6 is **not** rewritten — it stays the honest record of the dynamism attempt; Series 7 is the standalone impossibility that generalizes it.

---

*Status file v0. Maintained alongside `charter.md` (stable). Update the program snapshot and the relevant workstream block whenever a status changes; move closed obligations to the Closed log with their discharging theorem. No em dashes are permitted in final academic paper copy drawn from this program; this working ledger is not final copy.*
