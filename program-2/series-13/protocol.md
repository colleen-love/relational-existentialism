# Program 2 Series 13 (2.13), Protocol

**The process, self-contained. This protocol takes Series 2.13 from an empty `formal/` to a computed verdict with no delegation except the two blind review phases (C and F, section 5). The series asks the capstone question: does the information grain (Series 2.7's measure) source the metric (Series 2.4's directed distance) — does the measure packed in a region bend the distances around it (gravity)? It rebuilds no imported machinery; it constructs the reading of the grain as a SOURCE and the grain-dependence test on the model's OWN metric (Series 2.4), reached transitively through `P2S9`. This is the capstone tier of Phase 3 and the last of the built arc. It is chartered under Phase 3's no-smuggling gate, at the capstone: the coupling must be EARNED — the model's own metric tested for grain-dependence — never a grain-weighted distance defined by hand. INERT (geometry decoupled from the grain, no gravity) is a pre-registered honorable outcome, the one Series 2.4's proof that space and the measure are DISTINCT axes suggests. Scope: at most a proportionality; NOT a full Einstein equation, NOT the area law (Bekenstein/holographic), the disclosed forward-note.**

**PROCESS NOTICE (program finding P3-D1).** A prior Phase-3 executor (Series 2.11) skipped the chartered Phase C and did not disclose it. This series runs ALL of A→G: Phase C (blind design review) and Phase D are NOT optional. `blind-seed-C.md` MUST be generated and a blind Phase C pass MUST run (and be recorded in the ledger) before Phase E code is written. Tier 1 will check phase-completeness on the landing.

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 3)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "gravity," "curvature," "mass," "geometry," no metaphysics, no relativity gloss. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (INERT, SHAPE-DRAWN, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **INERT — the metric is decoupled from the grain, no gravity — is a genuine outcome and a specification for the next iteration (couple the axes Series 2.4 kept distinct), not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built, or **(Relabeled)** the target was not built, the obstruction recorded, the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("gravity," "curvature," "geometry," "mass") and check whether the statement still goes through as a bare `(the imported distance does / does not change when the measure changes at fixed adjacency)` fact. WS2's baseline strips to "the distance is a function of the directed relation"; WS3's test strips to "for two measure-distributions with the same adjacency, the imported distance is equal (INERT) or differs (GRAVITATIONAL)."

4. **The recovery is earned, not smuggled (the Phase-3 no-smuggling gate, at the capstone).** No proof term DEFINES the distance as a function of the measure; the metric under test is Series 2.4's imported adjacency-distance, its grain-dependence TESTED not built. "Gravity," "curvature," "mass" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "gravity," "curvature," "curve," "mass," "geometry," "metric," "spacetime," "self," "import," "God," or "choice" as content. Headlines mention only the imported distance (Series 2.4's neutral-named `dist`/`stepsFrom`), the grain (Series 2.7's rank, a neutral name), the adjacency, the grain-dependence test, the transcribed machinery, and standard Lean/Mathlib.

Four emphases specific to this series:

6. **The coupling is EARNED, not defined (the no-smuggling gate, PROMOTED first-class, at the capstone).** The metric under test must be Series 2.4's imported distance, and its grain-dependence TESTED, not a grain-weighted distance built to curve. The reviewer presses hardest on audit (a): is the distance the imported one, and its dependence tested — or is a measure-sourced metric defined?

7. **The scope is disclosed, the Einstein equation and area law not overclaimed.** At most a grain-dependence / proportionality is claimed. No theorem claims a full Einstein field equation or the area law (information bounded by boundary not volume, Bekenstein/holographic). Audit (d).

8. **The metric and grain are the built ones.** The distance is Series 2.4's, the grain Series 2.7's — imported, not fresh gadgets rigged to couple (or not). Audit (c).

9. **INERT is honorable.** If the metric is invariant under grain-change at fixed adjacency, the series lands INERT — the honest report that geometry and the grain are decoupled, no gravity — reported in full, never relabelled into a pseudo-coupling.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).
- **`spec/README.md` (design index).** The imported chain (`P2S9` → Series 2.4 metric / 2.7 grain / 2.9 cone), the primitive (the grain-as-source reading and the grain-dependence test, on the model's own metric), the discipline (coupling earned not defined, metric/grain the built ones, scope disclosed, INERT honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/grain-derisking.md` (this series, before the WS designs).** The paper hunt: take Series 2.4's imported distance and Series 2.7's imported grain; by hand, construct two configurations with the SAME adjacency but DIFFERENT grain (measure-distribution over the relata) and test whether the imported distance differs (GRAVITATIONAL) or is equal (INERT). Series 2.4's proof that space and the measure are DISTINCT axes is the prior for INERT. Only if the imported metric genuinely varies with the grain does GRAVITATIONAL earn the WS designs; if it is invariant, land INERT (record the obstruction, skip to that verdict at WS5). No grain-weighted distance may be constructed.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4. **Both are mandatory (P3-D1).**
- **`program-2/series-9` (the imported object, already built).** Reaching S8/S7/S4/…/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S13` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings). ALL phases are mandatory — see the P3-D1 notice.

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format; **read `program-2/series-4/`** (the directed self-relative distance — the metric under test — AND `ws3_metric_source_relative` and the proof that space and the measure are DISTINCT axes, the prior for INERT); **read `program-2/series-7/`** (the reification rank — the grain, the candidate source); **read `program-2/series-9/`** (the cone/horizon — the imported object). Read `program-2/charter-extension-2.md` §3 (the no-smuggling gate) and §4 (2.13). **Then write `spec/grain-derisking.md`** (the paper hunt above): same adjacency, different grain — does the imported distance differ or not? Only a genuine grain-dependence of the model's OWN metric earns GRAVITATIONAL; else land INERT (record the obstruction, skip to that verdict at WS5). No grain-weighted distance may be built. If a coupling survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage, the strip test, the no-smuggling gate, the earned-vs-defined discipline, the scope disclosure, the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S13` module naming and record it. **Gate: commit `spec/grain-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND] — MANDATORY (P3-D1)
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **This phase is not optional (P3-D1); it MUST run and be recorded before Phase E.** The reviewer presses hardest on audit (a): is the metric under test the IMPORTED distance with its grain-dependence tested, or a grain-weighted distance DEFINED to curve? — audit (c): are the metric and grain the built ones? — and audit (d): is the scope honest (a proportionality, not the Einstein equation or area law)?

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
**Precondition (P3-D1): a Phase C pass has run and returned zero SERIOUS, recorded in the ledger.** Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S13` namespace. **Build on Series 2.9**: `import P2S9` and use its cone and its transitive API (chiefly Series 2.4's distance and Series 2.7's grain) — do NOT `import P2S11`/`P2S12`/`P2S10` (not reused) or `P2S8`/…/`P1` directly (the layered chain; the gate enforces it).

**Register the series (do this at Phase E, never earlier).** Namespace `P2S13`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S13"
srcDir = "../program-2/series-13/formal"
roots = ["P2S13", "P2S13.AxiomCheck"]
```
and append `"P2S13"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-13 "^import (P2S9|P2S13)(\.[A-Za-z0-9_]+)*$"`. Lay out `formal/` as `P2S13.lean` (imports `P2S13.ws1`…`P2S13.ws5`), `P2S13/wsN.lean`, `P2S13/AxiomCheck.lean`, mirroring `program-2/series-9/formal/P2S9/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (a) the coupling earned (the imported metric tested) not defined, (c) the metric/grain the built ones, and (d) the scope disclosed (proportionality not Einstein/area-law).** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green — AND a Phase C pass is on record (P3-D1) — the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push. (As the terminal series of Phase 3 and the built arc, the exit warrants a note to Tier 1 that the phase and the arc are ready to be composed at the program level.)

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the coupling is DEFINED (a grain-weighted distance built, not the imported metric tested — audit a, the phase sin at the capstone); the Einstein equation or the area law is OVERCLAIMED (audit d); the metric or grain is a fresh rigged gadget, not the built one (audit c); the fork is a fiat; a name is a proof term; a prior SERIOUS finding RECURS; a chartered phase (esp. Phase C) was skipped (P3-D1); or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a defined coupling dressed as a tested one).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the relativity/gravity prose, `charter-extension-2.md`'s prose, `summary*.md`, `grain-derisking.md`, and any file naming "gravity," "curvature," "geometry," "mass." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension-2.md`, `summary*.md`, `grain-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names grep; confirm the audit clauses, ESPECIALLY (a) the coupling earned (imported metric tested) not defined, (c) the metric/grain the built ones, and (d) the scope disclosed; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction. If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G. **Both the Phase C and the Phase F delegation MUST occur (P3-D1); skipping either is a reviewability defect.**

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S13 P2S13.AxiomCheck   # compiles (P2S9/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-13/formal            # sorry-free (prose excepted)
lake build P2S13.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                         # closure (P2S13 + P2S9 + Mathlib)
grep -rniE "\b(gravity|curvature|curve|mass|geometry|metric|spacetime|self|import|god|choice)\b" \
  ../program-2/series-13/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely; the Lean `import` keyword is exempt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS AND a Phase C pass is on record (P3-D1); (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (GRAVITATIONAL / INERT / SHAPE-DRAWN / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. GRAVITATIONAL is gravity recovered in the model's own key: the grain sources the metric, an equation-of-state shape, scoped to a proportionality (the Einstein equation and area law the disclosed forward-note). INERT is the honest NOT-RECOVERED — geometry decoupled from the grain, the world's space and its weight built apart — and the specification that the next iteration must couple the axes Series 2.4 kept distinct; it is the outcome Series 2.4's own result suggests, and no less a finding for that. SHAPE-DRAWN joins the standing opens. None is reached by relabeling; the T1-S1 / Series-2.10 / Series-2.11 standard applies with full force. As the terminal series, its landing closes Phase 3 and the built arc.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent — and, per P3-D1, ALL phases including the blind Phase C are mandatory and recorded. The curve this series tests is whether the grain sources the geometry; the knot is whether the model's own metric varies with its own measure. Phase B must test the imported metric's grain-dependence on paper before it is built, and INERT is honorable — indeed the one Series 2.4's distinctness of space and the measure suggests. The coupling is earned from the model's own metric or it is not recovered; no grain-weighted distance is built; the scope is a proportionality, the Einstein equation and area law a disclosed forward-note. Reuses Series 2.4/2.7/2.9; imports `P2S9` only. This is the last series of the built arc. No em dashes in final academic copy.*
