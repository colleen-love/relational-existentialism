# Program 2 Series 12 (2.12), Protocol

**The process, self-contained. This protocol takes Series 2.12 from an empty `formal/` to a computed verdict with no delegation except the two blind review phases (C and F, section 5). The series asks one recovery question: do the imports carry a measure — a probability — and is it the Born rule `|amp|²`? It rebuilds no imported machinery; it constructs the reading of Series 2.11's weight as a PROBABILITY and the CONSISTENCY test that forces (or refutes) the Born form, on the imported amplitude (`P2S11`). This is execution tier 3 of Phase 3, the second half of the quantum recovery. It is chartered under Phase 3's no-smuggling gate, at its sharpest: the Born rule must be EARNED — the squared form FORCED by consistency with the interference and the classical additive measure REFUTED — never defined as `|amp|²`. Genuine chance requires the imports to carry a measure; DETERMINISTIC (no measure, interference without chance) is a pre-registered honorable outcome. Scope disclosed: the rebit Born rule (real ±1 amplitude); the complex form and Gleason's uniqueness a forward-note.**

**PROCESS NOTICE (program finding P3-D1).** The Series 2.11 executor SKIPPED the chartered Phase C (blind design review) and Phase D, running B→E→F, and did not disclose it. That is a reviewability defect regardless of outcome. This series runs ALL of A→G: Phase C (blind design review) and Phase D are NOT optional. `blind-seed-C.md` MUST be generated and a blind Phase C pass MUST run (and be recorded in the ledger) before Phase E code is written. Tier 1 will check phase-completeness on the landing.

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 3)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "probability," "Born," "chance," "measure," no metaphysics, no Gleason gloss. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (STOCHASTIC-NOT-BORN, DETERMINISTIC, SHAPE-DRAWN, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **DETERMINISTIC — the imports carry no measure, the world interferes without chance — is a genuine outcome and a specification for the next iteration, not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built, or **(Relabeled)** the target was not built, the obstruction recorded, the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("probability," "Born," "measure," "weight," "chance") and check whether the statement still goes through as a bare non-negativity / consistency / inequality fact. WS2's non-classicality strips to "the combined weight is `< ` the sum of the parts"; WS3's earn strips to "square-then-add gives `2` but the interference gives `0` (inconsistent), while add-then-square gives `0` (consistent) and is `≥ 0`."

4. **The recovery is earned, not smuggled (the Phase-3 no-smuggling gate, sharpest here).** No proof term DEFINES the probability as `|amp|²`; the squared form is FORCED by consistency with the interference and the classical form REFUTED. "Probability," "Born," "measure" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "weight," "measure," "probability," "Born," "chance," "random," "stochastic," "self," "import," "God," or "choice" as content. Headlines mention only the squared quantity (a neutral name), the consistency check, the imported `amp`/weight, the imports (a neutral name), the transcribed machinery, and standard Lean/Mathlib.

Four emphases specific to this series:

6. **The Born rule is EARNED, not named (the no-smuggling gate, PROMOTED first-class, sharpest in the program).** The squared form must be FORCED by consistency (the classical additive measure refuted by the interference), not defined. The reviewer presses hardest on audit (a): is the squared form forced, or is the probability defined as `|amp|²`?

7. **Genuine chance requires a measure.** A probability may be claimed only where the imports carry a non-trivial measure. If the freedom is structureless, the honest verdict is DETERMINISTIC. Audit (b).

8. **The scope is disclosed, the complex/Gleason form not overclaimed.** The amplitude is Series 2.11's real ±1 sign; this series earns at most the rebit Born rule. No theorem claims the full complex amplitude or Gleason's uniqueness. Audit (d).

9. **DETERMINISTIC is honorable.** If the imports carry no measure, the series lands DETERMINISTIC — the honest report that this world interferes without chance — reported in full, never relabelled into a pseudo-probability.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).
- **`spec/README.md` (design index).** The imported object (`P2S11`'s amplitude/weight/interference), the primitive (the weight-as-probability and the consistency test, built fresh and earned), the discipline (Born earned not named, chance needs a measure, scope disclosed, DETERMINISTIC honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/born-derisking.md` (this series, before the WS designs).** The paper hunt: the two candidate measures — the classical additive (square each amplitude, then add over the ways) and the Born (add the amplitudes, then square) — and the by-hand test on Series 2.11's carriers that (a) the classical measure CONTRADICTS the interference (gives `2` where the interference gives `0`), (b) the Born measure is consistent (gives `0`) and non-negative, and (c) whether the imports carry a genuine non-trivial measure at all (else DETERMINISTIC). Only if the Born form is forced by consistency does BORN earn the WS designs; if the classical form is not genuinely refuted, or no measure survives, land STOCHASTIC-NOT-BORN or DETERMINISTIC.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4. **Both are mandatory (P3-D1).**
- **`program-2/series-11` (the imported object, already built).** Reaching S8–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S12` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings). ALL phases are mandatory — see the P3-D1 notice.

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format; **read `program-2/series-11/`** (the amplitude, the weight `combinedWeight`/`partsWeight`, the interference `ws3_destructive` — the structure this series reads as a probability); **read `program-2/series-0/`** and the P1 prior art (the imports, the out-of-image differentiator — the candidate carrier of chance). Read `program-2/charter-extension-2.md` §3 (the no-smuggling gate) and §4 (2.12). **Then write `spec/born-derisking.md`** (the paper hunt above). Only if the Born form is forced by consistency (the classical refuted) and a genuine measure survives does BORN earn the WS designs; else land STOCHASTIC-NOT-BORN or DETERMINISTIC (record the obstruction, skip to that verdict at WS5). If it survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage, the strip test, the no-smuggling gate, the earned-vs-named discipline, the scope disclosure, the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S12` module naming and record it. **Gate: commit `spec/born-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND] — MANDATORY (P3-D1)
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **This phase is not optional (P3-D1); it MUST run and be recorded before Phase E.** The reviewer presses hardest on audit (a): is the Born form FORCED by consistency or DEFINED as `|amp|²`? — audit (b): do the imports carry a genuine measure, or is chance asserted where none is earned? — and audit (d): is the scope honest (rebit, not the complex/Gleason form)?

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
**Precondition (P3-D1): a Phase C pass has run and returned zero SERIOUS, recorded in the ledger.** Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S12` namespace. **Build on Series 2.11**: `import P2S11` and use its amplitude/weight/interference (and its transitive API) — do NOT `import P2S9`/`P2S10` (not reused) or `P2S8`/…/`P1` directly (the layered chain; the gate enforces it).

**Register the series (do this at Phase E, never earlier).** Namespace `P2S12`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S12"
srcDir = "../program-2/series-12/formal"
roots = ["P2S12", "P2S12.AxiomCheck"]
```
and append `"P2S12"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-12 "^import (P2S11|P2S12)(\.[A-Za-z0-9_]+)*$"`. Lay out `formal/` as `P2S12.lean` (imports `P2S12.ws1`…`P2S12.ws5`), `P2S12/wsN.lean`, `P2S12/AxiomCheck.lean`, mirroring `program-2/series-11/formal/P2S11/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (a) the Born form forced by consistency not named, (b) a genuine measure vs asserted chance, and (d) the scope disclosed (rebit not complex/Gleason).** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done — AND a Phase C pass is on record (P3-D1). The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the Born rule is NAMED (probability defined as `|amp|²`, not forced — audit a, the phase sin); chance is asserted where the imports carry no measure (audit b); the complex/Gleason form is OVERCLAIMED (audit d); the classical measure is excluded by fiat rather than refuted; a name is a proof term; a prior SERIOUS finding RECURS; a chartered phase (esp. Phase C) was skipped (P3-D1); or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a consistency check that is really a definition).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the Born/Gleason prose, `charter-extension-2.md`'s prose, `summary*.md`, `born-derisking.md`, and any file naming "probability," "Born," "chance," "measure." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension-2.md`, `summary*.md`, `born-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names grep; confirm the audit clauses, ESPECIALLY (a) the Born form forced not named, (b) a genuine measure not asserted chance, and (d) the scope disclosed; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction. If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G. **Both the Phase C and the Phase F delegation MUST occur (P3-D1); skipping either is a reviewability defect.**

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S12 P2S12.AxiomCheck   # compiles (P2S11/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-12/formal            # sorry-free (prose excepted)
lake build P2S12.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                         # closure (P2S12 + P2S11 + Mathlib)
grep -rniE "\b(weight|measure|probability|born|chance|random|stochastic|self|import|god|choice)\b" \
  ../program-2/series-12/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely; the Lean `import` keyword is exempt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS AND a Phase C pass is on record (P3-D1); (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (BORN / STOCHASTIC-NOT-BORN / DETERMINISTIC / SHAPE-DRAWN / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. BORN is quantum probability recovered in its rebit form: the imports carry a measure whose consistent form is the squared amplitude, forced by the interference, the complex/Gleason form the disclosed gap. STOCHASTIC-NOT-BORN is chance without the rule. DETERMINISTIC is the deepest NOT-RECOVERED — this world interferes without chance — and the specification that a source of weighted freedom must be built. SHAPE-DRAWN joins the standing opens. None is reached by relabeling; the T1-S1 / Series-2.10 / Series-2.11 standard applies with full force.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent — and, per P3-D1, ALL phases including the blind Phase C are mandatory and recorded. The weight this series tests is whether the world's one freedom carries the Born rule; the knot is whether the squared measure is forced by the interference or named. Phase B must find (or fail to find) a forced Born form on paper before it is built, and DETERMINISTIC is honorable. The Born rule is earned from the interference or it is not recovered; the scope is the real rebit form, the complex/Gleason form a disclosed forward-note. Reuses Series 2.11; imports `P2S11` only. No em dashes in final academic copy.*
