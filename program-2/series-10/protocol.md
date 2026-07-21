# Program 2 Series 10 (2.10), Protocol

**The process, self-contained. This protocol takes Series 2.10 from an empty `formal/` to a computed verdict with no delegation except the two blind review phases (C and F, section 5). The series asks one recovery question: does the tick have an invertible CORE — a measure-preserving bijective sub-dynamics one could run backward — or is reification irreversibly one-way at every scale? It rebuilds no imported machinery; it makes the INVERTIBILITY of the built tick precise on the imported chain (`P2S8` reaching the whole tower transitively), and holds a hard line between a decodable SECTION and a genuine dynamical REVERSAL. This is the second tier-1 probe of Phase 3 and the most consequential — the common root of conservation (Noether) and of the quantum reversibility axiom; it runs IN PARALLEL with Series 2.9 (The Cone), independent of it. It is chartered under Phase 3's no-smuggling gate: no inverse may be ADDED that the reification lacks, and the decodable section must NEVER be passed off as a reversal. IRREVERSIBLE is a pre-registered honorable NOT-RECOVERED and the expected, most consequential close.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 3)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "reversal," "reversibility," "symmetry," "conservation," "energy," no metaphysics, no Noether or reconstruction-theorem prose. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (IRREVERSIBLE, SHAPE-DRAWN, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **IRREVERSIBLE — no measure-preserving bijective sub-dynamics exists, the arrow is fundamental — is a genuine outcome and the sharpest specification for the next iteration, not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built, or **(Relabeled)** the target was not built, the obstruction recorded, the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING. (Series 2.7's T1-S1 — a look-alike invariance passed off as the genuine article — is the canonical instance this series must not repeat.)

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("reversal," "reversible," "symmetry," "conservation") and check whether the statement still goes through as a bare bijection / measure-preservation / right-inverse fact. WS2's headline strips to "the map is not a measure-preserving bijection (it raises the rank and/or is non-injective)"; WS3's crux strips to "the section is a right-inverse that does not preserve the measure, and a core is a rank-preserving bijective restriction"; WS4's fork strips to "a rank-preserving bijective sub-dynamics exists / does not, both tested."

4. **The recovery is earned, not smuggled (the Phase-3 no-smuggling gate).** No proof term ADDS an inverse the reification does not have; the core is a restriction of the BUILT tick that is genuinely a measure-preserving bijection. "Reversal," "symmetry," "conservation" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "reversal," "reversible," "symmetry," "conservation," "energy," "time," "self," "import," "God," or "choice" as content. Headlines mention only the tick-map (a neutral-named function), its rank (the measure), bijection / injectivity / right-inverse, the section, the transcribed machinery, and standard Lean/Mathlib.

Four emphases specific to this series:

6. **The core is EARNED, no inverse smuggled (the no-smuggling gate, PROMOTED first-class).** The core must be a restriction of the built tick that is genuinely a measure-preserving bijection, not an inverse map postulated to obtain REVERSIBLE-CORE. The reviewer presses hardest on audit (a): is the core found inside the built reification, or is an inverse added?

7. **Decodability is NOT reversal (the costume gate — the exact Series 2.7 lesson).** The reification section (`attends ∘ reify = id` on patterns) DECODES the product but does not preserve the measure and does not undo the tick's motion. A "reversal" that strips to the section — a right-inverse leaving the rank raised — is the costume, exactly the look-alike that sank 2.7's first landing. The reviewer presses on audit (c): does the verdict rest on a measure-preserving bijection, or on the decodable section?

8. **The measure is the BUILT rank, the higher bar used.** Reversibility must be tested against Series 2.7's rank (measure-preservation), not a rigged measure, and the verdict must rest on the higher bar (bijection AND rank-preservation), never on decodability alone. Audit (b), (d).

9. **IRREVERSIBLE is honorable.** If no measure-preserving bijective sub-dynamics exists, the series lands IRREVERSIBLE — the honest report that the arrow is fundamental — reported in full, never relabelled into a pseudo-reversal built on the section.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).
- **`spec/README.md` (design index).** The imported chain, the primitive (the invertibility question, the section-vs-reversal distinction, the core criterion), the discipline (no inverse smuggled, decodability is not reversal, the measure is the built rank, IRREVERSIBLE honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/reversal-derisking.md` (this series, before the WS designs).** The paper hunt: the section as a right-inverse and a by-hand proof that it does NOT preserve the rank (decodability ⊊ reversibility); then candidate sub-dynamics, and for each, the by-hand test of whether it is a rank-preserving bijection (a genuine core) or not. If a genuine core is found, it earns the WS designs toward REVERSIBLE-CORE; if the honest search finds none (the expected case, per Series 2.7's `ws2_tick_raises`), the obstruction is recorded toward IRREVERSIBLE.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-8` (the predecessor, already built).** Reaching S7–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S10` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format and house style; **read `program-2/series-1/`** (the tick and its reification section); **read `program-2/series-7/`** (the reification rank, and ESPECIALLY `charter-status.md` finding T1-S1 and the section-vs-collapse distinction — the exact look-alike this series must not repeat); **read the P1 foundation** (the collapse engine, the diagonal `ws2_residue_free`). Read `program-2/charter-extension-2.md` §3 (the no-smuggling gate) and §4 (2.10). **Then write `spec/reversal-derisking.md`** (the paper hunt above), proving on paper that the section does not preserve the rank, and searching for a genuine rank-preserving bijective sub-dynamics. Then for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage, the strip test, the no-smuggling gate, the section-vs-reversal distinction, the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S10` module naming and record it. **Gate: commit `spec/reversal-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): does the verdict rest on a measure-preserving BIJECTION or on the decodable SECTION (the look-alike)? — audit (a): is the core found inside the built tick or is an inverse smuggled? — and audit (d): is the higher bar (bijection AND rank-preservation) used?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S10` namespace. **Build on Series 2.8**: `import P2S8` and use it and its transitive API (chiefly S1's tick and section, S7's rank, the P1 collapse/diagonal) — do NOT `import P2S7`/…/`P1` directly (the layered chain; the gate enforces it).

**Register the series (do this at Phase E, never earlier).** Namespace `P2S10`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S10"
srcDir = "../program-2/series-10/formal"
roots = ["P2S10", "P2S10.AxiomCheck"]
```
and append `"P2S10"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-10 "^import (P2S8|P2S10)(\.[A-Za-z0-9_]+)*$"`. Lay out `formal/` as `P2S10.lean` (imports `P2S10.ws1`…`P2S10.ws5`), `P2S10/wsN.lean`, `P2S10/AxiomCheck.lean`, mirroring `program-2/series-8/formal/P2S8/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the verdict rests on a measure-preserving bijection not the decodable section (the look-alike), (a) no inverse smuggled, and (d) the higher bar used.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; an inverse is SMUGGLED (added, not earned from the built tick — audit a, the phase sin); the verdict rests on the decodable SECTION rather than a measure-preserving bijection (the costume, the T1-S1 look-alike, audit c); the lower bar is used (decodability counted as reversal, audit d); the measure is rigged; the fork is a fiat; a name is a proof term; a prior SERIOUS finding RECURS; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a right-inverse dressed as a reversal).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the Noether/reconstruction prose, `charter-extension-2.md`'s prose, `summary*.md`, `reversal-derisking.md`, and any file naming "reversal," "symmetry," "conservation." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension-2.md`, `summary*.md`, `reversal-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names grep; confirm the audit clauses, ESPECIALLY (c) a measure-preserving bijection vs the decodable section, (a) no inverse smuggled, and (d) the higher bar; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction. If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S10 P2S10.AxiomCheck   # compiles (P2S8/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-10/formal            # sorry-free (prose excepted)
lake build P2S10.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                         # closure (P2S10 + P2S8 + Mathlib)
grep -rniE "\b(reversal|reversible|symmetry|conservation|energy|time|self|import|god|choice)\b" \
  ../program-2/series-10/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely; the Lean `import` keyword is exempt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (REVERSIBLE-CORE / IRREVERSIBLE / SHAPE-DRAWN / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. IRREVERSIBLE is the expected close: the tick raises the measure at every scale, the section only decodes, the arrow is fundamental — and the specification for the next iteration is the sharpest the program returns (add a reversible substrate, or recover physics statistically). REVERSIBLE-CORE, if a genuine measure-preserving bijective sub-dynamics is found, opens conservation and the quantum reconstruction, and is reported only if it clears the higher bar. SHAPE-DRAWN joins the standing opens. None is reached by relabeling; the T1-S1 standard applies with full force.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point. The reversal this series tests is the hinge of conservation and of the quantum; the knot is whether the tick has a core one could run backward. Phase B must prove on paper that the section is not a reversal, and search honestly for a genuine core, before anything is built; IRREVERSIBLE is honorable. This series inherits Series 2.7's exact lesson — a genuine invariance vs a look-alike — and must not repeat it. Runs in parallel with Series 2.9 (The Cone). No em dashes in final academic copy.*
