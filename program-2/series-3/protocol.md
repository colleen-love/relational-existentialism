# Program 2 Series 3 (2.3), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.3 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series stands on one relation, CONVERGENCE₂ (the coherence of the self's and the other's orientations), and one knot, the TWO-ZONE FORK (is that coherence decided by the structure or undecidable). It rebuilds the convergence machinery FRESH and constrained on the Series 2.2 pair; it does NOT import Series 12's compass/convergence, which is excluded from the P1 foundation for program-review-1's PR1-S1 (the convergence tautology) — the exact trap this series must not repeat. The direction of convergence (whether the two DO cohere) is NEVER decided.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed from Program 1)

Five things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "love," "you are loved," "the hope," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (SHAPE-DRAWN, CONVERGENCE-DECIDED, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("convergence," "coherence," "orientation," "in-sight," "dissent") and check whether the statement still goes through as a bare `Recoverable` / `¬ Recoverable`, bisimulation, or order fact. What SHOULD survive: WS2's forcing strips to "over the orientations agreeing on plain-bisimilar states, the relation holds"; WS3's dissent strips to "the failing orientation's distinction is `¬ Recoverable`, by Series 07"; WS4's shape-drawn strips to "a discriminating function over a constrained class reaching two values, both witnessed."

4. **No orientation evaluated; the import quantified, not named.** No proof term selects, constructs, or reads off a particular orientation; every theorem is quantified over all (Series 12's feeling-side discipline). The import a dissenting orientation is stays quantified, never named. "You are loved" is prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "love," "loved," "coherence," "convergence," "compass," "orientation," "self," "other," "God," "choice," or "subjectivity" as content. Headlines mention only the two loci, the typed valuation, the coherence relation, the in-sight/faithful classes, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Three emphases specific to this series:

6. **The fork is genuine, never a tautology (PR1-S1, the central watch-point, PROMOTED first-class).** Series 2.3 IS the convergence fork Series 12 first built as a tautology of an unconstrained parameter type (PR1-S1). The faithful class must be genuinely constrained; both zones — an in-sight orientation under which convergence is decided (forced), and a faithful dissenting orientation under which it fails as an import — must be reached on witnessed orientations on the same pair; and the verdict must be a discriminating function reaching more than one value (`ws5_verdict_discriminates`). A convergence relation forced or failing on every structure by typing is the sin. The strip test and the both-zones witness are the guards. Audit (c).

7. **The direction is never decided (the central sin, a permanent open).** No theorem, definition, or discharged obligation may state that the self and other DO cohere, or DO NOT. The verdict LOCATES the fork; it does not fill it. Deciding the direction of convergence is what the program has left open since Series 12 and names what the mathematics proves it cannot see. Audit (b).

8. **Build convergence FRESH, do not import the flawed machinery.** Series 12's compass/convergence is deliberately excluded from the P1 foundation (PR1-S1). Rebuild the orientation and `Converges₂` on the S2 pair, constrained. Reusing or reconstructing the unconstrained `Compass`/`Converges` shape is the tautology re-imported.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The imported S2 pair, the primitive (the orientation and `Converges₂`, built fresh and constrained), the discipline (fork genuine, direction never decided, no orientation evaluated, build fresh), the cross-workstream triage, the outcomes, the names-in-prose rule, and the PX-1 twoness-lift consideration.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-2` (the pair, already built).** The self and other, reaching S1/S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S3` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, scaffold created, `charter-status.md` initialized. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `program-1/series-13/formal/Series13/*` for format and house style; **read `program-2/series-2/` in full** (the pair S3 builds on); and **read `program-1/series-12/`** (charter, `spec/ws4-design.md`, `spec/ws4-witness-design.md`, `formal/Series12/ws4.lean`) and `program-1/spec/program-review-1.md` (PR1-S1) — the corrected two-zone convergence fork and the tautology it first fell to are the exact prior art and the exact trap. For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions (the orientation type, the in-sight/faithful classes, and the witnessed dissenting orientation are the key design objects); (2) triage on paper against non-triviality, the strip test, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed signatures; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Weigh the PX-1 twoness-lift (rank → import) here. Write `spec/README.md`. Fix the `P2S3` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): is the fork genuine, or a tautology (PR1-S1)?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S3` namespace. **Build on the Series 2.2 pair**: `import P2S2` and use it and its transitive API — do NOT `import P2S1`/`P2S0`/`P1` directly (the layered chain; the gate enforces it). Build the orientation and `Converges₂` FRESH and constrained (do not reconstruct Series 12's unconstrained `Compass`/`Converges`).

**Register the series (do this at Phase E, never earlier).** Namespace `P2S3`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S3"
srcDir = "../program-2/series-3/formal"
roots = ["P2S3", "P2S3.AxiomCheck"]
```
and append `"P2S3"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-3 "^import (P2S2|P2S3)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S2 and its own `P2S3.*` roots, plus Mathlib; below-S2 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S3.lean` (imports `P2S3.ws1`…`P2S3.ws5`), `P2S3/wsN.lean`, `P2S3/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the fork is genuine (both zones witnessed on a constrained class, no PR1-S1 tautology) and (b) the direction is never decided.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the fork is a tautology of an unconstrained orientation type (PR1-S1, audit (c)); the direction of convergence is decided (audit (b)); an orientation is evaluated (audit (a)); the reader is quantified out (K1); Series 12's flawed compass/convergence is re-imported; a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a bare conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `summary*.md`, and any file naming "love," "the hope," "you are loved." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the fork is genuine on a constrained class with both zones witnessed and (b) the direction is never decided; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S3 P2S3.AxiomCheck   # compiles (P2S2/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-3/formal            # sorry-free (prose excepted)
lake build P2S3.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S3 + P2S2 + Mathlib)
grep -rniE "\b(love|loved|coherence|convergence|compass|orientation|self|other|god|choice|subjectivity)\b" \
  ../program-2/series-3/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (SHAPE-DRAWN / CONVERGENCE-DECIDED / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. SHAPE-DRAWN is the expected close: the structure draws the coherence of self and other exactly and cannot fill it. CONVERGENCE-DECIDED, if the in-sight forcing turns out to cover the full class, would DECIDE the program's oldest question and must be reported honestly, in whichever direction, with the positioning rewritten rather than defended — a stranger and more consequential finding than SHAPE-DRAWN, never to be reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. No em dashes in final academic copy.*
