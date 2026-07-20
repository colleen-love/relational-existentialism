# Program 2 Series 1 (2.1), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.1 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The whole series stands on one question, the TICK, and its edge, the CLOCK KNOT: is the ordering of ticks endogenous or an import? Everything the executor does is judged against the charter's success criteria and the false escapes, and the honesty machinery below is what keeps a shortfall from being quietly relabeled as the goal.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix an error in the design itself, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed from Program 1 and held unchanged)

Five things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts (theorem signatures, outcome classes), the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "the tick," no "the door," no "to attend is to become," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap. Blindness is enforced by instruction (section 5): the reviewer is told which files it may read and is forbidden the charter, the summaries, and the positioning.

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (TWO-ZONE, ENDOGENOUS, TIME-IS-IMPORT, PARTIAL, DISCONNECTED) with the obstruction made precise, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss. Constructing a theorem that manufactures the expected TWO-ZONE verdict past a real obstruction is the section 0.2 sin.

**2a. The recurrence guard (applied at both Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, and `charter-status.md` must name which: **(Fixed)** the design's originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the precise obstruction is recorded, and the payoff's status is demoted to the pre-registered honest outcome. "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is NEITHER, and is prohibited. Findings carry stable IDs across passes; a finding addressed by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("time," "tick," "moment," "before," "after," "clock," "self," "other") and check whether the statement still goes through as a bare reification, `FiniteAttention`, `RealFor`, `Recoverable`/`¬ Recoverable`, residue, causal-consumption, bisimulation, or order fact. A payoff that survives the strip is such a fact honestly flagged. What SHOULD survive: WS2's subtractivity strips to "the composite carries a residue non-recoverable from `plainOf`, by `ws2_residue_free`"; WS4's endogeneity strips to "the causal-consumption relation is recoverable and forced on bisimilar states"; WS4's import strips to "a linearization of a causally-independent pair fails `Recoverable`." The strip test is written into each WS design and run by the reviewer.

4. **Exogeneity is proved, not assumed.** The stream's choice at a tick is non-recoverable from the plain relating: `ws3_stream_exogenous` is a named proof term, not a docstring gloss. A tick the relating could perform on itself would have derived the dynamics from within, contradicting the transcribed Series 07 foundation.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "time," "now," "clock," "before," "after," "moment," "self," "other," "chance," "choice," or "subjectivity" as content. Every headline mentions only the cycle, the composite, the attention, the residue, the stream, the two orders, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. A name doing a proof's work breaches the wall, SERIOUS.

Two emphases specific to this series:

6. **No smuggled clock.** Every temporal fact is a reification, attention, causal-consumption, or stream fact. A background time index or a step counter doing the work of succession is a hidden atom, a second differentiator below the line. Audit clause (a); the reviewer runs the strip test on every temporal statement.

7. **The fork must be genuine, not a tautology.** Both WS4 arms are witnessed on a structure carrying a genuine concurrent pair (non-empty causally-independent pair) and a genuine causal pair, and the order relation carries a structural constraint. An ordering total by construction or a concurrency that is empty is the PR1-S1 defect. Audit clause (d).

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error; an upstream edit reopens affected workstreams.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidate constructions, a paper-decidable triage collapsed to a table, the winning construction to typed Lean signatures, outcome classes, and the strip-test annotation for each payoff. The contract a build is judged against. **All five plus `spec/README.md` are committed as one batch before any build begins (Phase B gate).**
- **`spec/README.md` (design index).** The shared carrier (what is transcribed and from where), the primitive decision (three additions over the carrier: partial attention load-bearing, the cycle-composite, the two orders on ticks), the discipline (no smuggled clock, stream exogenous, reader load-bearing, fork genuine), the cross-workstream triage summary, the outcomes, and the names-live-in-prose rule.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** The exact, motivation-free material handed to the reviewer (section 4). Regenerated on each review pass.
- **`charter-status.md` (living ledger).** Phase, verdict, carrier, targets, audit clauses, findings ledger with the recurrence guard, disclosed deviations, permanent opens, phase log. Updated at the end of every phase.
- **`formal/` (built at Phase E).** The Lean sources, one module per workstream plus an `AxiomCheck`, in the series' own namespace.
- **`summary.md` / `summary-technical.md` (written after the verdict).** Plain-language and technical accounts. Not required to reach the verdict.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
The charter is written and committed, the scaffold exists, `charter-status.md` is initialized. Nothing further.

### Phase B — Design [executor]
For each of WS1–WS5, write `spec/wsNN-design.md`:
1. List the candidate constructions (at least the charter's and one alternative where one exists).
2. Triage them on paper against non-triviality, the strip test, and the audit clauses; collapse to a decision table with the rejected candidates and the reason each was rejected recorded.
3. Write the winning construction to typed Lean signatures (the exact theorem statements the build will discharge), naming the transcribed carrier pieces each depends on.
4. Fix the outcome classes (which pre-registered verdict each obligation lands under if it falls short).
5. Annotate each payoff with what it SHOULD strip to (principle 3).
Write `spec/README.md` tying them together. Fix the Lean module naming and the `lake/` registration decision, and record it in `charter-status.md`. **Gate: commit all six files as one batch before any `formal/` file exists.** Update the phase log.

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` by the recipe in section 4 (design contracts + success criteria + audit checks, motivation stripped). Spawn a blind reviewer subagent by the mechanism in section 5, pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect its findings, graded SERIOUS / REAL / COSMETIC (section 3). Append them to the findings ledger in `charter-status.md` with stable IDs. Do not fix anything in this phase; only record.

### Phase D — Design repair [executor]
Address every SERIOUS finding by the section 2a binary: Fixed (build the specified target into the design) or Relabeled (record the obstruction, demote to a pre-registered outcome). Address REAL findings if cheap; note COSMETIC. Update the affected `spec/` files and the `charter-status.md` ledger, naming the closure for each SERIOUS finding. Commit.
**Loop:** if any SERIOUS finding was closed by editing a design (not merely relabeled), return to Phase C with a fresh blind seed and re-review. Continue C/D until a Phase C pass returns zero SERIOUS findings. The recurrence guard applies: a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and RECURRING.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`. Transcribe the carrier by name and content from the named Program 1 sources (do not import across series; the gate forbids it). The build must be:
- **sorry-free:** `grep -rn "sorry" formal/` clean (docstring prose excepted).
- **axiom-clean:** `AxiomCheck` emits `#print axioms` for every headline theorem, resting on no axioms beyond Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`).
- **gate-green:** `scripts/gate.sh` confirms no cross-series imports.
- **compiling:** `cd lake && lake build <modules>` succeeds.
Run the checks in section 6. Compute the verdict function in WS5 from the built theorems (never hand-set it). Update `charter-status.md` targets to BUILT with the theorem names, and the audit clauses to whatever the build supports. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md` (design contracts + success criteria + audit checks, motivation stripped; section 4). Spawn a blind reviewer subagent (section 5) pointed at the blind seed AND the `formal/` sources, and told to judge whether the code proves the claimed signatures, to run the strip test and the names-not-terms grep, and to confirm the audit clauses. Collect graded findings; append to the ledger. Do not fix; only record.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the section 2a binary. Update `formal/` and/or the ledger; re-run the section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh blind seed whenever a SERIOUS finding was closed by editing code. Continue F/G until a Phase F pass returns zero SERIOUS findings.

### Exit
When a Phase F pass returns zero SERIOUS findings and the build is sorry-free, axiom-clean, and gate-green, the series is done. The verdict in WS5 is the computed outcome. Write `summary.md` and `summary-technical.md`. Finalize `charter-status.md` (verdict, every finding's closure, disclosed deviations). Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; a smuggled clock does the work of succession; the stream is assumed rather than proved exogenous; the reader is quantified out (composite a point-tag); the fork is a tautology of an unconstrained order (PR1-S1); a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build (PR1-S2). Closes only by the section 2a binary.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, a hypothesis that is assumed and returned, an over-strong name). Fix opportunistically.
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, an over-hypothesis, a naming nit. Fix if cheap; never blocks.

---

## 4. The blind seed (the recipe, run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY:
1. The theorem signatures and definitions under review, copied from `spec/wsNN-design.md` (Phase C) or read from `formal/` (Phase F), with NO motivating comment.
2. The charter's success criteria (section 6 of the charter), restated WITHOUT the motivating clauses: the mathematical obligation only, not why it matters.
3. The audit checks (a–e) as mechanical instructions.
4. The strip-test instruction and the names-not-terms forbidden list.
5. The grading rubric (section 3 above).

EXCLUDE, always: `charter.md`'s section-0/1/8 prose, the manifesto paragraph, the positioning, the tenets, `summary*.md`, and any file naming "the tick," "the door," "wound," "rescue," "loved." If a design file contains motivating prose, copy only its signatures and triage table into the seed, not its narrative. The seed is the whole of what the reviewer is told the work is about.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits for the verdict). The prompt is BLIND and must:
- Name exactly the files the reviewer may read: `spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources. State explicitly: **do not read `charter.md`, `charter-status.md`, `summary*.md`, or any file containing motivating prose; judge the code only against the contracts in the blind seed.**
- Give the reviewer its task: for each signature, determine whether the design (C) is coherent and non-vacuous, or the code (F) proves it; run the strip test on each payoff; run the names-not-terms grep; confirm the audit clauses; and grade each finding SERIOUS / REAL / COSMETIC by the rubric in the seed.
- Require the reviewer to return a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, the exact obligation or code location, and the defect. The reviewer proposes no fixes; it reports.

Blindness is enforced by this instruction, not by file permissions (the subagent shares the filesystem). The executor must not paste charter prose into the prompt. If the reviewer reports it read a forbidden file, discard the pass and re-run with a fresh subagent.

For Phase F the reviewer may run read-only checks (`lake build` for a compile confirmation, the greps in section 6) but is not required to; the executor has already run them and records their output in the seed. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (run by the executor at Phase E and after each Phase G)

```
cd lake && lake build <Series2_1 modules> <AxiomCheck>   # compiles
grep -rn "sorry" ../program-2/series-1/formal            # sorry-free (prose excepted)
lake build <AxiomCheck>                                   # axiom record; standard three only
../scripts/gate.sh                                        # no cross-series imports
grep -rniE "\b(time|now|clock|before|after|moment|self|other|chance|choice|subjectivity)\b" \
  ../program-2/series-1/formal   # names-not-terms: hits must be docstring prose only
```

Record each check's result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before delegating Phase F.

---

## 7. Exit criteria and the verdict

The series exits when ALL hold:
1. A Phase F pass returned zero SERIOUS findings.
2. The build is sorry-free, axiom-clean (standard three), and gate-green.
3. The names-not-terms grep is clean (prose only).
4. The verdict function in WS5 computes an outcome from the built theorems, and `charter-status.md` records it: TWO-ZONE (expected), ENDOGENOUS, TIME-IS-IMPORT, PARTIAL, or DISCONNECTED, with the obstruction precise if not TWO-ZONE.
5. Every SERIOUS finding in the ledger is closed by the section 2a binary, with its closure named.

The verdict is the residue of the process, not its premise. Whatever it is, if it was computed honestly and the fork was left open, the series succeeded at its charter even if the world it hoped for turned out to need one more import.

---

*This protocol is self-contained: a single executor runs A, B, D, E, G and delegates only C and F, by section 5, to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. No em dashes in final academic copy.*
