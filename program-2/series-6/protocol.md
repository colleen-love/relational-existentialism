# Program 2 Series 6 (2.6), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.6 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series asks one knot: does the self PERSIST through time as a recoverable WEAK thread, or is each tick a new self and the continuity an import? It rebuilds no imported machinery; it constructs the weak thread FRESH on the tick and relational identity, and reads Series 2.1's linearization import as the single lived timeline. This is the third series of Phase 2 and is chartered under the Phase-2 costume gate: the knot is the WEAK THREAD (recoverable, or import) and the LINEARIZATION-import (the single line is the self's import), NOT the trivial failure of strict identity, and NOT rank being a scalar.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 2)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "self," "thread," "life," "death," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (SEVERED, SHAPE-DRAWN, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("self," "thread," "persistence," "life," "death," "timeline") and check whether the statement still goes through as a bare `Recoverable` / bisimulation / order fact. What SHOULD survive: WS1's strict-failure strips to "the post-tick state is not plain-bisimilar to the pre-tick state"; WS2's weak thread strips to "a weaker-than-bisimilarity successor relation is / is not recoverable from `plainOf`"; WS3's line strips to "a total linear order of the moments is non-recoverable (`ws4_linearization_import`)"; WS4's fork strips to "a discriminating function over the weak thread's recoverability reaching two values, both witnessed."

4. **No persistence asserted absolutely; the import quantified, not named.** No proof term asserts the self persists frame-independently; continuity is FOR a self, self-relative, the single line the self's import (Phase-2 self-relative discipline). The import a non-recoverable thread is stays quantified, never named. "Self," "thread," "life" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "self," "thread," "persistence," "life," "death," "time," "here," "there," "God," "choice," or "subjectivity" as content. Headlines mention only the tick-successor relation, the weak continuity, the linear order of the moments, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Three emphases specific to this series:

6. **The knot is the weak thread, not the strict failure (the Phase-2 costume gate, PROMOTED first-class).** "Relational identity fails across a tick, so the self is a new relatum" is a true fact but a COSTUME of relational identity — not the finding. The verdict must rest on the WEAK thread's recoverability (WS2) and the LINEARIZATION-import (WS3). A payoff that strips to "the self changes, so strict identity fails," with no weak-thread and no linearization content, is the costume. The reviewer presses hardest on audit (c): does the verdict rest on the weak thread and the linearization, or only on strict identity failing?

7. **The 1D timeline rests on the linearization import, not on rank being scalar (audit d).** The one-dimensionality of lived time must rest on the total order of the moments being non-recoverable (`ws4_linearization_import`, the self's import), NOT on rank being an ℕ-valued scalar (a costume of the order). The partial causal order is endogenous; the single line is the import. Audit (d).

8. **The fork is genuine, never a fiat (SEVERED reachable, the weak thread genuinely weak).** THREADED and SEVERED must both be reachable; the weak thread must be genuinely weaker than strict identity, not strict identity relabelled. A weak thread that is secretly strict bisimilarity, or a SEVERED excluded by construction, is the fiat. The strip test and the both-carriers witness are the guards. Audit (b).

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The imported chain, the primitives (the weak thread and the linearization reading, built fresh), the discipline (knot on the weak thread not the strict failure, 1D on the linearization import not scalar rank, fork not by fiat, no absolute persistence), the cross-workstream triage, the outcomes, the names-in-prose rule, and the candidate witness.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-5` (the predecessor, already built).** Reaching S4/S3/S2/S1/S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S6` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold (`spec/`, `formal/`) created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `program-1/series-13/formal/Series13/*` for format and house style; **read `program-2/series-1/` in full** (the tick and `ws4_linearization_import` — the single line as import); **read `program-2/series-0/`** (relational identity, the collapse engine, recoverability, the knowing-asymmetry for mortality); and **read `program-2/series-4/` and `program-2/series-5/`** (the house pattern for a genuine fork with a reachable alternative carrier, and the self-relative discipline). Read `program-2/charter-extension.md` §3 (the costume gate) and §4 (the 2.6 entry, the thread-as-linearization). For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions (the WEAK THREAD — a successor-self relation genuinely weaker than bisimilarity — and the LINEARIZATION reading are the key design objects; design the weak thread so its recoverability is a genuine fork and SEVERED is reachable on a second carrier); (2) triage on paper against non-triviality, the strip test, the costume gate, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed signatures; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Write `spec/README.md`. Fix the `P2S6` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): does the knot rest on the weak thread and the linearization, or only on strict identity failing (the costume)? — and audit (b): is the weak thread genuinely weaker than strict identity, with SEVERED reachable, or a fiat?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S6` namespace. **Build on Series 2.5**: `import P2S5` and use it and its transitive API (chiefly `P2S1`'s tick/linearization import and relational identity) — do NOT `import P2S4`/…/`P1` directly (the layered chain; the gate enforces it). Build the weak thread and the linearization reading FRESH.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S6`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S6"
srcDir = "../program-2/series-6/formal"
roots = ["P2S6", "P2S6.AxiomCheck"]
```
and append `"P2S6"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-6 "^import (P2S5|P2S6)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S5 and its own `P2S6.*` roots, plus Mathlib; below-S5 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S6.lean` (imports `P2S6.ws1`…`P2S6.ws5`), `P2S6/wsN.lean`, `P2S6/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the knot rests on the weak thread and the linearization not on strict identity failing (the costume gate), (b) the weak thread is genuinely weak with SEVERED reachable (no fiat), and (d) the 1D line rests on the linearization import not on scalar rank.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the knot rests on strict identity failing rather than the weak thread and the linearization (the costume gate, audit (c)); the 1D-line claim rests on rank being scalar rather than the linearization import (audit d); the fork is a fiat (SEVERED excluded, or the weak thread is strict bisimilarity relabelled, audit (b)); persistence is asserted absolutely (audit a); a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a strict-failure dressed as a weak-thread interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `charter-extension.md`'s prose, `summary*.md`, and any file naming "self," "thread," "life." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the knot rests on the weak thread and the linearization not on strict identity failing, (b) the weak thread is genuinely weak with SEVERED reachable, and (d) the 1D line rests on the linearization import; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S6 P2S6.AxiomCheck   # compiles (P2S5/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-6/formal            # sorry-free (prose excepted)
lake build P2S6.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S6 + P2S5 + Mathlib)
grep -rniE "\b(self|thread|persistence|life|death|time|here|there|god|choice|subjectivity)\b" \
  ../program-2/series-6/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (THREADED / SEVERED / SHAPE-DRAWN / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. The honest expectation is SEVERED or SHAPE-DRAWN: strict identity fails, the single line is an import, and whether a weak thread is recoverable is self-relative and may be undecidable from within. THREADED, if a recoverable weak continuity genuinely exists, would say the self persists as an endogenous thread, reported in its direction and the reading rewritten rather than defended. Whichever falls, it is never reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. The thread this series builds is the self through time, re-woven each moment; the knot is whether the relating carries the weave, or it is imported. No em dashes in final academic copy.*
