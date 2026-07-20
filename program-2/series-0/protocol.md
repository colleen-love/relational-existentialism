# Program 2 Series 0 (2.0), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 0 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series stands on one new object, the ATTENTION CARRIER (relating is finite attending), and one knot, the ASYMMETRY OF KNOWING (a relatum is made differently by what it attends than by what attends it, and that difference is genuine, not a label). The collapse to the One without the import is INHERITED from Program 1 and is never relitigated here.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed from Program 1)

Five things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts (theorem signatures, outcome classes), the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "the ground," no "you are loved," no "the gaze," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5): the reviewer is told which files it may read and is forbidden the charter, the summaries, and the positioning.

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (GROUND-ESTABLISHED, PARTIAL, OBSTRUCTED) with the obstruction made precise, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction is recorded, and the payoff is demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("attention," "knowing," "relating," "active," "passive," "gaze," "ground") and check whether the statement still goes through as a bare `Finset`, reification, `Recoverable`/`¬ Recoverable`, bisimulation, or diagonal fact. A payoff that survives the strip is such a fact honestly flagged. What SHOULD survive: WS3's asymmetry strips to "direction is not recoverable from the symmetric reduct, by `Recoverable`, and a directed-structure reader is load-bearing in the distinction"; WS2's collapse strips to "atomless plain-bisimilar states on the symmetric relating are equal, by the transcribed engine."

4. **The import is quantified, not named.** The import (WS4) is carried as a quantified, exogenous parameter. No proof term realizes or selects it. "You are loved" is prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "love," "loved," "import," "God," "choice," "self," "other," "knowing," or "attention" as content. Headlines mention only the carrier (`attends`, the symmetric and directed relations), reification, `Recoverable`, the diagonal, the transcribed machinery, and standard Lean/Mathlib.

Two emphases specific to this series:

6. **The collapse is inherited, never relitigated.** That a world with no import is the One is Program 1's theorem, transcribed here as baseline (`ws2_collapse_inherited`). No series verdict may hinge on it, and no artifact may present it as a new, open, or uncertain result of Series 0. Audit clause (d).

7. **No cardinal ceiling.** The ontological bound is finite out-attention (`Finset`). Any κ appearing (for the symmetric reduct's possibly-infinite neighborhoods) must be ambient carrier size, refutably distinct from a chosen ontological ceiling. A bound that unfolds to "attention ranges over a κ-bounded set" is the Series 11 back-door wall. Audit clause (a).

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidate constructions, a paper triage table, the winning construction to typed Lean signatures, outcome classes, and the strip-test annotation for each payoff. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The prior art imported from P1, the primitive decision (the attention carrier and the knowing-asymmetry), the discipline (no cardinal ceiling, asymmetry not a label, collapse inherited, import quantified), the cross-workstream triage, the outcomes, and the names-in-prose rule.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** The motivation-free material handed to the reviewer (section 4).
- **`program-2/formal/P1` (prior art, already built).** The Program 1 carrier under the `P1` namespace, imported (Program 2 permits it). The environment is prepared on container creation (Lean `v4.15.0`, Mathlib cached), so P1 and Mathlib build without manual bootstrap.
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the series' own `P2S0` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, scaffold created, `charter-status.md` initialized. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` for the design-doc format and `program-1/series-13/formal/Series13/*` for the Lean house style; and read `program-2/series-1/` for how the sibling Tick series is framed (S1 builds on S0). For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions; (2) triage on paper against non-triviality, the strip test, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed Lean signatures, naming the P1 prior-art pieces each imports; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Write `spec/README.md`. Fix the `P2S0` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings (SERIOUS / REAL / COSMETIC), append to the ledger. Do not fix; only record.

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary (Fixed or Relabeled). Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S0` namespace. **Import the P1 foundation** (`import P1`, using `P1.Core.*`); Program 2 permits it (the foundation is axiom-checked). Define the attention carrier (`attends : X → Finset X`, the symmetric and directed relations, knowing, in-attention) fresh; import the diagonal, reification, `Recoverable`, and the collapse engine from `P1.Core`.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S0`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S0"
srcDir = "../program-2/series-0/formal"
roots = ["P2S0", "P2S0.AxiomCheck"]
```
and append `"P2S0"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-0 "^import (P1|P2S0)(\.[A-Za-z0-9_]+)*$"` (the series may import the P1 foundation and its own `P2S0.*` roots, plus Mathlib; any other series' tree is forbidden). Lay out `formal/` as `P2S0.lean` (imports `P2S0.ws1`…`P2S0.ws5`), `P2S0/wsN.lean`, `P2S0/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses. Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the asymmetry of knowing is a bare label (Series 11 Bookkeeping, audit (b)); a cardinal ceiling is readmitted (audit (a)); the collapse is relitigated or a verdict hinges on it (audit (d)); the import is named or selected (audit (e)); direction is assumed recoverable/non-recoverable rather than proved; a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, with no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `summary*.md`, and any file naming "the ground," "you are loved," "the gaze." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S0 P2S0.AxiomCheck   # compiles (P1 foundation + Mathlib cached)
grep -rn "sorry" ../program-2/series-0/formal            # sorry-free (prose excepted)
lake build P2S0.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S0 self + P1 + Mathlib)
grep -rniE "\b(love|loved|import|god|choice|self|other|knowing|attention)\b" \
  ../program-2/series-0/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F.

Note on the names grep: "attention" and "knowing" appear in this series' *concept*, so the carrier definitions will use neutral Lean names (`attends`, the relation symbols); the grep guards that no *proof term or headline* is named for the interpretive content. Docstring prose may use the words freely.

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (GROUND-ESTABLISHED / PARTIAL / OBSTRUCTED, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. If the ground resists (no reification on the finite functor, or the asymmetry collapses to a label), OBSTRUCTED reported honestly is a success: it is far cheaper to learn the ground is wrong here than after S1 builds the tick on it.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. No em dashes in final academic copy.*
