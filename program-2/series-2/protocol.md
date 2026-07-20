# Program 2 Series 2 (2.2), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.2 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series stands on one new object, the OTHER as a second attending locus, and one knot, MUTUAL READING WITHOUT COLLAPSE (do two perspectives reading each other and themselves collapse, totalize, or leave a residue). The collapse to the One without an import is INHERITED from Program 1 and is never relitigated; the COHERENCE of the two readings is deferred to Series 2.3 and must never be decided here.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed from Program 1)

Five things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts (theorem signatures, outcome classes), the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "the other," "the face," "you are loved," "the gaze," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5): the reviewer is told which files it may read and is forbidden the charter, the summaries, and the positioning.

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (TWO-FACING, ONE, TOTALIZED, PARTIAL, DISCONNECTED) with the obstruction made precise, never a quiet redefinition of the target.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction is recorded, and the payoff is demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("self," "other," "perspective," "reading," "face," "mutual") and check whether the statement still goes through as a bare `attends`, `RealFor` / `AttentionDistinguishes`, `Recoverable` / `¬ Recoverable`, bisimulation, diagonal, or reification fact. A payoff that survives the strip is such a fact honestly flagged. What SHOULD survive: WS2's twoness strips to "a second reader for which a relatum is `RealFor`, and the separation is `¬ Recoverable`"; WS4's residue strips to "under the mutual-reading inspection, no self-total hold, by the diagonal."

4. **The import is quantified, not named; no reading is evaluated.** The symmetry-breaker separating self from other is a quantified, exogenous parameter; no proof term realizes or selects it. No reading is selected, constructed, or evaluated; theorems are quantified over the perspectives' attentions. "You are loved" is prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "self," "other," "I," "you," "perspective," "love," "loved," "gaze," "God," "choice," or "subjectivity" as content. Headlines mention only the two loci, their `attends`, the readings, `RealFor` / `AttentionDistinguishes`, `Recoverable`, the diagonal, the transcribed machinery, and standard Lean/Mathlib.

Three emphases specific to this series:

6. **The other is a reader, never a label (K1, the central sin, PROMOTED first-class).** The other is an attending locus whose READING does the distinguishing. If the second perspective's `attends` goes inert, or the distinction is a point-tag, or the reader is quantified out of the payoff, the other is decoration and the series has built the self twice — the Series 11 Bookkeeping / PR1-S2 failure, sharpest here because the other IS the reader. `ws2_other_reader_wise` names a genuine reader. Audit (a).

7. **The twoness is non-recoverable, and the coherence is untouched.** The self/other distinction must be `¬ Recoverable` (an import, Series 07) — recoverable twoness is the collapse smuggled shut. And no theorem, definition, or discharged obligation may decide the COHERENCE of the two readings (`Converges₂`, Series 2.3's question); the faces are typed and non-evaluated, the coherence left open. Deciding it is the central sin of the NEXT series done early, SERIOUS. Audit (b), (d — the coherence-open check).

8. **The mutual residue is TESTED, not assumed.** WS4 must not assume mutual reading behaves like self-inspection. The fork (COLLAPSE / TOTALIZED / RESIDUE) must be genuinely open on a witnessed pair with a real mutual-reading structure, both the collapse and residue arms reachable, the reading-order structurally constrained. An unconstrained reading type that decides the fork on every structure is the PR1-S1 tautology. Audit (d).

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidate constructions, a paper triage table, the winning construction to typed Lean signatures, outcome classes, the strip-test annotation for each payoff. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The imported ground (`P2S1` reaching `P2S0` / `P1`), the primitive decision (the other as a second locus, the four readings, the mutual-reading structure), the discipline (reader not label, twoness non-recoverable, coherence untouched, residue tested), the cross-workstream triage, the outcomes, and the names-in-prose rule.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** The motivation-free material handed to the reviewer (section 4).
- **`program-2/series-1` (the ground, already built).** The tick, reaching S0 and P1. The environment is prepared on container creation (Lean `v4.15.0`, Mathlib cached), so the ground and Mathlib build without manual bootstrap.
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the series' own `P2S2` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, scaffold created, `charter-status.md` initialized. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `program-1/series-13/formal/Series13/*` for format and house style; and **read `program-2/series-1/` and `program-2/series-0/` in full** — S2 builds on their actual API (`attends`, `ws1_first_other`, `knowLiftD` / `ws3_direction_not_recoverable`, `rankLift`, `impLift`, `RealFor` / `AttentionDistinguishes`, the tick). For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions (the shared witness of two loci and their readings is the key design object); (2) triage on paper against non-triviality, the strip test, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed Lean signatures; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Write `spec/README.md`. Fix the `P2S2` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings (SERIOUS / REAL / COSMETIC), append to the ledger. Do not fix; only record.

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary (Fixed or Relabeled). Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S2` namespace. **Build on the Series 2.1 ground**: `import P2S1` and use it and its transitive API (`P2S0.*`, `P1.*` reachable through it) — do NOT `import P2S0` or `P1` directly (the layered chain; the gate enforces it). Construct the two loci, their readings, and the mutual-reading structure as the shared witness.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S2`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S2"
srcDir = "../program-2/series-2/formal"
roots = ["P2S2", "P2S2.AxiomCheck"]
```
and append `"P2S2"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-2 "^import (P2S1|P2S2)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S1 and its own `P2S2.*` roots, plus Mathlib; S0 and P1 are reached transitively; any other tree is forbidden). Lay out `formal/` as `P2S2.lean` (imports `P2S2.ws1`…`P2S2.ws5`), `P2S2/wsN.lean`, `P2S2/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

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

- **SERIOUS:** the verdict rests on it; the other is a bare label / the reader quantified out (K1, audit (a)); the twoness is recoverable (the collapse smuggled shut, audit (b)); the mutual residue is decided by fiat (PR1-S1 tautology, audit (d)); the coherence of the two readings is decided (Series 2.3's question, foreclosed early); the import is named or a reading evaluated; a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a bare conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `summary*.md`, and any file naming "the other," "the face," "you are loved." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, especially (a) the reader is load-bearing and (d) the mutual residue is tested not assumed and the coherence is untouched; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S2 P2S2.AxiomCheck   # compiles (P2S1/P2S0/P1 + Mathlib cached)
grep -rn "sorry" ../program-2/series-2/formal            # sorry-free (prose excepted)
lake build P2S2.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S2 + P2S1 + Mathlib)
grep -rniE "\b(self|other|perspective|love|loved|gaze|god|choice|subjectivity)\b" \
  ../program-2/series-2/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (Note: "self"/"other" appear in this series' concept, so the carrier definitions use neutral Lean names; the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (TWO-FACING / ONE / TOTALIZED / PARTIAL / DISCONNECTED, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. If mutual reading collapses or totalizes (the other not genuinely two, or one closing the pair), ONE / TOTALIZED reported honestly is a success: it would be the program's finding that a genuine other needs more than the ground supplies, and it is far cheaper to learn it here than after Series 2.3 builds the coherence fork on two faces that were not really two.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. No em dashes in final academic copy.*
