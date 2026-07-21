# Program 2 Series 4 (2.4), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.4 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series builds THE WORLD (a genuine lateral population of same-rank import-distinguished peers with a local attention graph) and asks one knot: is the LATERAL axis (breadth, a directed distance) genuinely DISTINCT from the VERTICAL axis (reification depth, rank), or does it REDUCE to it (space is time seen sideways). It rebuilds no imported machinery; it constructs the world FRESH on the Series 2.0 attention carrier and grounds the space on Series 07. Every distance is stated FOR a self; no distance is asserted absolutely. This is the first series of Phase 2 and is chartered under the Phase-2 costume gate: the knot is AXIS-BUILDING, and the verdict must rest on axis-independence, not on the import-powered existence of many.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 2)

Seven things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "space," "world," "here/there," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (REDUCED, SHAPE-DRAWN, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("space," "distance," "axis," "world," "lateral," "breadth") and check whether the statement still goes through as a bare graph-metric, order-independence, bisimulation, or `Recoverable` fact. What SHOULD survive: WS1's world strips to "a set of same-rank states, pairwise non-recoverable, with a non-complete reachability relation"; WS2's independence strips to "the reachability-distance and the rank grading are not functions of each other"; WS3's import strips to "a distance-greater-than-one pair is `¬ Recoverable`, by Series 07"; WS4's fork strips to "a discriminating function over the axis-independence, reaching two values, both witnessed."

4. **No distance asserted absolutely; the import quantified, not named.** No proof term states a distance frame-independently; every metric claim is FOR a self, and a global metric is claimed only where forced (Phase-2 self-relative discipline). The import a lateral separation is stays quantified, never named. "Space" is prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "space," "distance," "world," "here," "there," "self," "time," "God," "choice," or "subjectivity" as content. Headlines mention only the peers, the two gradings (a reachability-distance and the rank), the reachability relation, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Two emphases specific to this series:

6. **The knot is axis-independence, not multiplicity (the Phase-2 costume gate, PROMOTED first-class).** The existence of many peers is import-powered — it is Series 07, the acknowledged GROUND, and it is NOT the finding. The verdict must rest on the INDEPENDENCE of the lateral axis from the vertical (WS2, WS4). A payoff that strips to "a genuine distinction is an import," with no axis-independence content, is a costume of the import theorem. The reviewer presses hardest on audit (c): does the verdict rest on axis-independence, or only on the fact that there are many?

7. **The fork is genuine, never a fiat, and the reduction is real (no tautology).** REDUCED must be genuinely reachable: the two-axes distinctness must NOT hold by typing on every structure, and the reduction must NOT be excluded by construction. Both a lateral-move-without-rank-change and a rank-move-without-lateral-change must be witnessed on the world, and the verdict must be a discriminating function reaching more than one value. The strip test and the both-moves witness are the guards. Audit (b).

Two watches carried from the charter (§4.a, §4.d):

8. **No absolute frame.** Every metric claim is stated for a self; a global, view-from-nowhere distance is the plain layer, which is the One. Audit (a).

9. **Distance is not disguised counting.** The breadth-metric must be genuinely path-based on a LOCAL (non-complete) attention graph, not the count of import-labels between peers. If the metric strips to bare label-counting, it is number, not space. Audit folded into the strip test.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The imported chain, the primitives (the world and the two gradings, built fresh), the discipline (fork genuine, no absolute frame, knot on axis-independence not multiplicity, distance not disguised counting), the cross-workstream triage, the outcomes, the names-in-prose rule, and the candidate witness world.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-3` (the predecessor, already built).** Reaching S2/S1/S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S4` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold (`spec/`, `formal/`) created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `program-1/series-13/formal/Series13/*` for format and house style; **read `program-2/series-2/` in full** (the lateral texture — the incomparable reaches and the same-rank peers `slf`/`p`/`q` at rank 0 are the seed of the world); **read `program-2/series-0/`** (the attention carrier, the directed knowing `ws3_direction_not_recoverable`, the rank machinery); and **read `program-2/series-1/`** (the tick, the template for a granular self-relative quantity). Read `program-2/charter-extension.md` §3 (the costume gate) and `program-1/spec/program-review-1.md` (the tautology traps). For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions (the WORLD — a lateral population of same-rank peers with a local attention graph — and the breadth-DISTANCE are the key design objects; weigh a directed ring/line/graph so distance has structure and directedness); (2) triage on paper against non-triviality, the strip test, the costume gate, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed signatures; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Design the witness world to make both the lateral-move-without-rank and the rank-move-without-lateral genuinely present, and REDUCED genuinely reachable. Write `spec/README.md`. Fix the `P2S4` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): does the knot rest on axis-independence, or only on the multiplicity (Series 07, the costume)? — and audit (b): is the fork genuine or a fiat?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S4` namespace. **Build on Series 2.3**: `import P2S3` and use it and its transitive API (chiefly `P2S0`'s attention carrier and `P2S2`'s lateral texture) — do NOT `import P2S2`/`P2S1`/`P2S0`/`P1` directly (the layered chain; the gate enforces it). Build the world and the two gradings FRESH on the attention carrier.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S4`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S4"
srcDir = "../program-2/series-4/formal"
roots = ["P2S4", "P2S4.AxiomCheck"]
```
and append `"P2S4"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-4 "^import (P2S3|P2S4)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S3 and its own `P2S4.*` roots, plus Mathlib; below-S3 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S4.lean` (imports `P2S4.ws1`…`P2S4.ws5`), `P2S4/wsN.lean`, `P2S4/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the knot rests on axis-independence not multiplicity (the costume gate), (b) the fork is genuine with REDUCED reachable, and (a) no distance is asserted absolutely.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the knot rests on the multiplicity rather than axis-independence (the costume gate, audit (c)); the fork is a fiat (distinctness by typing, or REDUCED excluded by construction, audit (b)); a distance is asserted absolutely (audit (a)); the breadth-metric strips to bare import-label counting (distance-as-number, §4.d); a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a metric axiom quietly assumed).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `charter-extension.md`'s prose, `summary*.md`, and any file naming "space," "world," "here/there." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the knot rests on axis-independence not the multiplicity, (b) the fork is genuine with REDUCED reachable, and (a) no absolute distance; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S4 P2S4.AxiomCheck   # compiles (P2S3/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-4/formal            # sorry-free (prose excepted)
lake build P2S4.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S4 + P2S3 + Mathlib)
grep -rniE "\b(space|distance|world|here|there|self|time|god|choice|subjectivity)\b" \
  ../program-2/series-4/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (DISTINCT / REDUCED / SHAPE-DRAWN / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. DISTINCT is the expected close: the world is genuinely lateral, the two axes come apart, and space is a real directed granular self-relative axis distinct from time. REDUCED, if same-rank peers collapse or breadth is only accumulated depth, is the honest finding that space and time are one axis, extension being disguised succession, reported in full and the Phase-2 thesis re-examined rather than defended, never reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. The world this series builds is the ground the rest of Phase 2 inherits. No em dashes in final academic copy.*
