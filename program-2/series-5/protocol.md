# Program 2 Series 5 (2.5), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.5 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The executor runs A, B, D, E, G directly; it spawns a reviewer for C and F and acts on the findings. The series builds THE FOLD (the topology of the whole: no poles, the largest bending into the smallest through the diagonal) and asks one knot: can the causal/temporal relation CLOSE into a loop, or is time acyclic even in a world whose relating cycles? It rebuilds no imported machinery; it constructs the fold and the causal relation FRESH on the Series 2.1 tick and the P1 diagonal. This is the second series of Phase 2 and is chartered under the Phase-2 costume gate: the knot is DIAGONAL/CYCLE-powered — the COEXISTENCE of cyclic relating and acyclic time — and the verdict must rest there, NOT on the well-foundedness of rank alone.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 2)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "time," "loop," "the fold," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (LOOPED, SHAPE-DRAWN, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target.

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("time," "loop," "causal," "fold," "pole," "cycle") and check whether the statement still goes through as a bare well-foundedness, cycle, self-membership, or `Recoverable` fact. What SHOULD survive: WS1's fold strips to "no leaf below, an unbounded rank-raising map above, and a self-membered / residue-point seam"; WS2 strips to "a directed cycle in the attention relation that reifies"; WS3 strips to "the reification-dependency is a subrelation of strict rank-increase, hence well-founded and acyclic on distinct states"; WS4 strips to "a closed cycle of the causal relation forces a self-constituting state (the diagonal), and a discriminating function over its status reaching more than one value."

4. **No pole or quantity asserted absolutely; the import quantified, not named.** No proof term asserts a topological quantity frame-independently where the self-relative discipline applies; the import (if any) stays quantified, never named. "Time" and "the fold" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "time," "loop," "causal," "fold," "pole," "self," "here," "there," "God," "choice," or "subjectivity" as content. Headlines mention only the reification-dependency relation, the rank, the attention cycle, the self-membered / residue point, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Three emphases specific to this series:

6. **The knot is the coexistence, not well-foundedness (the Phase-2 costume gate, PROMOTED first-class).** "Causation raises rank, rank is well-founded, so no loop" is a true fact but a COSTUME of the order structure — not the finding. The verdict must rest on the COEXISTENCE: the relating GENUINELY cycles (WS2) while causation GENUINELY does not (WS3), and the sole candidate for a closed loop is the fold (WS4). A payoff that strips to "a well-founded relation is acyclic," with no cyclic-relating content and no fold, is the costume. The reviewer presses hardest on audit (c): does the verdict rest on the coexistence and the fold, or only on rank being well-founded?

7. **The fork is genuine, never a fiat (no definitional acyclicity).** The causal relation must be the STRUCTURAL reification-dependency (a relatum minted from a pattern of others), and its acyclicity PROVED from the rank-lift, so that LOOPED — a self-constituting relatum at the fold — is a genuine reachable structure, not excluded by construction. A causal relation DEFINED as rank-increasing makes acyclicity a triviality and LOOPED impossible by fiat: the sin. The strip test and the LOOPED-reachable check are the guards. Audit (b).

8. **The fold is the diagonal, not the import (build the right engine).** The fold — the largest bending into the smallest — is the diagonal's work (`ws2_residue_free`, self-inspection's residue), not the import's. `ws1_fold` and `ws4_loop_only_at_fold` must rest on the P1 diagonal, not on a seated import, or the topology is a costume of Series 07. Audit (d).

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).**
- **`spec/README.md` (design index).** The imported chain, the primitives (the fold and the causal relation, built fresh), the discipline (knot on coexistence not well-foundedness, fork not by fiat, fold on the diagonal), the cross-workstream triage, the outcomes, the names-in-prose rule, and the candidate witness.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-4` (the predecessor, already built).** Reaching S3/S2/S1/S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S5` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold (`spec/`, `formal/`) created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `program-1/series-13/formal/Series13/*` for format and house style; **read `program-2/series-1/` in full** (the tick, causation, `ws4_causal_order_endogenous`, `ws1_cycle_reifies` — the cyclic relating and the rank-raising causation); **read `program-2/series-4/`** (the world carrier, `rankLift`, the reachability/`reachIn` path structure, the house pattern for a two-carrier fork W-vs-T); and **read the P1 diagonal** (`program-2/formal/P1/Reader.lean`: `ws2_residue_free`, `ws1_no_self_total_hold`, the residue — the fold's engine). Read `program-2/charter-extension.md` §3 (the costume gate). For each of WS1–WS5, write `spec/wsNN-design.md`: (1) list candidate constructions (the FOLD — the topology of the whole via the diagonal — and the CAUSAL RELATION as a structural reification-dependency are the key design objects; design the causal relation so its acyclicity is PROVED from the rank-lift, not definitional, and so LOOPED at the fold is genuinely reachable); (2) triage on paper against non-triviality, the strip test, the costume gate, and the audit clauses, recording rejected candidates; (3) write the winning construction to typed signatures; (4) fix the outcome classes; (5) annotate each payoff with what it SHOULD strip to. Write `spec/README.md`. Fix the `P2S5` module naming and record it. **Gate: commit all six files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): does the knot rest on the coexistence (cyclic relating + acyclic time) and the fold, or only on well-foundedness (the costume)? — and audit (b): is the causal relation structural, so acyclicity is proved and LOOPED reachable, or is it a fiat?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S5` namespace. **Build on Series 2.4**: `import P2S4` and use it and its transitive API (chiefly `P2S1`'s tick/causation and the P1 diagonal) — do NOT `import P2S3`/`P2S2`/`P2S1`/`P2S0`/`P1` directly (the layered chain; the gate enforces it). Build the fold and the causal relation FRESH.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S5`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S5"
srcDir = "../program-2/series-5/formal"
roots = ["P2S5", "P2S5.AxiomCheck"]
```
and append `"P2S5"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-5 "^import (P2S4|P2S5)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S4 and its own `P2S5.*` roots, plus Mathlib; below-S4 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S5.lean` (imports `P2S5.ws1`…`P2S5.ws5`), `P2S5/wsN.lean`, `P2S5/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the knot rests on the coexistence and the fold not on well-foundedness (the costume gate), (b) the causal relation is structural so acyclicity is proved and LOOPED reachable (no fiat), and (d) the fold rests on the diagonal not an import.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the knot rests on well-foundedness alone rather than the coexistence and the fold (the costume gate, audit (c)); the fork is a fiat (causation defined as rank-increasing, LOOPED excluded by construction, audit (b)); the fold rests on a seated import rather than the diagonal (audit (d)); the loop at the fold is decided without the computation; a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a well-foundedness fact dressed as a coexistence).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, `charter-extension.md`'s prose, `summary*.md`, and any file naming "time," "loop," "the fold." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension.md`, `summary*.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the knot rests on the coexistence and the fold not on well-foundedness, (b) the causal relation is structural so acyclicity is proved and LOOPED reachable, and (d) the fold rests on the diagonal; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S5 P2S5.AxiomCheck   # compiles (P2S4/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-5/formal            # sorry-free (prose excepted)
lake build P2S5.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S5 + P2S4 + Mathlib)
grep -rniE "\b(time|loop|causal|fold|pole|self|here|there|god|choice|subjectivity)\b" \
  ../program-2/series-5/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (ACYCLIC / LOOPED / SHAPE-DRAWN / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. ACYCLIC is the expected close: the relating loops but time does not, causation spirals up, and the fold's self-reference is a degenerate fixed point rather than a genuine closed timelike curve. LOOPED, if the fold turns out to be a real causal loop, is the strange finding that time closes at the One, reported in its direction and the reading rewritten rather than defended. SHAPE-DRAWN, if the fold is the sole candidate but its status undecidable, is the honest terminus, drawn exactly and never reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. The fold this series builds is the shape of the whole; the loop is whether time can close on it. No em dashes in final academic copy.*
