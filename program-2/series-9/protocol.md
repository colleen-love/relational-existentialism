# Program 2 Series 9 (2.9), Protocol

**The process, self-contained. This protocol takes Series 2.9 from an empty `formal/` to a computed verdict with no delegation except the two blind review phases (C and F, section 5). The series asks one recovery question: is there a maximal rate at which attention-breadth becomes reification-depth — a LIGHT CONE and a c? It rebuilds no imported machinery; it constructs the RATE and its CONE FRESH, earned from finite attention, on the imported chain (`P2S8` reaching the whole tower transitively). This is the first recovery test of Phase 3 and one of two tier-1 probes; it runs IN PARALLEL with Series 2.10 (The Reversal), independent of it. It is chartered under Phase 3's no-smuggling gate: the rate must be EARNED from finite attention (Series 2.0), never postulated as a c and re-found; and the cone must carry a genuine rate, never relabel Series 2.5's causal order. NO-CONE is a pre-registered honorable NOT-RECOVERED.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 3)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "light," "cone," "speed of light," "relativity," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (NO-CONE, SHAPE-DRAWN, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **NO-CONE — the rate is unbounded, the model is non-relativistic — is a genuine outcome and a specification for the next iteration, not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built, or **(Relabeled)** the target was not built, the obstruction recorded, the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("light," "cone," "speed," "rate") and check whether the statement still goes through as a bare bound / reachable-set / metric fact. WS1's rate strips to "a finite bound on breadth-per-tick, a function of the attention bound"; WS2's cone strips to "the set reachable within bound×steps in the lateral metric, with something strictly outside"; WS3's content strips to "two carriers, same reachability order, different bound, different reachable set."

4. **The recovery is earned, not smuggled (the Phase-3 no-smuggling gate).** No proof term POSTULATES a maximal speed; the bound is a function of the finite attention (Series 2.0), proved finite, not assumed. "Light," "cone," "c" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "light," "cone," "speed," "relativity," "spacetime," "self," "import," "God," or "compass" as content. Headlines mention only the rate (a neutral-named bound), the reachable set, the lateral metric, the causal order, the attention bound, the transcribed machinery, and standard Lean/Mathlib.

Four emphases specific to this series:

6. **The rate is EARNED from attention (the no-smuggling gate, PROMOTED first-class).** The bound must be a function of the Series 2.0 finite-attention limiter, not a numeric cap added to obtain the cone. The reviewer presses hardest on audit (a): is the rate a genuine consequence of finite attention, or a postulated c?

7. **The cone is a RATE, not the bare order (the costume gate).** Series 2.5 already has causal reachability. The cone must carry a rate (a ratio of 2.4's breadth to 2.1's depth): same order, different rate, different cone. A cone that strips to the causal reachable set is the costume. Audit (c).

8. **The cone is NON-TRIVIAL.** Some events must be strictly OUTSIDE the cone on the witnessing carrier — a genuine finite speed. A cone that is the whole world is no cone. Audit (d).

9. **NO-CONE is honorable.** If the rate is not bounded by attention, the series lands NO-CONE — the honest report that the model as built is non-relativistic — reported in full, never relabelled into a pseudo-cone.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).
- **`spec/README.md` (design index).** The imported chain, the primitive (the rate and its cone, built fresh and earned from attention), the discipline (rate earned not smuggled, cone is a rate not the order, cone non-trivial, NO-CONE honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/rate-derisking.md` (this series, before the WS designs).** The paper hunt: candidate rate definitions from finite attention, and for each, the by-hand test that (a) it is genuinely bounded by the attention limiter, (b) it gives a non-trivial cone (something outside), and (c) it distinguishes carriers with the same order but different rates. Only a rate that survives earns the WS designs; if none is bounded, land NO-CONE.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-8` (the predecessor, already built).** Reaching S7–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S9` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format and house style; **read `program-2/series-0/`** (finite attention, the bound); **read `program-2/series-1/`** (the tick, reification); **read `program-2/series-4/`** (the lateral metric, the two axes); **read `program-2/series-5/`** (the causal order — the skeleton this series rate-limits and exceeds). Read `program-2/charter-extension-2.md` §3 (the no-smuggling gate) and §4 (2.9). **Then write `spec/rate-derisking.md`** (the paper hunt above). Only a bounded, non-trivial, order-exceeding rate earns the WS designs; else land NO-CONE (record the obstruction, skip to the NO-CONE verdict at WS5). If a rate survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage, the strip test, the no-smuggling gate, the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S9` module naming and record it. **Gate: commit `spec/rate-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (a): is the rate EARNED from finite attention or postulated? — audit (c): is the cone a genuine rate or a relabel of the causal order? — and audit (d): is the cone non-trivial (something outside)?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S9` namespace. **Build on Series 2.8**: `import P2S8` and use it and its transitive API (chiefly S0's attention bound, S1's tick, S4's metric, S5's order) — do NOT `import P2S7`/…/`P1` directly (the layered chain; the gate enforces it). Build the rate FRESH, earned from attention.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S9`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S9"
srcDir = "../program-2/series-9/formal"
roots = ["P2S9", "P2S9.AxiomCheck"]
```
and append `"P2S9"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-9 "^import (P2S8|P2S9)(\.[A-Za-z0-9_]+)*$"`. Lay out `formal/` as `P2S9.lean` (imports `P2S9.ws1`…`P2S9.ws5`), `P2S9/wsN.lean`, `P2S9/AxiomCheck.lean`, mirroring `program-2/series-8/formal/P2S8/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (a) the rate earned from attention not smuggled, (c) the cone a genuine rate not the bare order, and (d) the cone non-trivial.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the rate is SMUGGLED (a postulated c, not earned from attention — audit a, the phase sin); the cone rests on the bare causal order (the costume, audit c); the cone is trivial (audit d); the fork is a fiat; a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, an order-fact dressed as a rate).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the relativity prose, `charter-extension-2.md`'s prose, `summary*.md`, `rate-derisking.md`, and any file naming "light," "cone," "speed." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension-2.md`, `summary*.md`, `rate-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names grep; confirm the audit clauses, ESPECIALLY (a) the rate earned from attention, (c) the cone a genuine rate not the order, and (d) the cone non-trivial; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction. If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S9 P2S9.AxiomCheck   # compiles (P2S8/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-9/formal            # sorry-free (prose excepted)
lake build P2S9.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S9 + P2S8 + Mathlib)
grep -rniE "\b(light|cone|speed|relativity|spacetime|self|import|god|compass)\b" \
  ../program-2/series-9/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely; the Lean `import` keyword is exempt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (CONE / NO-CONE / SHAPE-DRAWN / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. CONE is the expected close: finite attention is a maximal rate of becoming, and relativity's light cone is the shadow of a bounded capacity to attend. NO-CONE, if the rate is unbounded, is the honest finding that the model as built is non-relativistic, and the specification for the next iteration (add a fundamental rate-bound). SHAPE-DRAWN joins the standing opens. None is reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point. The cone this series builds is relativity's first pillar tested against the model; the knot is whether finite attention already limits the rate of becoming. Phase B must earn the rate from attention on paper before it is built, and NO-CONE is honorable. Runs in parallel with Series 2.10 (The Reversal). No em dashes in final academic copy.*
