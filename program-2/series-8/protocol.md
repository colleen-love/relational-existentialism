# Program 2 Series 8 (2.8), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.8 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The series asks one knot: across many selves, does local pairwise coherence GLUE into a global good, or can it be FRUSTRATED — every pair reconciled, yet no global section? It rebuilds no imported machinery; it constructs the GOOD, the RECONCILIATION, and the HOLONOMY/COCYCLE FRESH on the world (Series 2.4, reached transitively) and the directed knowing-asymmetry, and puts local-coherence-gluing on trial as a many-body cocycle. This is the fifth and last series of Phase 2, the value CAPSTONE. It is chartered under the Phase-2 costume gate, doubled: the knot is a genuinely MANY-BODY cocycle — neither import-powered (Series 07) NOR a replay of the single edge (Series 2.3) — and its reconciliations must be DERIVED FROM THE MODEL (the directed attention), never bolted on, the lesson Series 2.7 taught at cost (finding T1-S1). No global good is asserted; the global fails at the capstone, as general relativity and Series 2.7 foretold.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 2)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "good," "common," "value," "justice," no metaphysics, no Condorcet or sheaf prose. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (GLUABLE, SHAPE-DRAWN, PAIRWISE-ONLY, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **PAIRWISE-ONLY — the obstruction is not genuinely many-body, i.e. Series 2.3 replayed — and DISCONNECTED — no non-trivial good survives — are genuine outcomes, not failures to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING. (Series 2.7's T1-S1 is the canonical instance: a CONSERVED-RELATIVE costume was Relabeled to the pre-registered MONOTONE-ONLY with the obstruction proved, NOT closed by an adjacent weaker theorem. This series inherits that standard in full.)

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("good," "common," "value," "justice," "consensus," "reconciliation") and check whether the statement still goes through as a bare valuation / transition / cocycle / global-section fact. What SHOULD survive: WS1's good strips to "a function on selves taking two distinct values"; WS2's coherence strips to "for every pair, a transition aligning the two functions exists"; WS3's many-body-ness strips to "the composed transition around a 2-chain is identity, and the reconciliations are read off the directed carrier"; WS4's crux strips to "the composed transition around a 3-cycle is / is not the identity, both reachable, so a simultaneous global assignment does / does not exist."

4. **No global good asserted; the import quantified, not named.** No proof term asserts a globally forced good; the good is FOR a self, glued only where the cocycle vanishes (Phase-2 self-relative discipline, its capstone). Any import that appears stays quantified, never named. "Good," "common," "value" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "good," "common," "value," "justice," "consensus," "ethics," "self," "import," "God," "love," or "compass" as content. Headlines mention only the valuation (a neutral-named function), the transition/reconciliation (a neutral-named map), the holonomy/cocycle, the population, the directed reading, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Four emphases specific to this series:

6. **The knot is a genuine many-body cocycle, not a single edge and not import-ness (the Phase-2 costume gate, DOUBLED and PROMOTED first-class).** A single-edge fact is Series 2.3; an import fact is Series 07; both are costumes. The verdict must rest on the HOLONOMY of the reconciliations around a CYCLE (WS4), a phenomenon that VANISHES for two selves (WS3). A payoff that strips to "these two cohere / do not," or to "that is an import," with no cycle-level gluing content, is the costume. The reviewer presses hardest on audit (c): does the verdict rest on a genuine many-body cocycle, or on a single edge / import-ness?

7. **The reconciliations are model-derived, not bolted on (the Series 2.7 lesson, first-class).** The reconciliation between two selves, and the holonomy around a cycle, must be READ OFF the model — the directed mutual attention, the built world — not free permutations or an abstract cocycle chosen to frustrate. A frustration carried by a structure disconnected from the good (the `Finset.card`/`insert` counter that sank 2.7's first landing) is the costume. The reviewer presses on audit (c) and (d): are the reconciliations derived from the directed carrier, and does the strip test leave a fact about THAT structure rather than a bolted-on gadget?

8. **No global good, and the global's failure is the finding (the phase thesis).** No theorem asserts a globally forced good the structure does not force. The good glues only where the cocycle vanishes; a global good is claimed only if forced (GLUABLE), reported honestly and the positioning rewritten. Audit (a).

9. **PAIRWISE-ONLY and DISCONNECTED are honorable.** If Phase B's paper de-risking finds no non-trivial good (DISCONNECTED), or an obstruction that degenerates to a single edge (PAIRWISE-ONLY), the series lands there — the honest finding — reported in full, never relabelled into a pseudo-many-body claim.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate), AND only after the good and the model-derived frustration have been de-risked on paper (the Phase B gate for this series).**
- **`spec/README.md` (design index).** The imported chain, the primitive (the good, the reconciliation, the holonomy, built fresh and de-risked), the discipline (no global good, knot on the many-body cocycle not a single edge or import-ness, reconciliations model-derived, PAIRWISE-ONLY and DISCONNECTED honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/frustration-derisking.md` (this series only, before the WS designs).** The paper hunt for the good and the model-derived frustration: candidate goods (self-relative valuations on the population), and for each, the by-hand test that (a) it is non-trivial, and (b) a concrete three-self population with MODEL-DERIVED directed reconciliations exhibits a non-trivial triangle holonomy (frustration) AND a vanishing one (gluing). Only a candidate that survives earns the WS designs. If the good is trivial, this file records the obstruction and the series lands DISCONNECTED; if the obstruction is only pairwise, it lands PAIRWISE-ONLY.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-7` (the predecessor, already built).** Reaching S6–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S8` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold (`spec/`, `formal/`) created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
**This series' Phase B begins with the frustration de-risking, and does NOT proceed to the WS designs until a non-trivial good AND a model-derived frustration survive.** Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format and house style; **read `program-2/series-4/`** (the world — the lateral population of peers, the metric, the directed distance); **read `program-2/series-2/` and `program-2/series-0/`** (the other, the directed knowing-asymmetry); **read `program-2/series-3/`** (`Converges₂`, `Valuation`, `Faithful₂`, `InSight` — the single-edge coherence datum this series uses locally and exceeds at the network); and **read `program-2/series-7/`** (the ledger, and ESPECIALLY `charter-status.md` finding T1-S1 and `formal/P2S7/ConservedRelativeAttempt.lean` — the anatomy of a disconnected-counter costume and how it was caught, the exact trap WS3 must avoid). Read `program-2/charter-extension.md` §3 (the costume gate) and §2.8. **Then write `spec/frustration-derisking.md`**: propose candidate goods (self-relative valuations on a ≥3 population), and for each, test BY HAND (a) is it non-trivial and genuinely self-relative (not a relabelling of 2.4's metric or 2.3's convergence), and (b) do MODEL-DERIVED directed reconciliations on a concrete three-self population exhibit a non-trivial triangle holonomy (frustration, no global section) AND a vanishing one (gluing, a global section)? Record rejected candidates. Only a good that survives both earns the WS designs; if the good is trivial land DISCONNECTED, if the obstruction is only pairwise land PAIRWISE-ONLY (record the obstruction, skip to that verdict at WS5). If a good survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage against non-triviality and many-body-ness, the strip test, the doubled costume gate, the model-derived check, and the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S8` module naming and record it. **Gate: commit `spec/frustration-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): is the knot a genuine many-body cocycle (vanishing for two selves), or a single edge / import-ness (the doubled costume)? — is the reconciliation MODEL-DERIVED or bolted on (the T1-S1 trap)? — audit (b): is the good non-trivial and self-relative, or rigged? — and audit (a): is any globally forced good asserted?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S8` namespace. **Build on Series 2.7**: `import P2S7` and use it and its transitive API (chiefly the world of Series 2.4, the directed reading of Series 2.0/2.2, and the coherence datum of Series 2.3) — do NOT `import P2S6`/…/`P1` directly (the layered chain; the gate enforces it). Build the good, the reconciliation, and the holonomy FRESH, model-derived, independently of whether they frustrate.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S8`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S8"
srcDir = "../program-2/series-8/formal"
roots = ["P2S8", "P2S8.AxiomCheck"]
```
and append `"P2S8"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-8 "^import (P2S7|P2S8)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S7 and its own `P2S8.*` roots, plus Mathlib; below-S7 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S8.lean` (imports `P2S8.ws1`…`P2S8.ws5`), `P2S8/wsN.lean`, `P2S8/AxiomCheck.lean`, mirroring `program-2/series-7/formal/P2S7/`. **If an on-record attempt file is written (e.g. a genuine GLUABLE attempt, as 2.7 wrote `ConservedRelativeAttempt.lean`), add it as a `roots` entry too, so `lake build` compiles it — the standalone-but-unbuilt gap noted at the 2.7 landing must not recur.**

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the knot rests on a genuine many-body cocycle (vanishing for two selves) with model-derived reconciliations, not a single edge / import-ness / a bolted-on gadget (the doubled costume gate and the T1-S1 trap), (b) the good is non-trivial and self-relative (not rigged), and (a) no globally forced good is asserted.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push. (As the terminal series of Phase 2, the exit also warrants a note to Tier 1 that the phase is ready to be composed at the program level.)

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; a globally forced good is asserted the structure does not force (audit a, the phase sin); the knot rests on a single edge (Series 2.3) or import-ness (Series 07) rather than a genuine many-body cocycle (the doubled costume gate, audit c); the reconciliations are bolted on rather than model-derived (the T1-S1 trap, audit c/d); the good is trivial or rigged (audit b); the fork is a fiat (FRUSTRATED or GLUABLE excluded by construction); a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a single-edge fact dressed as a cocycle interaction, a reconciliation whose model-derivation is asserted in prose but not carried in the term).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, the Condorcet/sheaf prose, `charter-extension.md`'s prose, `summary*.md`, `frustration-derisking.md`, and any file naming "good," "common," "value," "justice." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension.md`, `summary*.md`, `frustration-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the knot is a genuine many-body cocycle with model-derived reconciliations, not a single edge / import-ness / a bolted-on gadget, (b) the good is non-trivial and self-relative, and (a) no globally forced good is asserted; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S8 P2S8.AxiomCheck   # compiles (P2S7/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-8/formal            # sorry-free (prose excepted)
lake build P2S8.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S8 + P2S7 + Mathlib)
grep -rniE "\b(good|common|value|justice|consensus|ethics|self|import|god|love|compass)\b" \
  ../program-2/series-8/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely. If an on-record attempt file is written, it is a `roots` entry and MUST compile under `lake build` — do not leave it standalone-and-unbuilt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (FRUSTRATED / GLUABLE / SHAPE-DRAWN / PAIRWISE-ONLY / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. FRUSTRATED is the expected close: many selves, each reconciled with each neighbor, share no single good — local coherence does not glue, the whole frustrated as a matter of theorem, the value analog of Series 2.7's global failure and general relativity's before it. GLUABLE, if a global good is forced, contradicts the phase thesis and must be reported honestly, the positioning rewritten — the surprise that this universe guarantees a common good. SHAPE-DRAWN joins the permanent opens. PAIRWISE-ONLY, if the obstruction is only a single edge, is the honest finding that the many-body phenomenon did not materialize; DISCONNECTED, if no good survives, that the universe writes no good at all. None is reached by relabeling; the T1-S1 standard applies with full force.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. The good this series builds is the common good of the universe; the knot is whether local coherence glues into it or is frustrated. Phase B must find the good AND a model-derived frustration on paper before it is built, and PAIRWISE-ONLY and DISCONNECTED are honorable. The Series 2.7 lesson — reconciliations model-derived, not bolted on; the verdict on the world, not on a disconnected counter — is carried first-class. No em dashes in final academic copy.*
