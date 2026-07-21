# Program 2 Series 7 (2.7), Protocol

**The process, self-contained. This protocol is written so that a single Claude Code instance can take Series 2.7 from an empty `formal/` to a computed verdict with no delegation except the two review phases (C and F), which are delegated to a blind subagent by the mechanism in section 5. The series asks one knot: is there a quantity conjugate to the tick — a measure of distinction, energy-and-information — and is it CONSERVED-RELATIVE, MONOTONE-ONLY, or a FREE-LUNCH created by self-reference? It rebuilds no imported machinery; it constructs the MEASURE FRESH on the tick and the recoverability test, and puts the P1 diagonal on trial as a source. This is the fourth series of Phase 2, the physics CAPSTONE, and the HARDEST: its risk is concentrated in WS1, the measure itself, which must be FOUND, not inherited. It is chartered under the Phase-2 costume gate: the knot is DIAGONAL-powered (does self-reference create or relocate the measure), not import-powered — and NOT the mere fact that a distinction is an import. No global conservation is asserted; the global fails, as general relativity foretold.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 2)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "energy," "conservation," "creation," no metaphysics, no general relativity. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (MONOTONE-ONLY, FREE-LUNCH, GLOBAL, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **DISCONNECTED — no non-trivial measure survives — is a genuine outcome, not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built (name the theorem), or **(Relabeled)** the target was not built, the obstruction recorded, and the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING.

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("energy," "conservation," "information," "measure," "creation," "ledger") and check whether the statement still goes through as a bare count / `¬ Recoverable` / invariance fact. What SHOULD survive: WS1's measure strips to "a function on configurations taking two distinct values"; WS2's conservation strips to "the measure is invariant under the reification map, in-sight"; WS3's source strips to "any configuration with a different measure differs by a `¬ Recoverable` distinction (Series 07)"; WS4's crux strips to "the residue map does / does not change the measure, both reachable."

4. **No global conservation asserted; the import quantified, not named.** No proof term asserts a globally conserved measure; conservation is FOR a self, in-sight, changed at the import (Phase-2 self-relative discipline, its capstone). The import that sources the measure stays quantified, never named. "Energy," "conservation," "creation" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "energy," "conservation," "information," "measure," "creation," "self," "import," "God," "choice," or "subjectivity" as content. Headlines mention only the measure (a neutral-named function), the reification map, the recoverability test, the residue, `¬ Recoverable`, the transcribed machinery, and standard Lean/Mathlib. (Neutral Lean names for the concept-bearing objects; the grep guards the content-names.)

Four emphases specific to this series:

6. **The knot is the diagonal-as-source, not import-ness (the Phase-2 costume gate, PROMOTED first-class).** The mere fact that a distinction is an import is Series 07 — a costume. The verdict must rest on whether self-reference (the diagonal, the residue) CREATES or RELOCATES the measure (WS4). A payoff that strips to "a distinction is `¬ Recoverable`," with no create-or-relocate content, is the costume. The reviewer presses hardest on audit (c): does the verdict rest on the diagonal-as-source, or only on import-ness?

7. **No global conservation, and the global's failure is the finding (the phase thesis).** No theorem asserts a globally conserved measure the structure does not force. Conservation is relative-to-the-self, in-sight, changed at the import — the general-relativity shape (local, not global). If GLOBAL is forced, it is reported honestly and the positioning rewritten, never asserted to comfort. Audit (a).

8. **The measure is independently defined, non-trivial, and not rigged (the WS1 watch).** `Q` must be defined WITHOUT reference to its conservation or its rise; its conservation (WS2) and its free-lunch status (WS4) must be PROVED of the independent `Q`, not built in. A `Q` that conserves or rises by construction is the sin. Audit (b), (c).

9. **DISCONNECTED is honorable.** If Phase B's paper de-risking finds no non-trivial measure that survives the tick and the diagonal, the series lands DISCONNECTED — the honest finding that the universe keeps no ledger at all — reported in full, never relabelled into a weaker pseudo-measure.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. **All five plus `spec/README.md` are committed as one batch before any build (Phase B gate), AND only after the measure has been de-risked on paper (the Phase B gate for this series).**
- **`spec/README.md` (design index).** The imported chain, the primitive (the measure, built fresh and de-risked), the discipline (no global conservation, knot on the diagonal-as-source not import-ness, measure non-trivial and not rigged, DISCONNECTED honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/measure-derisking.md` (this series only, before the WS designs).** The paper hunt for `Q`: candidate measures, and for each, the by-hand test against the tick (does it conserve in-sight?) and the diagonal (does the residue change it?). Only a candidate that survives both earns the WS designs. If none survives, this file records the obstruction and the series lands DISCONNECTED.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-6` (the predecessor, already built).** Reaching S5–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S7` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold (`spec/`, `formal/`) created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
**This series' Phase B begins with the measure de-risking, and does NOT proceed to the WS designs until a measure survives.** Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format and house style; **read `program-2/series-1/`** (the tick, the reification map); **read the P1 foundation** (`program-2/formal/P1/Core.lean`, `Reader.lean`: `Recoverable`, `plainOf`, `ws4_recoverable_not_import`, `ws2_residue_free`, the residue — the source test and the free-lunch test object); and `program-1/series-13/` (the mint — how self-reference manufactured imports in Program 1, the prior art for the free-lunch question). Read `program-2/charter-extension.md` §3 (the costume gate). **Then write `spec/measure-derisking.md`**: propose candidate measures `Q` (the latent-and-actual / import-content candidate is the lead), and for each, test BY HAND (a) does a reification-tick conserve it in-sight, and (b) does the residue (the diagonal) change it? Record rejected candidates. Only a `Q` that survives both earns the WS designs; if none does, land DISCONNECTED (record the obstruction, skip to the DISCONNECTED verdict at WS5). If a `Q` survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage against non-triviality, the strip test, the costume gate, and the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S7` module naming and record it. **Gate: commit `spec/measure-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (c): does the knot rest on the diagonal-as-source, or only on import-ness (the costume)? — audit (b): is `Q` independently defined and non-trivial, or rigged? — and audit (a): is any global conservation asserted?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S7` namespace. **Build on Series 2.6**: `import P2S6` and use it and its transitive API (chiefly `P2S1`'s tick and the P1 recoverability/diagonal machinery) — do NOT `import P2S5`/…/`P1` directly (the layered chain; the gate enforces it). Build the measure FRESH, independently of its conservation.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S7`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S7"
srcDir = "../program-2/series-7/formal"
roots = ["P2S7", "P2S7.AxiomCheck"]
```
and append `"P2S7"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-7 "^import (P2S6|P2S7)(\.[A-Za-z0-9_]+)*$"` (the series imports its predecessor S6 and its own `P2S7.*` roots, plus Mathlib; below-S6 is transitive; any other tree is forbidden). Lay out `formal/` as `P2S7.lean` (imports `P2S7.ws1`…`P2S7.ws5`), `P2S7/wsN.lean`, `P2S7/AxiomCheck.lean`, mirroring `program-1/series-13/formal/Series13/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (c) the knot rests on the diagonal-as-source not import-ness (the costume gate), (b) `Q` is independently defined and non-trivial (not rigged), and (a) no global conservation is asserted.** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; a global conservation is asserted the structure does not force (audit a, the phase sin); the knot rests on import-ness rather than the diagonal-as-source (the costume gate, audit c); `Q` conserves or rises by construction (rigged, audit b); the fork is a fiat (FREE-LUNCH or CONSERVED excluded by construction); a name is a proof term; a prior SERIOUS finding RECURS via a target-avoiding closure; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, an import-ness fact dressed as a create-or-relocate interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the tenets, the general-relativity prose, `charter-extension.md`'s prose, `summary*.md`, and any file naming "energy," "conservation," "creation." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension.md`, `summary*.md`, `measure-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names-not-terms grep; confirm the audit clauses, ESPECIALLY (c) the knot rests on the diagonal-as-source not import-ness, (b) `Q` is independently defined and non-trivial, and (a) no global conservation is asserted; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction (the subagent shares the filesystem). If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S7 P2S7.AxiomCheck   # compiles (P2S6/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-7/formal            # sorry-free (prose excepted)
lake build P2S7.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                        # closure (P2S7 + P2S6 + Mathlib)
grep -rniE "\b(energy|conservation|information|measure|creation|self|import|god|choice|subjectivity)\b" \
  ../program-2/series-7/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (CONSERVED-RELATIVE / MONOTONE-ONLY / FREE-LUNCH / GLOBAL / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. CONSERVED-RELATIVE is the expected close: the universe keeps a private ledger each self balances within its own sight, changed only at the import, and no global books — general relativity's local-but-not-global conservation, in a relational key. FREE-LUNCH, if the diagonal is a genuine source, is the strange and beautiful finding that this universe creates distinction from within and runs on generosity, not conservation — "to relate is to create" as a law — reported in its direction. GLOBAL, if forced, contradicts the phase thesis and must be reported honestly, the positioning rewritten. DISCONNECTED, if no measure survives, is the honest finding that the universe keeps no ledger at all. None is reached by relabeling.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point; the phases are their scaffolding. The measure this series builds is the ledger of the universe; the knot is whether it conserves, and whether self-reference is generosity. Phase B must find the measure on paper before it is built, and DISCONNECTED is honorable. No em dashes in final academic copy.*
