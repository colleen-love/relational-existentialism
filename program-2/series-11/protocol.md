# Program 2 Series 11 (2.11), Protocol

**The process, self-contained. This protocol takes Series 2.11 from an empty `formal/` to a computed verdict with no delegation except the two blind review phases (C and F, section 5). The series asks one recovery question, the decisive one: can distinction CANCEL — is there a signed amplitude, read off Series 2.8's holonomy, that produces genuine DESTRUCTIVE INTERFERENCE (a combined weight strictly below its parts)? It rebuilds no imported machinery; it constructs the AMPLITUDE and the WEIGHT FRESH, read off Series 2.8's built `incr`/`hol` (imported), and asks whether the signed structure subtracts. This is execution tier 2 of Phase 3 (after the tier-1 pair 2.9/2.10 cleared), the make-or-break for the recovery test. It is chartered under Phase 3's no-smuggling gate, at its sharpest: the amplitude must be EARNED from the built holonomy, never a bolted-on complex number; genuine interference is a combined weight STRICTLY below the parts, not additive bookkeeping; and the scope is disclosed — the amplitude is a REAL sign (`±1`), the complex `U(1)` phase a forward-note, never overclaimed. ADDITIVE-ONLY is a pre-registered honorable NOT-RECOVERED.**

*Read the charter (`charter.md`) once for the question and the targets, then run the phases in order. The charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the runbook. Do not edit the charter to record progress; edit it only to fix a design error, and an edit upstream of built work reopens the affected workstreams.*

---

## 0. Core principles (the honesty invariants, transcribed and extended for Phase 3)

Nine things carry the honesty. Violating any is a SERIOUS finding.

1. **Blind means blind.** A review phase (C, F) is seeded with the design contracts, the built code where it exists, and the charter's success criteria and audit checks, but NEVER the charter's motivating prose. No "phase," "amplitude," "interference," "quantum," no metaphysics, no double-slit. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Blindness is enforced by instruction (section 5).

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build or design falls short, the honest outcome is a pre-registered alternative (ADDITIVE-ONLY, SHAPE-DRAWN, DISCONNECTED, PARTIAL) with the obstruction made precise, never a quiet redefinition of the target. **ADDITIVE-ONLY — no combined weight ever falls below its parts, the world classical — is a genuine outcome and a specification for the next iteration (add a phase), not a failure to hide.**

**2a. The recurrence guard (Phase D and Phase G).** A SERIOUS finding closes in exactly ONE of two ways, named in `charter-status.md`: **(Fixed)** the originally specified target was built, or **(Relabeled)** the target was not built, the obstruction recorded, the payoff demoted to a pre-registered outcome. A different, weaker theorem adjacent to the target is NEITHER, and is prohibited; a finding addressed that way is re-graded SERIOUS and marked RECURRING. (Series 2.7's T1-S1 — a look-alike passed off as the genuine article — and Series 2.10's discipline — the higher bar, no smuggle — are the standards this series inherits.)

3. **Strip the word, keep the theorem.** For every payoff, delete the structural term ("phase," "amplitude," "interference," "quantum") and check whether the statement still goes through as a bare sign / squared-sum inequality on the built holonomy. WS1's amplitude strips to "a `±1`-valued function of `hol`, taking both values"; WS2's cancellation to "two opposite signs sum to zero"; WS3's interference to "`(a+b)² < a² + b²` for the signed `a,b`" (the strict inequality is the whole content); WS4's fork to "odd holonomy ⇒ weight below the parts; even holonomy ⇒ weight the sum."

4. **The recovery is earned, not smuggled (the Phase-3 no-smuggling gate, sharpest here).** No proof term BOLTS ON a complex number, a phase, or an amplitude not read off the model; the amplitude is a function of the built `incr`/`hol` (definitional), its signedness proved. "Phase," "amplitude," "interference" are prose.

5. **Names are names, not terms.** The reviewer greps `formal/` and confirms no proof term, definition, or discharged obligation is named "phase," "amplitude," "interference," "quantum," "superposition," "wave," "complex," "self," "import," "God," or "choice" as content. Headlines mention only the sign (a neutral-named `±1`/ℤ function of `hol`), the weight (a squared modulus), the imported `incr`/`hol`, the transcribed machinery, and standard Lean/Mathlib.

Four emphases specific to this series:

6. **The phase is EARNED, no complex number smuggled (the no-smuggling gate, PROMOTED first-class, sharpest in the program).** The amplitude must be a function of the built holonomy, not a bolted-on phase. The reviewer presses hardest on audit (a): is the amplitude read off `incr`/`hol`, or is a complex number added to produce cancellation?

7. **Interference is DESTRUCTIVE, not additive (the costume gate).** Genuine interference is a combined weight STRICTLY below the sum of the parts (`|a+b|² < |a|²+|b|²`) — an inequality no classical probability satisfies. The signed sum being zero is necessary but not sufficient; the WEIGHT must fall below the parts. A "cancellation" that only ever adds is additive bookkeeping. Audit (c).

8. **The scope is disclosed, the complex phase not overclaimed.** The amplitude is a REAL sign (`±1`); no theorem claims the full complex `U(1)` phase or that quantum theory is recovered whole. Real (signed) interference is the honest claim; the complex phase and the Born rule (Series 2.12) are the disclosed gap. Audit (d).

9. **ADDITIVE-ONLY is honorable.** If no combined weight ever falls below its parts, the series lands ADDITIVE-ONLY — the honest report that distinction only accumulates, the world classical — reported in full, never relabelled into a pseudo-interference.

---

## 1. The documents

- **`charter.md` (stable).** The question and the targets. Edited only to fix a design error.
- **`spec/wsNN-design.md`, WS1–WS5 (stable once committed).** Per-workstream designs: candidates, a paper triage table, the winning construction to typed signatures, outcome classes, strip-test annotation. All five plus `spec/README.md` are committed as one batch before any build (Phase B gate).
- **`spec/README.md` (design index).** The imported object (`P2S8`'s `incr`/`hol`), the primitive (the amplitude and weight, built fresh and earned), the discipline (phase earned not smuggled, interference destructive not additive, scope disclosed, ADDITIVE-ONLY honorable), the cross-workstream triage, the outcomes, the names-in-prose rule.
- **`spec/phase-derisking.md` (this series, before the WS designs).** The paper hunt: the candidate amplitude read off `hol` (the parity sign `(−1)^…` is the lead), and the by-hand test that (a) it is genuinely signed (takes both values on `P2S8`'s carriers), (b) on the frustrated cycle (`hol = 3`, odd) two paths' amplitudes give a combined weight STRICTLY below the parts (`0 < 2`), and (c) on the gluable case (`hol = 0`, even) the weight is the ordinary sum. Only an amplitude that survives — signed, earned, genuinely destructive on one carrier and additive on another — earns the WS designs; if the cancellation is only additive, land ADDITIVE-ONLY.
- **`spec/blind-seed-C.md` / `spec/blind-seed-F.md` (generated at review time).** Section 4.
- **`program-2/series-8` (the imported object, already built).** Reaching S7–S0/P1. Environment prepared on container creation (Lean `v4.15.0`, Mathlib cached).
- **`formal/` (built at Phase E).** The series' Lean sources, one module per workstream plus an `AxiomCheck`, in the `P2S11` namespace.
- **`charter-status.md` (living ledger).** Updated at the end of every phase.

---

## 2. The phases (run in order; C/D and F/G loop on SERIOUS findings)

### Phase A — Charter [executor, COMPLETE]
Charter written and committed, `charter-status.md` initialized. Scaffold created at the start of Phase B. Nothing further.

### Phase B — Design [executor]
Read the canonical templates first: `program-1/series-13/spec/*` and `formal/Series13/*` for format and house style; **read `program-2/series-8/`** (the built `incr`/`hol`, the frustrated / gluable carriers — the signed structure this series lifts to an amplitude); **read `program-2/series-10/`** (the no-smuggling discipline and the higher-bar / look-alike guard, freshly exercised); **read `program-2/series-2/`** (the two-facing reader, the oriented seed of a phase). Read `program-2/charter-extension-2.md` §3 (the no-smuggling gate) and §4 (2.11). **Then write `spec/phase-derisking.md`** (the paper hunt above): a signed amplitude read off `hol`, genuinely destructive (weight below the parts) on the frustrated cycle and additive on the gluable case, earned, no smuggled complex number. Only such an amplitude earns the WS designs; if the cancellation is only additive, land ADDITIVE-ONLY (record the obstruction, skip to that verdict at WS5). If it survives: for each of WS1–WS5, write `spec/wsNN-design.md` (candidates, paper triage, the strip test, the no-smuggling gate, the destructive-vs-additive bar, the scope disclosure, the audit clauses; the winning construction to typed signatures; the outcome classes; the strip-test annotation). Write `spec/README.md`. Fix the `P2S11` module naming and record it. **Gate: commit `spec/phase-derisking.md` plus all six design files as one batch before any `formal/` file exists.**

### Phase C — Design review [DELEGATED, BLIND]
Generate `spec/blind-seed-C.md` (section 4). Spawn a blind reviewer (section 5) pointed at the blind seed and the `spec/wsNN-design.md` signatures ONLY. Collect graded findings, append to the ledger. Do not fix; only record. **The reviewer presses hardest on audit (a): is the amplitude EARNED from the built `incr`/`hol` or is a complex number bolted on? — audit (c): is the interference genuinely destructive (a combined weight STRICTLY below the parts) or additive bookkeeping? — and audit (d): is the scope disclosed (a real sign, not the complex phase overclaimed)?**

### Phase D — Design repair [executor]
Address every SERIOUS finding by the 2a binary. Address REAL if cheap; note COSMETIC. Update `spec/` and the ledger. Commit.
**Loop:** return to Phase C with a fresh seed whenever a SERIOUS finding was closed by editing a design. Continue until a Phase C pass returns zero SERIOUS.

### Phase E — Code [executor]
Build `formal/` to the Phase B (post-repair) signatures, one module per workstream plus `AxiomCheck`, in the `P2S11` namespace. **Build on Series 2.8**: `import P2S8` and use its built `incr`/`hol` and carriers (and its transitive API) — do NOT `import P2S9`/`P2S10` (not reused) or `P2S7`/…/`P1` directly (the layered chain; the gate enforces it). Build the amplitude FRESH, earned from the built holonomy.

**Register the series (do this at Phase E, never earlier).** Namespace `P2S11`. In `lake/lakefile.toml`, add:
```
[[lean_lib]]
name = "P2S11"
srcDir = "../program-2/series-11/formal"
roots = ["P2S11", "P2S11.AxiomCheck"]
```
and append `"P2S11"` to `defaultTargets`. In `scripts/gate.sh`, add: `check program-2/series-11 "^import (P2S8|P2S11)(\.[A-Za-z0-9_]+)*$"`. Lay out `formal/` as `P2S11.lean` (imports `P2S11.ws1`…`P2S11.ws5`), `P2S11/wsN.lean`, `P2S11/AxiomCheck.lean`, mirroring `program-2/series-8/formal/P2S8/`.

The build must be sorry-free, axiom-clean (standard three, via `AxiomCheck`), gate-green, and compiling. Run the section 6 checks. Compute the WS5 verdict from the built theorems (never hand-set). Update `charter-status.md`. Commit.

### Phase F — Code review [DELEGATED, BLIND]
Generate `spec/blind-seed-F.md`. Spawn a blind reviewer (section 5) pointed at the blind seed AND the `formal/` sources, told to judge whether the code proves the claimed signatures, run the strip test and names-not-terms grep, and confirm the audit clauses — **especially (a) the amplitude earned from the built holonomy not smuggled, (c) the interference destructive (weight strictly below the parts) not additive, and (d) the scope disclosed (a real sign, complex phase not overclaimed).** Collect graded findings; append to the ledger. Do not fix.

### Phase G — Code repair [executor]
Address every SERIOUS finding by the 2a binary. Update `formal/` and/or the ledger; re-run section 6 checks; recompute the verdict if a payoff changed. Commit.
**Loop:** return to Phase F with a fresh seed whenever a SERIOUS finding was closed by editing code. Continue until a Phase F pass returns zero SERIOUS.

### Exit
When a Phase F pass returns zero SERIOUS and the build is sorry-free, axiom-clean, and gate-green, the series is done. The WS5 verdict is the computed outcome. Write `summary.md` / `summary-technical.md`. Finalize `charter-status.md`. Commit and push.

---

## 3. The grading rubric (used by the reviewer in C and F)

- **SERIOUS:** the verdict rests on it; the phase is SMUGGLED (a bolted-on complex number, not earned from the built holonomy — audit a, the phase sin); the interference is ADDITIVE, not destructive (no combined weight below the parts — the costume, audit c); the full complex phase is OVERCLAIMED (audit d); the amplitude is trivial (unsigned); the fork is a fiat; a name is a proof term; a prior SERIOUS finding RECURS; or an undisclosed narrowing between charter and build.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, an additive fact dressed as destructive interference).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

---

## 4. The blind seed (run before each C and each F)

Write `spec/blind-seed-<phase>.md` containing ONLY: (1) the theorem signatures and definitions under review, no motivating comment; (2) the charter's success criteria restated WITHOUT the motivating clauses; (3) the audit checks (a–e) as mechanical instructions; (4) the strip-test instruction and the names-not-terms forbidden list; (5) the grading rubric. EXCLUDE always: `charter.md`'s manifesto and sections 0/1/8, the positioning, the double-slit / quantum prose, `charter-extension-2.md`'s prose, `summary*.md`, `phase-derisking.md`, and any file naming "phase," "amplitude," "interference," "quantum." Copy only signatures and triage tables from design files, never their narrative.

---

## 5. The delegation mechanism (how C and F are run)

Spawn one reviewer with the Agent tool, `subagent_type: general-purpose`, `run_in_background: false` (the executor waits). The prompt is BLIND and must: name exactly the files the reviewer may read (`spec/blind-seed-<phase>.md` and, for Phase F, the `formal/` sources), and state explicitly **do not read `charter.md`, `charter-status.md`, `charter-extension-2.md`, `summary*.md`, `phase-derisking.md`, or any file with motivating prose; judge the code only against the contracts in the blind seed**; give the reviewer its task (for each signature, is the design coherent and non-vacuous (C) or does the code prove it (F); run the strip test; run the names grep; confirm the audit clauses, ESPECIALLY (a) the amplitude earned not smuggled, (c) the interference destructive not additive, and (d) the scope disclosed; grade each finding); and require a structured list of findings with stable IDs (`Cn-Sm`, `Fn-Sm`), each with grade, exact location, and defect. Blindness is enforced by instruction. If the reviewer reports reading a forbidden file, discard the pass and re-run. The executor never delegates B, D, E, or G.

---

## 6. The mechanical checks (Phase E and after each Phase G)

```
cd lake && lake build P2S11 P2S11.AxiomCheck   # compiles (P2S8/… + Mathlib cached)
grep -rn "sorry" ../program-2/series-11/formal            # sorry-free (prose excepted)
lake build P2S11.AxiomCheck                                # axiom record; standard three only
../scripts/gate.sh                                         # closure (P2S11 + P2S8 + Mathlib)
grep -rniE "\b(phase|amplitude|interference|quantum|superposition|wave|complex|self|import|god|choice)\b" \
  ../program-2/series-11/formal   # names-not-terms: hits must be docstring prose only
```
Record each result in `charter-status.md`. A non-clean grep or a non-standard axiom is a Phase E defect the executor fixes before Phase F. (The concept-words appear in this series' subject; the carrier definitions use neutral Lean names, and the grep guards that no proof term or headline is named for the interpretive content. Docstring prose may use the words freely; the Lean `import` keyword is exempt.)

## 7. Exit criteria and the verdict

The series exits when: (1) a Phase F pass returned zero SERIOUS; (2) the build is sorry-free, axiom-clean, gate-green; (3) the names grep is clean (prose only); (4) the WS5 verdict computes an outcome from the built theorems (INTERFERING / ADDITIVE-ONLY / SHAPE-DRAWN / DISCONNECTED / PARTIAL, obstruction precise if not the first); (5) every SERIOUS finding is closed by the 2a binary. The verdict is the residue of the process, not its premise. INTERFERING is the hoped-for recovery: the signed holonomy Series 2.8 built is a genuine phase, distinction can SUBTRACT, and the door to quantum theory is open — honestly scoped as real (signed) interference, the complex phase and the Born rule the disclosed gap. ADDITIVE-ONLY, if no combined weight ever falls below its parts, is the honest NOT-RECOVERED: distinction only accumulates, the world classical, the specification for the next iteration (add a phase). SHAPE-DRAWN joins the standing opens. None is reached by relabeling; the T1-S1 / Series-2.10 standard applies with full force.

---

*This protocol is self-contained: one executor runs A, B, D, E, G and delegates only C and F to a blind subagent. The honesty invariants (section 0) are the whole point. The phase this series tests is the decisive question of the recovery test — whether distinction can cancel into genuine interference. Phase B must find a signed, earned, genuinely destructive amplitude on paper before it is built, and ADDITIVE-ONLY is honorable. The amplitude is a real sign, the complex phase a disclosed forward-note; no complex number is smuggled. Reuses Series 2.8's holonomy; imports `P2S8` only. No em dashes in final academic copy.*
