# Relational Existentialism, Program 2, Protocol

**The process, at the PROGRAM level. Program 2 is built series by series, and each series runs its own self-contained A→G protocol (`program-2/series-N/protocol.md`). This document is one level up: it codifies the TWO-TIER workflow that produces those series and stitches them into a program. Tier 1 is a PERSISTENT design-and-review conversation (this one): it authors each series' charter / status / protocol, hands the series to an executor, reviews the landing with an independent skeptical read, and writes a Charter Extension when the review finds the bar was set too low. Tier 2 is a FRESH executor instance per series: a single Claude Code conversation that takes the chartered protocol from an empty `formal/` to a computed verdict, with no delegation except its own two blind review phases. The program charter (`charter.md`) is the fixed program-level bar; `charter-status.md` is the program's living ledger; this protocol is the runbook that connects the two tiers.**

*Read the program charter (`charter.md`) once for the one question and the series decomposition, then this protocol for how a series is born, run, reviewed, and extended. The program charter is the fixed bar. `charter-status.md` is the living ledger. This protocol is the process. Do not edit either charter to record progress; edit a charter only to fix a design error, and edit the program charter's series decomposition only when a series charter genuinely revises it (the charter §2 grants that latitude).*

---

## 0. Core principles (the honesty invariants, at program scope)

The series protocols carry five honesty invariants (blind means blind; never relabel a shortfall; strip the word keep the theorem; the import quantified never named; names are names not terms) plus a §0.2a recurrence guard. Those govern one series. Six more govern the PROGRAM, and Tier 1 is their custodian. Violating any is a SERIOUS program-level finding.

1. **The bar only ever rises.** A Charter Extension (§3) may STRENGTHEN a series target, promote a disclosed-cosmetic finding to REAL, or add an obligation. It may NEVER weaken a target, retire an audit clause, or lower a verdict threshold. An "extension" that relaxes the bar is the program-level relabel, the one unforgivable move at this scope. Honest under the series protocol §0.2a: a target that cannot be met closes Relabeled, with the obstruction recorded — it is never quietly lowered.

2. **The review that writes an extension is independent, not the executor's.** Tier 1 reviews each landing itself, with a fresh skeptical read seeded by the executor's report and the built code, NOT by trust in the executor's own review verdict. The executor's blind C/F reviews guard the series; Tier 1's read guards the program, and it presses hardest exactly where a blind reviewer under-graded (an inert reification, a bare conjunction dressed as an interaction, a non-directional arrow, a generic stream — the actual Program 2 catches so far). A landing is not accepted because the executor says it passed; it is accepted because Tier 1 re-derived that it passed.

3. **The layered import chain is sound by construction, and enforced.** `P1 → S0 → S1 → S2 → S3`, each series importing ONLY the one immediately before it (plus Mathlib), reaching the rest transitively. A layer enters the build exactly once and is built and axiom-checked before the next imports it. Tier 1 owns the invariant that nothing downstream reaches behind its predecessor to raw machinery the predecessor was built to correct (nothing reaches behind S0 to P1's κ-bounded carrier). Each series' `scripts/gate.sh` line encodes the chain; the gate is green before a series is accepted.

4. **The excluded machinery stays excluded, program-wide.** Program 1's PR1-S1 trap (the convergence tautology of an unconstrained `Compass`/`Converges` type) and PR1-S2 trap (the reader quantified out to `Many`) were transcribed into the P1 foundation as DELIBERATE EXCLUSIONS with a guardrail banner. No series may re-import or reconstruct them. Tier 1 checks every new series design against both traps before the executor builds, and the blind F review checks the code against them; the two catches must agree.

5. **The permanent opens are never filled, by any series.** The content of the compass, the direction of convergence, the differentiating act, and the classification of the out-of-image imports are carried untouched across every series. A series may draw one sharper (Series 2.3 draws the direction of convergence exactly and fills it never); no series adds to them or closes one. Tier 1 audits the roster of opens after every landing and confirms the count is unchanged.

6. **The program verdict is composed, not asserted.** The program's standing (CONSTRUCTED-AND-WALLED / CONSTRUCTED-FLAT / COLLAPSED / DISCONNECTED, charter §5) is READ OFF the series verdicts as they land, never declared ahead of them. A series verdict is itself computed (a discriminating `Bool^n → Outcome`, never hand-set). Tier 1 records each series verdict in the ledger as it computes and lets the program verdict accumulate; it does not decide the program's outcome and then grade series to fit it.

---

## 1. The two tiers

### Tier 1 — the persistent design-and-review conversation (this one)

One long-lived Claude Code conversation holds the whole program. It does five things, and only these:

- **Authors** each series' three documents before the series is handed off: `charter.md` (the fixed series bar, §2 of this protocol), `charter-status.md` (the series ledger, initialized), `protocol.md` (the self-contained A→G runbook the executor follows).
- **Hands off** the series to a fresh executor (Tier 2) by pointing it at the series folder and its protocol.
- **Reviews** each landing with an independent skeptical read (§4): pulls the executor's branch, reads the built code, and re-derives whether the verdict is earned — pressing where a blind reviewer would under-grade.
- **Extends** the charter (§3) when the review finds the bar was set too low, then hands the series BACK to an executor for another code/review/repair pass.
- **Composes** the landed series into the program: updates `charter-status.md` (the program ledger), carries forward-notes between series (the PX-N notes), and lets the program verdict accumulate.

Tier 1 never writes a series' `formal/` code and never runs the A→G phases. Its product is documents and judgments, not proofs.

### Tier 2 — the series executor instance (fresh per series)

A separate Claude Code conversation, spawned once per series (or once per extension pass). It runs the series' own `protocol.md` start to finish: phases A→G, delegating only its two blind review phases (C and F) to a blind subagent. It builds `formal/`, computes the WS5 verdict, and reports back to Tier 1 with the branch, the verdict, and the findings ledger. It does not design the next series, does not touch other series, and does not judge its own landing at the program level — that is Tier 1's job. Each executor is BLIND to the program's motivating prose in exactly the way the series blind reviewers are; its charter states the mathematical targets, not the metaphysics.

**Why two tiers.** The persistent conversation accumulates the program's judgment — the traps, the forward-notes, the sense of where the next wall stands — which a fresh executor cannot hold. The fresh executor gets a clean, self-contained runbook and a fixed bar, so its work cannot drift on stale context and its verdict is a function of the code, not of the conversation that designed it. The independence is the point: the tier that sets the bar is not the tier that clears it, and the tier that clears it is not the tier that certifies the clearing.

---

## 2. The series lifecycle (how Tier 1 authors and closes a series)

Each series moves through these program-level steps. The middle of it (the executor's A→G) is the series protocol; the ends are Tier 1's.

### Step 1 — Author (Tier 1)
Write the series' `charter.md`, `charter-status.md`, `protocol.md`, modelled on the prior series' triad and on `program-1/series-13/`. The charter states the series' one question, its WS1–WS5 targets, its pre-registered outcomes, and its false escapes (inheriting the program's §4 escapes, sharpened for this series). The protocol is self-contained: an executor with no other context can run it. Fix the namespace (`P2SN`), the gate line, and the lakefile registration in the protocol's Phase E. Carry any forward-note from the previous series (a PX-N note in the previous series' status) into the new charter as a Phase B consideration. Precondition: the predecessor series must have LANDED (its verdict computed and accepted) before this series' Phase B begins — the import chain requires a built predecessor.

### Step 2 — Hand off (Tier 1 → Tier 2)
Point a fresh executor at the series folder and its protocol. The executor runs A→G. Tier 1 waits; it does not run the phases.

### Step 3 — Land (Tier 2 → Tier 1)
The executor reports back: the branch, the computed WS5 verdict, the findings ledger, the build/axiom/gate/grep results. The series is now a candidate landing.

### Step 4 — Review (Tier 1, §4)
Tier 1 pulls the branch and reads the built code with a fresh skeptical eye, independent of the executor's own review. It confirms: the verdict is computed and discriminating; the payoffs survive the strip test; the reader is named not quantified out; the import is quantified not named; the audit clauses hold on the code; the layered gate is green; the excluded machinery was not re-imported. It presses hardest where a blind reviewer under-grades.

### Step 5 — Extend or accept (Tier 1)
- If the review finds the bar was set too low (a payoff that strips to a bare fact, an inert argument, a disclosed-cosmetic finding that should have been REAL), Tier 1 writes a **Charter Extension** (§3), hands the series back to an executor for a code/review/repair pass, and returns to Step 3.
- If the review finds the verdict earned, Tier 1 **accepts** the landing: records the series verdict in the program ledger, writes any forward-note for the next series, and updates the program snapshot.

### Step 6 — Compose (Tier 1)
The accepted series is now part of the program. Its verdict accumulates into the program verdict (charter §5). Its `formal/` is a built layer the next series imports. Its permanent-opens accounting is folded into the program's. Return to Step 1 for the next series.

---

## 3. The Charter Extension mechanism

A Charter Extension is Tier 1's instrument for raising the bar on a series AFTER its charter was fixed but the review found it too generous. It lives at `program-2/series-N/charter-extension.md`.

- **It only ever raises the bar.** It strengthens a target (Series 2.0's WS1 raised from a bare reification to `ws1_first_other`; Series 2.1's WS3 raised to a load-bearing implication), promotes a disclosed-cosmetic finding to REAL, or adds an obligation. It never weakens one. (Program-level invariant §0.1.)
- **It is honest under the series protocol §0.2a.** A finding re-graded from cosmetic to REAL by an extension re-enters the recurrence guard: it closes Fixed (the strengthened target built, name the theorem) or Relabeled (the obstruction recorded, the payoff demoted to a pre-registered outcome). A target-avoiding closure is re-graded SERIOUS and marked RECURRING.
- **It triggers a re-run.** After an extension is written, the series goes back to an executor for another E/F/G pass (code / blind review / repair). The extension's findings are tracked in the series ledger with stable IDs (e.g. `EXT-F1`) alongside the original C/F findings.
- **It is recorded at both scopes.** The series' `charter-status.md` logs the extension and its findings' closures; the program `charter-status.md` logs that the extension happened, one line per series (§4 of the program ledger).

The extensions written so far (Series 2.0 Ext 1, Series 2.1 Ext 1) are the model: each caught an under-graded weakness (inert reification and bare-conjunction asymmetry in S0; non-directional arrow, generic stream, bare residue in S1), strengthened the target, and the executor re-ran to Fixed.

---

## 4. The independent landing review (how Tier 1 reviews, Step 4)

This is Tier 1's own review, distinct from the executor's blind C/F. It is NOT blind — Tier 1 holds the whole program's context, and that context is exactly what lets it catch what a blind reviewer misses. The read:

1. **Pull and build.** Fetch the executor's branch, read the `formal/` sources for the series, confirm the build is sorry-free, axiom-clean (standard three), gate-green, and grep-clean, independently of the executor's report.
2. **Re-derive the verdict.** Confirm the WS5 verdict is a discriminating function reaching more than one value with the pre-registered alternatives reachable, and that it is computed from the built theorems, not hand-set.
3. **Run the strip test by hand.** For each payoff, delete the interpretive term and check whether the statement survives as a bare `Recoverable` / bisimulation / rank / order fact. A payoff that strips to a bare fact is the catch — it means the series' new content is doing no work (the Series 11 Bookkeeping danger, K1). This is where Tier 1 has caught the most: inert reification, bare conjunctions, generic streams.
4. **Check the reader and the import.** The reader is a named `FiniteAttention` load-bearing in the payoff, never quantified out to `Many` (PR1-S2). The import is quantified over, never named as a term (charter §4.e). Both grepped and read.
5. **Check the traps and the chain.** The excluded PR1-S1/PR1-S2 machinery was not re-imported or reconstructed; the gate line encodes the correct predecessor; nothing reaches behind the predecessor.
6. **Account the permanent opens.** The roster of four opens is unchanged; the series added none and closed none.

If steps 3–4 find a payoff that under-delivers, Tier 1 writes the Charter Extension (§3). Otherwise it accepts.

---

## 5. How the series compose into the program

- **The import chain is the spine.** Each accepted series is a built, axiom-checked Lean layer the next imports. The program's `formal/` is the union of `P1`, `P2S0`, `P2S1`, `P2S2`, `P2S3`, …, registered in `lake/lakefile.toml`'s `defaultTargets`, each with its own `[[lean_lib]]` block and gate line. The whole program builds green together.
- **The forward-notes carry the judgment.** When a landing reveals something the next series should weigh, Tier 1 writes it as a PX-N note in the landing's status (S2's PX-1: the twoness is rank-based, S3 may lift it rank→import) and folds it into the next charter as a Phase B consideration. This is how the persistent conversation's accumulated sense of the terrain reaches the fresh executor.
- **The program verdict accumulates.** Each series verdict (GROUND-ESTABLISHED, TWO-ZONE, TWO-FACING, …) is a rung. The program verdict (charter §5) is read off the sequence as it lands: the constructions holding for every stream push toward CONSTRUCTED-AND-WALLED; a series that cannot hold multiplicity without a second import would surface COLLAPSED. Tier 1 records the rungs and lets the program standing follow; it never asserts the standing ahead of the rungs.
- **The permanent opens bound the whole.** No series fills one. The program's ambition is the wall, drawn exactly, not the filling — at series scope and at program scope alike.

---

## 6. Program-level exit

Program 2 has no single terminal build the way a series does; it exits when the chartered series (2.0–2.3, plus any later population stretch actually reached) have all landed and been accepted, the program verdict is read off their sequence, and the program summaries are written. The verdict is the residue of the composed series, not a premise. CONSTRUCTED-AND-WALLED is the expected close: the dynamic multi-perspective universe is built for every stream, and the new wall stands exactly where the relating stops being able to see. COLLAPSED, if a series cannot hold its ambition without a second import, is honorable and reported in full, in whichever direction, with the positioning rewritten rather than defended — the true heir to Series 07, never reached by relabeling.

---

*This protocol is self-contained at the program level: Tier 1 (this persistent conversation) authors, reviews, extends, and composes; Tier 2 (a fresh executor per series) runs the chartered A→G. The honesty invariants (§0) are the whole point; the two-tier structure is their scaffolding — the tier that sets the bar does not clear it, and the tier that clears it does not certify the clearing. No em dashes in final academic copy.*
