# Program 3 protocol

How Program 3 runs. Two loops: a program loop with four steps, and inside its second step, a series loop with five phases. One persistent conversation (the program seat) runs everything except a series' design and code, which go to a fresh executor per series.

This protocol replaces Program 2's two-tier document set. There are no per-series status or protocol files. Each series has one document, its outline; everything else a series produces is its `formal/` code and an entry in the program status.

## House style

Calm prose. Sentence case. Bold is reserved for verdicts and the rare load-bearing term, used at most a few times per document. No all-caps emphasis. Short sections, short paragraphs. A reader should be able to skim any document top to bottom without fighting it. Docstrings in code follow the same rule: say what the theorem states, plainly; interpretation is welcome but must never exceed the statement.

## The program loop

**1. Charter design (or extension).** The program seat writes or revises `charter.md`: the question, the series plan, the disciplines, the pre-registered outcomes. The charter is edited only to fix a design error or to extend the program; never to record progress. Progress lives in `status.md`.

**2. Series iteration.** For each series in the charter's plan, run the series loop below. A series does not begin until its predecessor has landed and been accepted. The charter's evaluation gate (after 3.2) interrupts iteration for a program review before further series are chartered.

**3. Program review.** An independent adversarial read of everything landed so far, in the style of Program Review 2-1: rebuild from scratch, read every statement against every claim, grade findings (serious / real / cosmetic), and publish the review under `program-3/spec/`. The review runs at the gate and again at the end of the arc, and can be requested at any time.

**4. Program repair.** Each serious finding closes one of two ways: fixed, with the strengthened target built and the theorem named; or relabeled, with the obstruction recorded (as a theorem where one is stateable) and the claim re-scoped. Repairs land in a review-repairs module and a closure ledger, the `PR2R1` pattern. A target-avoiding closure re-enters review as a new serious finding.

## The series loop

**1. Outline.** Written by the program seat: `program-3/series-N/outline.md`. It contains what the old charter and protocol carried, in one readable document: the series' one question, the mathematical targets with their intended theorem names, the pre-registered outcomes including the failure modes, the reuse list (each item with its required bridge theorem), the witness plan (how the carrier satisfies the non-degeneracy discipline), and the scratch de-risk: a short check, on paper or in a throwaway file, that the central object can exist before anyone is asked to build it. If the de-risk fails, the outline is revised or the series is cancelled; nothing is handed off.

**2. Design.** A fresh executor conversation, running on Opus, receives the outline and nothing else of the program's motivating prose. It produces the formal design: the definitions, the statement of every target theorem, and the verdict function with its tying theorem stated. Design is complete when every target can be stated in Lean and type-checks against stubs.

**3. Code.** The same executor builds `formal/`: proves the targets, computes the verdict through tied flags, runs the build, the axiom check, and the gate. The executor's product is the branch and a short landing note (verdict, theorem list, anything that deviated from the outline and why). The executor's job ends here.

**4. Series review.** Back in the program seat. An independent skeptical read of the landed code against the outline: rebuild, check the disciplines (non-degenerate carrier, derived quantities, tied verdict, bridges, no vacuous audits, prose matches Lean), run the strip test on each headline, and press hardest wherever the verdict is the desired one. Where the reviewer's prior runs in the verdict's favor, spawn one blind reader with the outline's targets and the code only. The review ends in one of three ways: accepted, with the verdict and any findings recorded in `status.md`; sent to repair, with graded findings; or relabeled, when the target cannot be met, with the obstruction recorded and the pre-registered alternative outcome taken. Acceptance is recorded in the program status, and the next series may begin.

**5. Series repair.** Runs when the review sends findings back. Each serious finding closes fixed (the strengthened target built, the theorem named) or relabeled (the obstruction recorded, the pre-registered alternative taken); real findings close on the ordinary schedule; cosmetic ones opportunistically. Repairs go to an executor when they touch design or proofs, and stay in the program seat when they are mechanical. After the repair pass the series returns to review. A repair that avoids its target re-enters review as a new serious finding; the loop ends only in acceptance or relabeling.

## Records

- `program-3/charter.md` — the fixed bar. Edited only for design errors or extensions.
- `program-3/status.md` — the living ledger. Every landing, review, finding, and repair gets its entry here, dated, in the order it happened. This file is the program's memory; nothing else needs to be.
- `program-3/series-N/outline.md` — one per series. Frozen at handoff except to fix a design error, and any such edit is noted in the status.
- `program-3/series-N/formal/` — the code.
- `program-3/spec/` — program reviews, their closure ledgers, and any scratch de-risk worth keeping.

## Build

Program 3 series register in `lake/lakefile.toml` and `scripts/gate.sh` like Program 2's did: one library per series, an axiom-check root per library, a gate line naming exactly what the series may import. Reuse of Program 1 or 2 layers is by import plus bridge theorem, per the charter's disciplines.
