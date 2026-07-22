# Program 3 protocol

How Program 3 runs. Two loops: a program loop with four steps, and inside its second step, a series loop. One persistent conversation (the program seat) runs everything, including design and code; the deep skeptical review is batched at the charter's gate and at the end of the arc rather than run per series. This trades reviewer independence during the arc for speed and cost, deliberately: the program seat certifies only the mechanical layer per landing, and the adversarial read at the gate is done with fresh eyes (independent readers with no stake in the landings), the arrangement that produced Program Review 2-1.

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

**2. Design and code.** The program seat produces the formal design and builds `formal/`: the definitions, every target theorem proved, the verdict computed through tied flags, the build, the axiom check, and the gate. The product is the code and a short landing note (verdict, theorem list, anything that deviated from the outline and why).

**3. Landing check.** A mechanical self-check, not a skeptical review: build green, gate green, axiom check clean, tying theorem present, no vacuous audits, bridges named for every reuse, docstrings within their theorems. The landing is recorded in `status.md` with the note that it awaits the gate review. The next series may begin.

**4. Series review, batched.** The deep skeptical read (strip tests, non-degeneracy pressure, prose-versus-Lean, blind readers where the verdict is the desired one) runs for all landed series at once, at the charter's gate and again at the end of the arc, as part of the program review. Because the same seat builds and lands, this batched review is done with fresh independent readers, and it treats the landings' verdicts as claims to refute, not results to confirm.

**5. Series repair.** Runs when a review sends findings back. Each serious finding closes fixed (the strengthened target built, the theorem named) or relabeled (the obstruction recorded, the pre-registered alternative taken); real findings close on the ordinary schedule; cosmetic ones opportunistically. After the repair pass the affected series return to review. A repair that avoids its target re-enters review as a new serious finding; the loop ends only in acceptance or relabeling.

## Records

- `program-3/charter.md` — the fixed bar. Edited only for design errors or extensions.
- `program-3/status.md` — the living ledger. Every landing, review, finding, and repair gets its entry here, dated, in the order it happened. This file is the program's memory; nothing else needs to be.
- `program-3/series-N/outline.md` — one per series. Frozen at handoff except to fix a design error, and any such edit is noted in the status.
- `program-3/series-N/formal/` — the code.
- `program-3/spec/` — program reviews, their closure ledgers, and any scratch de-risk worth keeping.

## Build

Program 3 series register in `lake/lakefile.toml` and `scripts/gate.sh` like Program 2's did: one library per series, an axiom-check root per library, a gate line naming exactly what the series may import. Reuse of Program 1 or 2 layers is by import plus bridge theorem, per the charter's disciplines.
