# Relational Existentialism — Series 4 Protocol

**The process. Simpler than Series 3's seven-phase cycle: charter, then design each workstream with context, build against the repo, review blind against both design and charter, loop review back to build if needed. At series end, a full blind project review produces the next series' plan.**

*Series 3 ran a seven-phase cycle per proof obligation, alternating blind and against-charter phases with an incognito session for each. It worked but was heavy. Series 4 keeps the one idea that gave Series 3 its integrity — **blind review has teeth only when the reviewer cannot see the motivation** — and drops the ceremony around it.*

---

## 0. Core principle

Two things carry over unchanged, because they are what made Series 3 honest:

1. **Blind means blind.** A blind phase runs in a fresh session seeded with the design and the repo, but **not** the charter's motivating prose — no "grain not wall," no "finitude of facing," no metaphysics. The reviewer sees the mathematical claim and the code, and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal.** When a build falls short, the honest outcome is a **Partial** with the obstruction made precise and routed — never a quiet redefinition of the target. The charter is the fixed bar; the status file records the miss.

Everything else is lighter.

---

## 1. The two documents that don't move, and the one that does

- **`charter.md` — the design (stable).** Commitments, framework, the seven workstreams, success criteria, risks. Edited *only* to fix an error in the design itself, never to record progress. If an edit changes work upstream of something already built, the affected workstreams reopen.
- **`spec/wsN/design.md` — the per-workstream design (stable once committed).** Candidates, paper-decidable triage, the winning construction, outcome classes, deliverable. This is the contract a build is judged against.
- **`charter-status.md` — the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the closed log. This is where change lives.

The charter and the designs are what you paste into a build session. The charter alone, stripped of a workstream's design rationale, plus the built code, is what you paste into a blind review.

---

## 2. The process, per workstream

Five steps. Steps 3–4 loop.

| Step | Name | Sees |
|---|---|---|
| 1 | Charter | (the whole program; done once, up front) |
| 2 | Design | charter + repo (for reusable machinery) |
| 3 | Build | design + repo |
| 4 | Blind review | design + built code + charter criteria — **not** the design's motivating prose |
| 5 | Accept / route | (bookkeeping into the status file) |

### Step 1 — Charter (once per series)

Write `charter.md`: the question, the commitments, the framework, the workstreams, the success criteria and outcome vocabulary, the honest risks. This is the whole-series act; it does not repeat per workstream. Series 4's charter is written.

### Step 2 — Design a workstream (with context)

For each workstream, write `spec/wsN/design.md` **with full context**: the charter in view, and the repo in view so the design references real, reusable machinery by name (in Series 4: `PkObj`, `Coalg`, `bisim_eq`, `Reaches`, `carrier_card_ge`, the Łukasiewicz / `ℕ∞` witnesses, and so on) rather than reinventing it. Every design must contain:

- **3–5 candidates** for each object at stake.
- **A triage that is decidable on paper** per candidate — a check you can run by inspection, before writing Lean, that says whether the candidate is viable (e.g. "does this functor preserve weak pullbacks? decidable by whether the face-constraint is a sub-object" or "is this quantale ⊥-divisor-free? decidable from its multiplication table").
- **The winning candidate(s)** worked out to typed theorem signatures.
- **Outcome classes** (Discharged / Impossibility proved / Partial / Failed / — for WS7 — Trivialized) with the pre-registered honest alternatives.

Designs may be written in any order, but respect dependencies (§4). Once committed, a design is the stable contract for its build.

### Step 3 — Build (with repo context)

Realize the design in `formal/wsN.lean`, against the repository so the build reuses Series 3 machinery directly. The build produces theorems (or precise impossibilities) matching the design's signatures. A build may discover the design was wrong; if so, it **stops and reports** rather than silently retargeting — the design is corrected (Step 2 re-run) and the build restarts. Building past a broken design is the one prohibited move.

### Step 4 — Blind review (against design and charter)

In a **fresh session**, hand the reviewer:

- the built code (`formal/wsN.lean`),
- the design's **theorem signatures and outcome classes** (the contract),
- the charter's **success criteria** (the bar),
- **but not** the design's motivating prose or the charter's metaphysical framing.

The reviewer answers, adversarially: *does this code prove these theorems, do these theorems meet the design's stated targets, and do they satisfy the charter criteria they claim — with no `sorry`, no custom axiom, no signature that quietly weakens the target?* The reviewer checks the naming discipline (no `*_resolved` while a hole remains), the coincidence rule where it applies (is a "forced" theorem genuinely independent of the "definitional" one, or does its proof secretly unfold to the definition?), and the axiom-check status (was `#print axioms` actually run, or is the claim still *static*?).

The reviewer returns one of: **passes** (build accepted), or **fails with specific findings** (routed back to Step 3).

### Step 5 — Accept or route

- **Passes** → record in `charter-status.md`: status class, discharged theorems, coincidence status, axiom-check status, any obligation routed onward. Move closed items to the closed log.
- **Fails** → the findings go back to **Step 3 (build)**, or, if the fault is in the design itself, back to **Step 2 (design)**. The review→build loop repeats until the review passes or the honest outcome is a reported Partial/Failed/Impossibility (all of which are valid terminal states — a sharp impossibility is a success, not a loop-forever condition).

The loop's exit is not "the build finally passes" — it is "the build passes **or** the reviewer and the design agree the honest outcome is a precise Partial/Impossibility." Do not grind a genuine impossibility against the review; report it.

---

## 3. End of series — full blind project review, then the next plan

When every workstream has reached a terminal state, the series closes with two acts.

### 3a — Full blind project review

A fresh session reviews the **whole series at once**, blind: all built code, all design contracts, all charter criteria — **without** the charter's motivating prose. This is the Series 4 analogue of Series 3's WS9/WS10 external audit, and it exists to catch what per-workstream reviews cannot:

- **Cross-workstream laundering** — a claim that looks discharged in isolation but leans on a hypothesis another workstream left open (Series 3's `hcard` was exactly this).
- **The trivialization verdict** — for Series 4 specifically, whether the payoffs genuinely reduce to distinct consequences of one finitude (WS7's distinctness ledger) or collapse into one definition. The project review is where **Trivialized** is confirmed or refuted at the whole-program level.
- **Over-labels** — statuses claimed stronger than the code supports (Series 3's "atomlessness automatic" was corrected here).

Its findings are folded into `charter-status.md` and may reopen workstreams. **Disclosure, carried from Series 3:** this review is Claude-reviewing-Claude — a stated limitation, not claimed independence. The objective anchors (dependency graphs, `#print axioms` records, the distinctness ledger) are what keep it honest despite that.

### 3b — The next series' plan

The project review's findings become the **seed of the next series**. The inter-series iteration is the heart of this program's method, and it is deliberate, not incidental:

> **Each series is a response to the previous series' honest findings — not a continuation of its plan.**

Concretely, the pattern Series 1 →2 → 3 → 4 has followed:

- **Series 1** built the first mechanization and was met by a review that exposed foundational mathematical failures.
- **Series 2** restarted the program in a new mathematical arena but was met with a review that exposed a crippling methodology weaknesses.
- **Series 3** was a *redesign in response*, not an extension: it rebuilt the foundation, added the register discipline, and its central finding (the interdependence / fracture result) came out of taking Series 2's resistances seriously.
- **Series 4** is a *response to Series 3's central fracture* — the bound-as-fiat — and reframes the whole program around making the bound endogenous. It inherits Series 3 as prior art but presupposes none of it.

So the inter-series step is: **read the closed project review, find the finding that most resists — the place the mathematics pushed back hardest — and make the next series about that.** Series 3's hardest pushback was "bounding buys existence but is a fiat that drains the global claims"; Series 4 is the series that takes that seriously. Whatever Series 4's project review surfaces as *its* hardest resistance becomes Series 5's question.

The mechanics:

1. Freeze the closing series under `archive/` (as Series 2 is frozen). It stays readable as origin, normative for nothing.
2. Write the new charter as **standalone** — stating its own question and building its own object from scratch, with the prior series as informing prior art, exactly as Series 4's charter relates to Series 3.
3. Carry forward *machinery* freely (the Lean files are reusable), but carry forward *claims* only by re-deriving or explicitly citing them. A new series does not inherit discharges; it earns or re-imports them.
4. New workstreams are framed as responses to the prior findings, and the cycle (§2) begins again.

---

## 4. Dependencies and ordering

Workstreams are not independent; build in dependency order and let the status file track the edges. For Series 4 the load-bearing edges are:

- **WS1 is blocking** — its weak-pullback gate is existential; nothing downstream is sound until it is discharged (or the carrier is redirected).
- **WS3 forces WS1's R3 escalation** — the plurality payoff needs faces as independent data, which reopens the WS1 gate on the new functor. Build WS1(R2) first; when WS3 triggers R3, return to WS1 before completing WS3.
- **WS2 exports the collapse to WS3** — WS3's coincidence theorem cites `ws2_collapse` as its forced counterweight; WS2's collapse must be built first.
- **WS4 and WS6 reuse WS1's `face` and Series 3's cardinality / diagonal results** — buildable once WS1 lands.
- **WS7 runs last** — it audits all others and cannot report until they have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in the status file. This is the one place the process is strict: **upstream changes invalidate downstream builds**, and the status file must show it.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design (Step 2) | charter + repo | — |
| Build (Step 3) | design + repo | — |
| Blind review (Step 4) | built code + design signatures + charter criteria | design's motivating prose; charter's metaphysical framing |
| Project review (Step 3a) | all code + all design contracts + charter criteria | charter's motivating prose |

The review sessions are the only blind ones, and the blindness is a single, checkable rule: **strip the *why*, keep the *what*.** A reviewer who can see why a theorem matters is tempted to grade the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

*Protocol for Series 4. Companion to `charter.md` (the design), `spec/wsN/design.md` (the per-workstream contracts), and `charter-status.md` (the ledger). Five steps per workstream with a review→build loop; a full blind project review at series end; and an inter-series step that makes each new series a response to the last one's hardest finding rather than a continuation of its plan. No em dashes in final academic paper copy; this working protocol is not final copy.*
