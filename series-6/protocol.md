# Relational Existentialism — Series 6 Protocol

**The process. Series 6 keeps the program's one load-bearing idea — blind review has teeth only when the reviewer cannot see the motivation — and keeps Series 5's batching: each phase runs once across the whole series, because the workstreams are one coupled object (the process is one thing; the payoffs are meant to be consequences of a single incompletion), and reviewing them in isolation would miss exactly the cross-workstream laundering the audit exists to catch.**

*Series 3 ran a seven-phase cycle per proof obligation. Series 4 collapsed that to five steps per workstream with a per-workstream review loop. Series 5 collapsed it further: the same phases (design, build, blind review, address), each run once over all seven workstreams together. Series 6 inherits the Series 5 shape unchanged — the coupling is, if anything, tighter here, since the whole series stands on the claim that one fact (the diagonal, the failure of self-knowledge to close) drives groundlessness, plurality, and time at once, and that claim is only checkable across all the workstreams together.*

---

## 0. Core principle

Three things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria — but **not** the charter's motivating prose. No "incompleteness as fuel," no "self-knowing gives time its arrow," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Trivialized** for WS7) with the obstruction made precise and routed — never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss.
3. **Strip the *why*, keep the *what* — and strip the *word*, keep the *theorem*.** Beyond session-level blindness, Series 6 carries the statement-level strip test inherited from Series 4/5 adversarial review, sharpened for this series' load-bearing words. For every payoff, delete the structural term — **"diagonal," "self-survey," "residue," "later," "face"** — and check whether the statement still goes through as a bare fixed-point, cardinality, or order fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. The strip test is written into the WS3/WS4/WS5/WS6 designs and aggregated by WS7; the reviewer runs it.

Series 6 adds one emphasis of its own, because its signature risk is the sharpest the program has faced:

4. **The engine must drive, not decorate.** The whole series rests on the transition *being* the diagonal residue, not on a dynamics defined elsewhere with diagonal-vocabulary applied. This is the exact trap Series 3's attention fell into (bolted-on replicator dynamics) and Series 5's grade-shift Trivialized on. The review must, for WS3 specifically, unfold the transition's definition and confirm the residue is *literally* it — not merely that a theorem relating them is provable. "Painted on" is a SERIOUS finding.

---

## 1. The documents

- **`charter.md` — the design (stable).** The question, the Static Collapse, the false repairs, the diagonal-driven process, the seven workstreams, success criteria, honest risks. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md` — the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, deliverable, strip-test annotation. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md` — the design index.** Ties the seven together: the shared ambient-theory choice (the carrier home — guarded / metric / pro-object — is fixed here once, in WS1, and consumed by all), the cross-workstream triage summary, the predicted headline.
- **`charter-status.md` — the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the closed log, the series-review log. Where change lives.
- **`series-review.md` — the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it.

The charter + all designs are what you paste into the build session. The designs' signatures + outcome classes + charter criteria + the built code, stripped of motivating prose, are what you paste into a review session.

---

## 2. The process — phases, batched across the series

Six phases. Phases D and E loop.

| Phase | Name | Session | Sees | Batching |
|---|---|---|---|---|
| A | Charter | 1 | (whole program) | once per series |
| B | Design-all | 1 | charter + repo | **all seven at once** |
| C | Build-all | 1 | all designs + repo | **all seven at once** |
| D | Blind series-review | 1 | all built code + all design contracts + charter criteria — **not** motivating prose | **whole series at once** → writes `series-review.md` |
| E | Address | 1 | `series-review.md` + all code + designs | **whole series at once** |
| — | Accept / route | — | (bookkeeping into `charter-status.md`) | — |

The canonical run is **B → C → D → E → D → E** (two review passes, three code touches counting the initial build), with more D→E loops added only if a review pass still returns SERIOUS findings.

### Phase A — Charter (once)

Write `charter.md`: the question, the Static Collapse, the diagonal-driven repair, the workstreams, the success criteria and outcome vocabulary, the honest risks. **Done** — Series 6's charter is written; this protocol and `charter-status.md` are its companions.

### Phase B — Design all seven (one session, with context)

In a single session with the charter and repo in view, write all of `spec/ws01-design.md … ws07-design.md` plus `spec/README.md`. The repo is in view so designs reference real, reusable machinery *by name* — and, because Series 6 is standalone, name the Series 4/5 theorems that will be **transcribed** (not imported): the carrier machinery (`PkObj`, `Coalg`, `bisim_eq`, `νLk`, `lcomp`, `carrier_card_ge`), the collapse (`ws2_collapse`, `ws5_global_groundless_collapses`), the diagonal (`ws6_lawvere_incomplete`, `ws6_omega_nonterminating`), the two-sided face (the Series 4 restriction structure), the tower colimit (`ws1_bisim_eq_colim`) as the static object WS2 must subsume, and `ProgramVerdict`. Every design must contain:

- **3–7 candidate framings** of the obligation — different ways to cash out the commitment as something provable — each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (the carrier home; the functor `F`; the fixed-point-free map that is the time-step; the order `≺` for WS5), the success condition, and the explicit failure mode (collapse / non-existence / painted-on / laundered order / non-convergence).
- **A paper-decidable triage** per candidate — a check runnable by inspection before writing Lean — **collapsed into a table**, with the framing choice *downstream* of the triage.
- **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems.
- **Outcome classes** (Discharged / Impossibility / Partial / Failed / — WS7 — Trivialized) with pre-registered honest alternatives, and the **strip-test annotation** per payoff.

Two Series-6-specific design duties, settled in this batch:

- **The carrier home is chosen once (WS1) and is ambient for all.** Guarded recursion / topos of trees is the charter's lead; the metric completion and the pro-object are the pre-registered alternatives. Whichever WS1 picks becomes the setting WS3–WS6 are written against — do not let two workstreams assume different homes.
- **`≺` is fixed once (WS5) and its totality is the theorem.** The relation "`m ≺ m′` iff `m′` is a diagonal residue of a survey at `m`" must be a single definite order that WS4 (directionality) and WS5 (totality/relativity) both consume; the Ω-absolute-frame branch is designed in as a pre-registered alternative, not discovered late.

### Phase C — Build all seven (one session, with repo context)

In a single session, realize every design in `formal/wsNN.lean`, building `Series6.lean` and `AxiomCheck.lean`, self-contained (transcribe Series 4/5 machinery; import nothing from `series-5/`, `series-4/`, or `archive/`). Respect the dependency order (§4): WS1 first (blocking), then WS2, then WS3, then WS4–WS6, then WS7. The build produces theorems (or precise impossibilities) matching the designs' signatures. Update `charter-status.md` as you go.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield. Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS3 needing the carrier to expose the residue as a first-class operation that WS1 did not provide) is handled by the pre-registered fallback in the affected design (WS1's carrier-home escalation: guarded → metric → pro-object), not by an ad hoc patch.

Please make sure to update `charter-status.md` as you complete each workstream.

### Phase D — Blind series-review (one session) → `series-review.md`

In a fresh session, seeded with the built code, the design signatures, and the charter criteria but **not** the motivating prose, review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' stated targets; do they satisfy the charter criteria they claim — with no `sorry`, no custom axiom, no signature that quietly weakens the target? Specifically for Series 6, run:

- **The engine-drive check (§0.4), the sharpest.** Unfold WS3's transition. Is the successor *literally* the diagonal residue, or is it a separately-defined evolution with a theorem relating it to the diagonal? If the latter, the engine is painted on — a SERIOUS finding, the Series 3/5 trap.
- **The strip test on every payoff (§0.3).** Delete "diagonal" from the engine identity; delete the external time index from the arrow; delete "face" from the causal-order incomparability; delete "residue" from no-view-from-nowhere. Flag every payoff that survives stripping as a bare fixed-point / cardinality / order fact, not an earned process theorem — exactly the S1/S2 findings that reshaped Series 4 and the R1 finding that demoted Series 5's V3.
- **The relativity verdict (WS5).** Is `≺` proved total or partial? Is incomparability genuinely nonempty and genuinely tied to the two-sided face, or is it posethood relabelled "causal order"? Is the Ω-absolute-frame branch honestly adjudicated rather than assumed away? Confirm which of {global time, relativity, laundered} the code actually delivers.
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open — e.g. WS6's globally-atomless-and-plural depending on WS1's gate; WS5's partiality depending on WS3's residue being genuinely two-sided; WS4's endogeneity depending on WS1's carrier having no first stage. The batched review is the only place this is visible.
- **The coincidence rule** where it applies — is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS3 `ws3_diagonal_drives`, WS6 `ws6_one_engine`, WS6 `ws6_no_view_from_nowhere`.)
- **The trivialization verdict.** Do groundlessness, plurality, and directed plural time reduce to distinct consequences of the one incompletion (WS7's distinctness ledger), or collapse into one definition? Confirm or refute Trivialized at the whole-program level.
- **The axiom-check status** — was `#print axioms` actually run, or is the claim still static?

Write `series-review.md`: findings graded SERIOUS (the verdict rests on it — a flagship payoff laundering, or the engine painted on), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed — no goalpost-moving: "relabel this / prove that / strip and re-prove," never "lower the bar."

### Phase E — Address `series-review.md` (one session)

In a code session with `series-review.md`, all code, and all designs in view, address every finding. **Attempt the charter-strength theorem first**; where it provably resists, deliver an honest Partial/Impossibility with the obstruction precise. Many corrections will be *relabels, not fixes* (a payoff shown to be a bare order fact is renamed and demoted, as Series 4's `ws4_no_top_endogenous → ws4_no_top_reach` and Series 5's V3), and that is a correct outcome, not a failure. Record every change in `charter-status.md` (the series-review log and the affected workstream rows); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

Then loop back to Phase D for another blind pass. Exit when a review pass returns no SERIOUS findings and the remaining REAL items are correctly-labelled terminal Partials/Impossibilities — **not** "the build finally passes at charter strength." Do not grind a genuine impossibility (or a genuine Trivialized) against the review; report it.

---

## 3. Why the review is batched at series level (not per workstream)

Series 4 reviewed per workstream and caught most gaps, but its *sharpest* findings came from its end-of-series adversarial review, which saw all workstreams at once. Series 5 promoted the whole-series blind review to the primary vehicle because its payoffs were meant to be consequences of a single fact (double-unboundedness) and the laundering risk was cross-workstream. Series 6's payoffs are *even more* tightly coupled: they are meant to be consequences of one incompletion (the diagonal), so a payoff can look earned in its own file while secretly being either the shared fixed-point fact relabelled or the engine painted on. Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it — the reviewer sees the whole dependency graph and can trace a "discharged" payoff to the open obligation in another file that actually carries it.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude — a stated limitation, not claimed independence. The objective anchors — the dependency graph, the `#print axioms` records, the strip-test results, the engine-drive unfolding, and WS7's distinctness ledger — are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 6:

- **WS1 is blocking.** The gate is existential; nothing downstream is sound until the process is shown to exist as a coherent, non-collapsing object with plurality-keeping sameness that carries the diagonal transition (or the carrier home is redirected). Built and reviewed first, and its choice of home (guarded / metric / pro-object) is ambient for all.
- **WS2 is the spine and can proceed in parallel with WS1's carrier choice**, because the Static Collapse is a fact about *finished* objects and does not depend on which dynamic home replaces them. But its *forced answer* (dynamism is the escape) needs WS1's process in hand to point at.
- **WS3 supplies the engine the rest consume.** The residue-as-successor transition (WS3) is what WS4's arrow, WS5's `≺`, and WS6's atomless-and-plural all run on. Build WS3's transition before closing WS4–WS6; until then those are stated with the residue as a hypothesis.
- **WS4 and WS5 share `≺`.** WS4 proves the order is directional; WS5 proves whether it is total or partial. They must consume one definition of `≺` (fixed in the WS5 design). WS5's relativity verdict depends on WS3's residue being genuinely two-sided (the two-sided face), a forward edge to WS3/WS1.
- **WS6 consumes WS1 + WS3.** Globally-atomless-and-plural needs the carrier (WS1) and the engine (WS3); the one-engine unification needs both groundlessness and plurality to be traced to the *same* residue mechanism.
- **WS7 runs last.** It audits all others, unfolds the engine drive, and aggregates the strip-test ledger; it cannot report until WS1–WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback (WS1's carrier-home escalation is the principal one), then propagated forward.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria | designs' motivating prose; charter's metaphysical framing |
| Address (Phase E) | `series-review.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level — plus, for Series 6, **unfold the transition and check the residue drives it**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series — the next series' plan

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 6 closes. The final `series-review.md` and `charter-status.md` become the **seed of Series 7**, following the program's inter-series discipline:

> **Each series is a response to the previous series' honest findings — not a continuation of its plan.**

The pattern (Series 1 → 2 → 3 → 4 → 5 → 6): each series takes the place the mathematics pushed back hardest in the prior series and makes *that* its question. Series 4's hardest pushback was that boundedness could not be made endogenous on one carrier; Series 5's response was to relocate the bound between levels, and *its* hardest pushback was that global groundlessness stayed unbuilt at the carrier (the tower was locally founded); Series 6's response is to make the world a process so groundlessness need never be completed. Whatever Series 6's final review surfaces as its hardest resistance — the charter forecasts it will be either the engine painted on (WS3), the relativity laundered or returned Newtonian (WS5), or the unification a conjunction (WS7) — becomes Series 7's question.

The mechanics, unchanged:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone** — its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again — design-all, build-all, then the review→address loop.

---

*Protocol for Series 6. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and — once written — `spec/wsNN-design.md` (the per-workstream contracts) and `series-review.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `series-review.md`. The whole-series blind review is the primary vehicle, and Series 6 sharpens it with the engine-drive check, because the series stands or falls on whether the diagonal genuinely drives the process or is painted onto it. No em dashes in final academic paper copy; this working protocol is not final copy.*
