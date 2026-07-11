# Relational Existentialism — Series 8 Protocol

**The process. Series 8 keeps the program's one load-bearing idea, that blind review has teeth only when the reviewer cannot see the motivation, and keeps the Series 5/6 batching: each phase runs once across the whole series, because the workstreams are one coupled object. The whole series stands on a single claim, that the finitude of holding makes the One many, moving, and layered at once, and that claim is only checkable across all the workstreams together.**

*Series 3 ran a seven-phase cycle per proof obligation. Series 4 collapsed that to five steps per workstream. Series 5 and 6 collapsed it further: the same phases (design, build, blind review, address), each run once over all seven workstreams together. Series 8 inherits the Series 6 shape unchanged. The coupling is at least as tight: the whole series stands on the claim that one fact (no relationally-identified node holds all perspectival restrictions, the no-god's-eye theorem) drives plurality, dynamics, and depth at once, and that is only checkable across all workstreams together. Series 8 is Part Two of the story Series 7 opened.*

---

## 0. Core principle

Four things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria, but **not** the charter's motivating prose. No "to attend is to become," no "finite perspective breaks the One," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Refuted hypothesis**, or **Circular** for WS7) with the obstruction made precise and routed, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss.
3. **Strip the *why*, keep the *what*, and strip the *word*, keep the *theorem*.** Beyond session-level blindness, Series 8 carries the statement-level strip test. For every payoff, delete the structural term, **"perspective," "restriction," "narrowing," "hold," "re-restriction," "face"**, and check whether the statement still goes through as a bare bisimulation, subsingleton, order, or reachability fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. The strip test is written into the WS1–WS5 designs and aggregated by WS7; the reviewer runs it.

Series 8 adds two emphases of its own, because its signature risks are the sharpest the program has faced since Series 6's painted-on engine:

4. **The bound must be tested, not assumed (conservation-by-fiat is the cardinal sin).** The whole "self-limiting universe" claim rests on conservation of breadth under narrowing being *proved or refuted*, never defined in. This is the exact trap the program must not fall into: a definition of re-restriction that *builds in* foreclosure, so that "breadth is conserved" is true by unfolding the definition rather than by a fact about relating. The review must, for WS5 specifically, unfold the re-restriction definition and confirm conservation is a *theorem about it or a refuted hypothesis*, not a clause inside it. Conservation assumed-in-a-definition is a SERIOUS finding, and the kill condition (charter §5.4) is the guard.
5. **Freeness must drive, not decorate (the Spinozist retreat must be refuted as a theorem).** The whole series rests on perspective being *free*, not recoverable from the plain relating, which is secured by the no-god's-eye theorem. The review must, for WS1 specifically, confirm the all-faces (god's-eye) node is *provably* bisimilar to the trivial self-loop and hence collapses, not merely *asserted* to be positionless. A god's-eye node that is excluded by fiat rather than collapsed by the engine is the Spinozist retreat smuggled past, and it is a SERIOUS finding: monism's escape hatch left open while the prose claims it is closed.

---

## 1. The documents

- **`charter.md`, the design (stable).** The question, the Series 7 collapse it answers, the no-god's-eye spine, the three consequences, the false escapes (weight/index/leaf), the conservation fork with its kill condition, the seven workstreams, success criteria, honest risks. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md`, the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, strip-test annotation. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md`, the design index.** Ties the seven together: the shared carrier choice (fixed once in WS1 and consumed by all), the primitive decision (holding-first, reaching-derived, charter §3), the cross-workstream triage summary, the predicted headline.
- **`charter-status.md`, the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the conservation fork's running status, the closed log, the series-review log. Where change lives.
- **`series-review.md`, the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it.

The charter + all designs are what you paste into the build session. The designs' signatures + outcome classes + charter criteria + the built code, stripped of motivating prose, are what you paste into a review session.

---

## 2. The process, phases batched across the series

Six phases. Phases D and E loop.

| Phase | Name | Session | Format | Batching |
|---|---|---|---|---|
| A | Charter | 1 | normal conversation with repo | once per series |
| B | Design-all | 1 | Claude code with repo | **all seven at once** |
| C | Build-all | 1 | Claude code with repo | **all seven at once** |
| D | Blind series-review | 1 | incognito with repo | **whole series at once** → writes `series-review.md` |
| E | Address | 1 | Claude code with repo | **whole series at once** |
| — | Accept / route | — | (bookkeeping into `charter-status.md`) | — |

The canonical run is **B → C → D → E → D → E** (two review passes, three code touches counting the initial build), with more D→E loops added only if a review pass still returns SERIOUS findings.

### Phase A — Charter (once)

Write `charter.md`: the question, the Series 7 collapse, the no-god's-eye spine and its three consequences, the false escapes, the conservation fork and kill condition, the workstreams, success criteria and outcome vocabulary, honest risks. **Done** — Series 8's charter is written; this protocol and `charter-status.md` are its companions.

### Phase B — Design all seven (one session, with context)

**Prompt to seed the design session:**

> You are writing all seven per-workstream design docs for Series 8 in one session, with `charter.md` and the repository in view. Series 8 is standalone but transcribes (does not import) machinery from Series 7 and Series 4. Name the theorems to be transcribed: the engine (`ws1_atomless_bisim`, the both-atomless bisimulation), the collapse (`ws2_import_theorem`, `ws2_import_theorem_static`), the restriction primitive and its two-sided face (the Series 4 restriction structure, `x↾(x,y)`), the semantic import test (`ws4_free_label_is_import`, `ws4_recoverable_not_import`), the reachability relation (`SReaches`), the hereditary-non-emptiness predicate (`SHNE`), behavioral/relational identity (`BehaviorallyIdentified`), and `ProgramVerdict`. Every design must contain:
>
> - **3 to 7 candidate framings** of the obligation, each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (the carrier home; the functor; the restriction/hold object; the re-restriction map; the order derived from re-restriction sequences), the success condition, and the explicit failure mode (collapse / recoverable-hence-not-free / painted-on-order / conservation-assumed / non-termination).
> - **A paper-decidable triage** per candidate, a check runnable by inspection before writing Lean, collapsed into a table, with the framing choice downstream of the triage.
> - **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems.
> - **Outcome classes** (Discharged / Impossibility / Partial / Refuted hypothesis / Failed / — WS7 — Circular) with pre-registered honest alternatives, and the **strip-test annotation** per payoff (which structural word, deleted, would be the test).

Two Series-8-specific design duties, settled in this batch:

- **The carrier home and the hold primitive are chosen once (WS1) and are ambient for all.** The restriction/hold `x↾(x,y)` is the primitive (charter §3, holding-first); reaching is derived. Whichever concrete carrier WS1 picks becomes the setting WS2–WS6 are written against. Do not let two workstreams assume different homes or different primitives.
- **The order `≺` is derived once (WS3) from re-restriction sequences and its endogeneity is the theorem.** The relation "`m ≺ m′` iff `m′` is reached by a re-restriction (narrowing) from `m`" must be a single definite order that WS3 (forced dynamics) and WS4 (narrowing/depth) both consume; the imported-index branch is designed in as a pre-registered *failure* mode to be refuted, not a fallback to adopt.

### Phase C — Build all seven (one session, with repo context)

**Prompt to seed the build session:**

> Realize every Series 8 design in `formal/Series8/wsNN.lean`, building `Series8.lean` and `AxiomCheck.lean`, self-contained: transcribe Series 7/4 machinery, import nothing from `series-7/`, `series-4/`, or `archive/`. Respect the dependency order (§4): WS1 first (blocking, the spine + carrier + hold primitive), then WS2, then WS3 (the re-restriction engine), then WS4–WS6, then WS7. The build produces theorems (or precise impossibilities, or a refuted conservation hypothesis) matching the designs' signatures. Update `charter-status.md` as you go. Sorry-free and axiom-clean or it is not done.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield. Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS3 needing the hold to expose re-restriction as a first-class operation WS1 did not provide) is handled by the pre-registered fallback in the affected design, not by an ad hoc patch.

The first incremental build takes longer than two minutes. Please run it as a background task at the start of the session.

**The first file is WS3's re-restriction map** in spirit even though WS1 builds first: WS1 establishes the carrier, hold, and the no-god's-eye spine; but the object the whole of Part Two turns on is the re-restriction map (charter §3), and its two easy obligations, **(NL)** no leaf and **(NF)** not-a-function, should be discharged early as the seed. **Conservation (CB) is NOT attempted in the build until WS5**, and is never built into the re-restriction definition.

### Phase D — Blind series-review (one session) → `series-review.md`

**Prompt to seed the blind review session:**

> Please clone https://github.com/colleen-love/relational-existentialism and view the series 8 working branch.

> Review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' stated targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no signature that quietly weakens the target? Specifically for Series 8, without building the code, run:

- **The Spinozist-retreat check (§0.5), the sharpest on the positive side.** Unfold WS1's no-god's-eye theorem. Is the all-faces (god's-eye) node *proved* bisimilar to the trivial self-loop and hence collapsed by the engine, or merely *asserted* positionless / excluded by a definitional clause? If the latter, monism's escape is smuggled past, a SERIOUS finding.
- **The conservation-by-fiat check (§0.4), the sharpest on the bound side.** Unfold WS3's re-restriction definition. Does "breadth is conserved under narrowing" (WS5) follow from a *fact about the map* or from a *clause inside the map's definition*? If foreclosure is baked into the definition, conservation is assumed, not shown, a SERIOUS finding. Confirm the kill condition (charter §5.4) was actually run: was a depth-opening-without-foreclosure re-restriction *attempted* and either built (Refuted) or shown impossible (Discharged/Partial)?
- **The strip test on every payoff (§0.3).** Delete "perspective" from the plurality payoff; delete "narrowing" from the depth payoff; delete "re-restriction" from the forced-dynamics payoff; delete "face" from the no-god's-eye collapse; delete "hold" from the bound. Flag every payoff that survives stripping as a bare bisimulation / subsingleton / order / reachability fact, not an earned perspective theorem.
- **The freeness verdict (WS2).** Is perspective proved *free* (not recoverable from the plain relating), or is the restriction defined so it is trivially free / trivially recoverable? Confirm which of {monism-broken, monism-reasserts, recoverable-hence-collapsed} the code actually delivers, tied to the Series 4/WS4 semantic import test.
- **The endogenous-order verdict (WS3).** Is `≺` *derived* from re-restriction sequences, or is it an imported stage-index (the Series 5 trap) wearing the name "narrowing order"? Is the forcing of dynamics ("a finite hold cannot statically contain an atomless field") a *theorem*, or an intuition asserted between two definitions?
- **The no-leaf verdict (WS3).** Confirm (NL): re-restriction preserves `SHNE`, never empties a node, honoring the hard rejection of limit-atomlessness. A transient bare relatum anywhere is a SERIOUS finding (the constraint Series 8 exists to respect).
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open, e.g. WS2's plurality depending on WS1's freeness; WS4's depth depending on WS3's re-restriction being genuinely narrowing; WS5's conservation depending on WS3's order being genuinely endogenous. The batched review is the only place this is visible.
- **The coincidence rule** where it applies: is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS1 no-god's-eye vs. relational identity; WS3 forced-dynamics vs. finitude; WS5 conservation vs. re-restriction.)
- **The conservation verdict, stated plainly.** Which of {Discharged, Refuted hypothesis, Partial} did the code deliver for conservation? Confirm it is one of these and is honestly labelled, never assumed-and-unstated.
- **The axiom-check status.** Was `#print axioms` actually run over every headline, or is the claim still static?

Write `series-review.md`: findings graded SERIOUS (the verdict rests on it, a flagship payoff laundering, the Spinozist retreat smuggled, conservation assumed-in), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed, no goalpost-moving: "relabel this / prove that / strip and re-prove / run the kill condition," never "lower the bar."

If there is a serious finding, continue to Phase E. If not, conclude with Phase F.

### Phase E — Address `series-review.md` (one session)

**Prompt to seed the blind review session:**

Please pull your branch, review the most recent `series-review.md` file, and address every finding. **Attempt the charter-strength theorem first**; where it provably resists, deliver an honest Partial/Impossibility/Refuted with the obstruction precise. Many corrections will be *relabels, not fixes* (a payoff shown to be a bare order fact is renamed and demoted; a conservation "proof" shown to unfold to its definition is demoted to a refuted or assumed hypothesis and the "self-limiting" claim retracted), and that is a correct outcome, not a failure. Record every change in `charter-status.md` (the series-review log and the affected workstream rows); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

### Phase F

**Prompt to seed the blind review session:**

Please pull your branch, review the most recent `series-review.md` file, and address every finding. **Attempt the charter-strength theorem first**; where it provably resists, deliver an honest Partial/Impossibility/Refuted with the obstruction precise. Many corrections will be *relabels, not fixes* (a payoff shown to be a bare order fact is renamed and demoted; a conservation "proof" shown to unfold to its definition is demoted to a refuted or assumed hypothesis and the "self-limiting" claim retracted), and that is a correct outcome, not a failure. Record every change in `charter-status.md` (the series-review log and the affected workstream rows); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

Once you are finished, this series is closed. Please write a `summary.md`, a `summary-technical.md` and update the root readme to reflect your findings. Great work.

---

## 3. Why the review is batched at series level (not per workstream)

Series 4 reviewed per workstream and caught most gaps, but its sharpest findings came from its end-of-series adversarial review, which saw all workstreams at once. Series 5 and 6 promoted the whole-series blind review to the primary vehicle because their payoffs were meant to be consequences of a single fact. Series 8's payoffs are just as tightly coupled: plurality, dynamics, and depth are all meant to be consequences of one fact (no god's-eye node), so a payoff can look earned in its own file while secretly being the shared collapse relabelled, the order painted on, or conservation assumed. Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it: the reviewer sees the whole dependency graph and can trace a "discharged" payoff to the open obligation in another file that actually carries it.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude, a stated limitation, not claimed independence. The objective anchors, the dependency graph, the `#print axioms` records, the strip-test results, the Spinozist-retreat unfolding, the conservation kill condition, and WS7's freeness/conservation ledger, are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 8:

- **WS1 is blocking.** The gate is the spine: no relationally-identified god's-eye node exists (the all-faces node collapses to the One). Nothing downstream is sound until this lands, because it is what makes perspective *free*. WS1 also fixes the carrier and the hold primitive, ambient for all.
- **WS2 depends on WS1's freeness.** Perspective breaks the collapse only if the restriction is free, not recoverable; WS1 secures it. WS2's plurality is stated with freeness as a hypothesis until WS1 discharges it.
- **WS3 supplies the engine the rest consume.** The re-restriction map (WS3) is what WS4's depth and WS5's conservation run on. Build WS3's map and discharge (NL)+(NF) before closing WS4–WS5; until then those are stated with re-restriction as a hypothesis. WS3 also derives the order `≺` endogenously, a forward dependency for anything time-shaped.
- **WS4 consumes WS3.** Narrowing/depth needs the re-restriction map; reachability-as-trace needs the order.
- **WS5 owns the conservation fork and consumes WS3.** Conservation is a claim *about* re-restriction; it cannot be attempted until the map exists, and it must never be folded into the map. WS5 runs the kill condition and reports Discharged / Refuted / Partial.
- **WS6 (heuristic ceiling)** reports the universal forms of WS4 (depth) and WS5 (conservation) where they exceed what is rangeable.
- **WS7 runs last.** It audits all others, unfolds the Spinozist-retreat and conservation-by-fiat risks, and aggregates the strip-test and freeness/conservation ledger; it cannot report until WS1–WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback, then propagated forward.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria | designs' motivating prose; charter's metaphysical framing (no "to attend is to become," no "finite perspective breaks the One") |
| Address (Phase E) | `series-review.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level, plus, for Series 8, **unfold the god's-eye node and check it collapses**, and **unfold re-restriction and check conservation is not baked in**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series, the next series' plan

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 8 closes. The final `series-review.md` and `charter-status.md` become the **seed of Series 9**, following the program's inter-series discipline:

> **Each series is a response to the previous series' honest findings, not a continuation of its plan.**

The pattern (Series 1 → 2 → ... → 8): each series takes the place the mathematics pushed back hardest in the prior series and makes *that* its question. Series 7's hardest pushback was that the collapse to the One left plurality unexplained except by import; Series 8's response is finite perspective. Whatever Series 8's final review surfaces as its hardest resistance, the charter forecasts it will be either the Spinozist retreat (WS1, the god's-eye node not provably collapsing), conservation refuted or assumed (WS5), or the order not endogenous (WS3), becomes Series 9's question. If conservation is refuted, Series 9's question is likely "what bounds the many if not conservation." If the Spinozist retreat holds, Series 9 inherits monism's counterattack as its problem.

The mechanics, unchanged:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone**, its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again, design-all, build-all, then the review→address loop.

---

*Protocol for Series 8. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and, once written, `spec/wsNN-design.md` (the per-workstream contracts) and `series-review.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `series-review.md`. The whole-series blind review is the primary vehicle, and Series 8 sharpens it with two checks, because the series stands or falls on whether the god's-eye node genuinely collapses (freeness, against the Spinozist retreat) and whether conservation is genuinely tested rather than assumed (the bound, against conservation-by-fiat). No em dashes in final academic paper copy; this working protocol is not final copy.*
