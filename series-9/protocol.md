# Relational Existentialism — Series 9 Protocol

**The process. Series 9 keeps the program's one load-bearing idea, that blind review has teeth only when the reviewer cannot see the motivation, and keeps the Series 5/6/8 batching: each phase runs once across the whole series, because the workstreams are one coupled object. The whole series stands on a single claim, that the incompletability of self-inspection makes the One many, moving, and layered at once, from a single position, and that claim is only checkable across all the workstreams together.**

*Series 3 ran a seven-phase cycle per proof obligation. Series 4 collapsed that to five steps per workstream. Series 5, 6, and 8 collapsed it further: the same phases (design, build, blind review, address), each run once over all seven workstreams together. Series 9 inherits the Series 8 shape unchanged. The coupling is at least as tight: the whole series stands on the claim that one fact (no hold contains its own complete content, the diagonal spine) drives plurality, dynamics, and depth at once, and that is only checkable across all workstreams together. Series 9 is the program's return to its founding thesis, self-reference as the engine, and it is the response to Series 8's honest Partial.*

---

## 0. Core principle

Four things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria, but **not** the charter's motivating prose. No "self is a paradox," no "self-reference is the engine," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Refuted hypothesis**, or **Coincident**, or **Circular** for WS7) with the obstruction made precise and routed, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss.
3. **Strip the *why*, keep the *what*, and strip the *word*, keep the *theorem*.** Beyond session-level blindness, Series 9 carries the statement-level strip test. For every payoff, delete the structural term, **"self-reference," "diagonal," "residue," "re-diagonalization," "hold," "blind spot," "self-total"**, and check whether the statement still goes through as a bare fixed-point, subsingleton, order, or reachability fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. The strip test is written into the WS1-WS5 designs and aggregated by WS7; the reviewer runs it.

Series 9 adds two emphases of its own, because its signature risks are the sharpest the program has faced, inheriting Series 8's central finding directly:

4. **The diagonal must be a fixed-point contradiction, NOT a bisimulation (the coincidence re-hit is the cardinal sin).** The whole repair of Series 8 rests on the no-self-total-hold theorem being *independent* of relational identity. This is the exact trap Series 8 fell into and Series 9 exists to escape: a spine proof that, unfolded, routes through "all states bisimilar" (relational identity), so no-self-total-hold COINCIDES with the Series 7/8 collapse and is not the separable second fact claimed. The review must, for WS1 specifically, unfold the no-self-total-hold proof and confirm it is Cantor/Lawvere-shaped, a diagonal term the assumed self-total fixed point cannot contain, NOT a `ws1_symmetric_states_bisimilar`-shaped behavioral identity. A spine proof that unfolds to bisimulation is a **Coincident** result and a SERIOUS finding: Series 8's wall re-hit while the prose claims it is escaped. The coincidence rule is PROMOTED to a first-class spine check.
5. **Hold-reflexivity must be genuine, neither too weak nor too strong (the carrier is the whole battlefield).** The diagonal bites only if a hold genuinely ranges over the space of holds. The review must, for WS1 specifically, confirm the carrier is hold-REFLEXIVE (a hold ranging over holds) and not merely self-looping (`dest x ∋ x`, which Series 8 already showed collapses by coincidence, so a self-loop carrier silently reduces Series 9 to Series 8's Partial), and confirm it is `κ`-bounded so the diagonal is a genuine gap in a consistent object and not a Russell paradox that trivializes everything. A carrier too weak to diagonalize, or too strong to have a model, is a SERIOUS finding: the diagonal asserted rather than run, or run in an inconsistent theory.

---

## 1. The documents

- **`charter.md`, the design (stable).** The question, the Series 8 Partial it responds to, the diagonal spine, the three consequences, the false escapes (import/leaf/self-loop/coincidence), the monotonicity fork with its kill condition, the seven workstreams, success criteria, honest risks. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md`, the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, strip-test annotation. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md`, the design index.** Ties the seven together: the shared carrier choice (the hold-reflexive carrier, fixed once in WS1 and consumed by all), the primitive decision (the hold, from Series 8, plus hold-reflexivity, charter §3), the cross-workstream triage summary, the predicted headline.
- **`charter-status.md`, the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the monotonicity fork's running status, the closed log, the series-review log. Where change lives.
- **`spec/series-review-N.md`, the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it.

The charter + all designs are what you paste into the build session. The designs' signatures + outcome classes + charter criteria + the built code, stripped of motivating prose, are what you paste into a review session.

---

## 2. The process, phases batched across the series

Six phases. Phases D and E loop.

| Phase | Name | Session | Format | Batching |
|---|---|---|---|---|
| A | Charter | 1 | normal conversation with repo | once per series |
| B | Design-all | 1 | Claude code with repo | **all seven at once** |
| C | Build-all | 1 | Claude code with repo | **all seven at once** |
| D | Blind series-review | 1 | incognito with repo | **whole series at once** → writes `spec/series-review-N.md` |
| E | Address | 1 | Claude code with repo | **whole series at once** |
| F | Close | 1 | Claude code with repo | summaries + root README |

The canonical run is **B → C → D → E → D → E** (two review passes, three code touches counting the initial build), with more D→E loops added only if a review pass still returns SERIOUS findings.

### Phase A — Charter (once)

Write `charter.md`: the question, the Series 8 Partial it responds to, the diagonal spine and its three consequences, the false escapes, the monotonicity fork and kill condition, the workstreams, success criteria and outcome vocabulary, honest risks. **Done** — Series 9's charter is written; this protocol and `charter-status.md` are its companions.

### Phase B — Design all seven (one session, with context)

**Prompt to seed the design session:**

> You are writing all seven per-workstream design docs for Series 9 in one session, with `charter.md` and the repository in view. Series 9 is standalone but transcribes (does not import) machinery from Series 8, 7, and 4. Name the theorems to be transcribed: the hold and its face (Series 8's `Hold`/`afford`, the Series 4 restriction `x↾(x,y)`), the engine (`ws1_atomless_bisim`, the both-atomless bisimulation), the collapse (`ws2_import_theorem_static`), the semantic import test (`ws4_free_label_is_import`, `ws4_recoverable_not_import`), the reachability relation (`SReaches`), hereditary non-emptiness (`SHNE`), behavioral/relational identity (`BehaviorallyIdentified`), and the Series 8 coincidence witness (`ws1_symmetric_states_bisimilar`, transcribed as the thing the Series 9 spine must NOT unfold to). Every design must contain:
>
> - **3 to 7 candidate framings** of the obligation, each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (the hold-reflexive carrier; the functor; the hold object; the self-total fixed-point equation; the re-diagonalization map; the tower order derived from re-diagonalization sequences), the success condition, and the explicit failure mode (coincidence-with-relational-identity / self-loop-too-weak / Russell-too-strong / residue-recoverable-hence-not-free / painted-on-order / monotonicity-assumed / non-termination).
> - **A paper-decidable triage** per candidate, a check runnable by inspection before writing Lean, collapsed into a table, with the framing choice downstream of the triage.
> - **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems.
> - **Outcome classes** (Discharged / Impossibility / Partial / Refuted hypothesis / Coincident / Failed / — WS7 — Circular) with pre-registered honest alternatives, and the **strip-test annotation** per payoff (which structural word, deleted, would be the test).

Two Series-9-specific design duties, settled in this batch:

- **The hold-reflexive carrier is chosen once (WS1) and is ambient for all.** The carrier must admit a hold ranging over the space of holds so the self-total hold is expressible-and-refutable; it must be `κ`-bounded so the diagonal is a genuine gap in a consistent object; it must be strictly stronger than a self-loop carrier (or the diagonal cannot run and the spine reduces to Series 8's coincidence). Whichever concrete carrier WS1 picks becomes the setting WS2-WS6 are written against. Do not let two workstreams assume different homes.
- **The tower order `≺` is derived once (WS3) from re-diagonalization sequences and its endogeneity is the theorem.** The relation "`m ≺ m′` iff `m′` is reached by a re-diagonalization from `m`" must be a single definite order that WS3 (forced dynamics) and WS4 (tower/depth) both consume; the imported-index branch is designed in as a pre-registered *failure* mode to be refuted, not a fallback.

### Phase C — Build all seven (one session, with repo context)

**Prompt to seed the build session:**

> Realize every Series 9 design in `formal/Series9/wsNN.lean`, building `Series9.lean` and `AxiomCheck.lean`, self-contained: transcribe Series 8/7/4 machinery, import nothing from `series-8/`, `series-7/`, `archive/`. Respect the dependency order (§4): WS1 first (blocking, the hold-reflexive carrier + the diagonal spine + the hold primitive), then WS2, then WS3 (the re-diagonalization engine), then WS4-WS6, then WS7. The build produces theorems (or precise impossibilities, or a refuted monotonicity hypothesis, or an honest Coincident spine) matching the designs' signatures. Update `charter-status.md` as you go. Sorry-free and axiom-clean or it is not done.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial (or Coincident, for the spine) with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield. Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS3 needing the carrier to expose re-diagonalization as a first-class operation WS1 did not provide) is handled by the pre-registered fallback in the affected design, not by an ad hoc patch.

The first incremental build takes longer than two minutes. Please run it as a background task at the start of the session.

**The first file is WS3's re-diagonalization map** in spirit even though WS1 builds first: WS1 establishes the hold-reflexive carrier, the hold, and the diagonal spine; but the object the whole tower turns on is the re-diagonalization map (charter §3), and its two easy obligations, **(NL)** no leaf and **(NF)** not-a-function, should be discharged early as the seed. **Monotonicity (MG) is NOT attempted in the build until WS5**, and is never built into the re-diagonalization definition.

**The single most important build check (Series 9's reason to exist):** when WS1's no-self-total-hold theorem is built, immediately `#print` its proof term / unfold its structure and confirm it is a diagonal fixed-point contradiction and does NOT reduce to `ws1_symmetric_states_bisimilar` or any behavioral-identity lemma. If it does, the spine is **Coincident**, Series 8's wall is re-hit, and that must be recorded honestly in `charter-status.md`, not papered over. The whole series succeeds or fails on this one check.

### Phase D — Blind series-review (one session) → `spec/series-review-N.md`

**Prompt to seed the blind review session:**

> Please clone https://github.com/colleen-love/relational-existentialism and view the series 9 working branch.

> Review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' stated targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no signature that quietly weakens the target? Specifically for Series 9, without building the code, run:

- **The coincidence check (§0.4), the sharpest on the positive side and the reason the series exists.** Unfold WS1's no-self-total-hold theorem. Is it a Cantor/Lawvere-shaped fixed-point contradiction (the self-total hold's defining equation has no solution, a diagonal term it cannot contain), genuinely INDEPENDENT of relational identity? Or does its proof, unfolded, route through bisimulation / "all states behaviorally identical," so no-self-total-hold COINCIDES with the Series 7/8 collapse? If the latter, the spine is **Coincident**, Series 8's wall re-hit, a SERIOUS finding, and the central repair failed (honestly reported, not buried).
- **The carrier-strength check (§0.5).** Is the carrier genuinely hold-reflexive (a hold ranges over the space of holds), or merely self-looping (`dest x ∋ x`, too weak to diagonalize, silently reducing to Series 8)? Is it `κ`-bounded (a consistent object where the diagonal is a genuine gap), or unrestrictedly self-ranging (Russell-paradoxical, no model)? Either failure is SERIOUS: the diagonal asserted not run, or run in an inconsistent theory.
- **The strip test on every payoff (§0.3).** Delete "self-reference"/"diagonal" from the plurality payoff; delete "re-diagonalization" from the forced-dynamics payoff; delete "blind spot" from the depth payoff; delete "self-total" from the spine; delete "residue" from the bound. Flag every payoff that survives stripping as a bare fixed-point / subsingleton / order / reachability fact, not an earned self-reference theorem.
- **The freeness verdict (WS2).** Is the residue proved *free* (not recoverable from the plain relating), or is it defined so it is trivially free / trivially recoverable? Confirm the residue's distinctness is derived from ONE position (no second position smuggled into the premise, the exact Series 8 circularity), tied to the Series 4/WS4 semantic import test.
- **The endogenous-order verdict (WS3).** Is the tower `≺` *derived* from re-diagonalization sequences, or an imported stage-index wearing the name "tower"? Is the forcing of dynamics ("a self-total hold being impossible forces successive re-inspection") a *theorem*, or an intuition asserted between two definitions?
- **The no-leaf verdict (WS3).** Confirm (NL): the residue is a full unheld face, `SHNE` preserved, never a bare relatum. A transient bare relatum anywhere is a SERIOUS finding (the constraint Series 7/8/9 all respect).
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open, e.g. WS2's plurality depending on WS1's diagonal being genuinely independent (not Coincident); WS4's depth depending on WS3's re-diagonalization genuinely opening new blind spots; WS5's monotonicity depending on WS3's order being genuinely endogenous. The batched review is the only place this is visible.
- **The coincidence rule** where it applies, PROMOTED to first-class at the spine: is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS1 no-self-total-hold vs. relational identity, the flagship; WS3 forced-dynamics vs. incompleteness; WS5 monotonicity vs. re-diagonalization.)
- **The monotonicity verdict, stated plainly.** Which of {Discharged, Refuted hypothesis, Partial} did the code deliver for monotonicity? Confirm it is one of these and is honestly labelled, never assumed-and-unstated.
- **The axiom-check status.** Was `#print axioms` actually run over every headline, or is the claim still static?

Write `spec/series-review-N.md`: findings graded SERIOUS (the verdict rests on it, a flagship payoff laundering, the spine Coincident, the carrier too weak/strong, monotonicity assumed-in), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed, no goalpost-moving: "relabel this / prove that / strip and re-prove / run the kill condition / re-report Coincident honestly," never "lower the bar."

If there is a serious finding, continue to Phase E. If not, conclude with Phase F.

### Phase E — Address `spec/series-review-N.md` (one session)

**Prompt to seed the address session:**

> Please pull your branch, review the most recent `spec/series-review-N.md` file, and address every finding. **Attempt the charter-strength theorem first**; where it provably resists, deliver an honest Partial/Impossibility/Refuted/Coincident with the obstruction precise. Many corrections will be *relabels, not fixes* (a payoff shown to be a bare order fact is renamed and demoted; a monotonicity "proof" shown to unfold to its definition is demoted to refuted or assumed and the "ever-deepening self" retracted; a spine shown to unfold to bisimulation is demoted to Coincident and the Series 8 wall re-reported), and that is a correct outcome, not a failure. Record every change in `charter-status.md` (the series-review log and the affected workstream rows); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

### Phase F — Close (one session)

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 9 closes. Write `summary.md`, `summary-technical.md`, and update the root `README.md` to reflect the findings (a new row in the series table). The final `spec/series-review-N.md` and `charter-status.md` become the seed of Series 10.

---

## 3. Why the review is batched at series level (not per workstream)

Series 4 reviewed per workstream and caught most gaps, but its sharpest findings came from its end-of-series adversarial review, which saw all workstreams at once. Series 5, 6, and 8 promoted the whole-series blind review to the primary vehicle because their payoffs were meant to be consequences of a single fact. Series 9's payoffs are just as tightly coupled: plurality, dynamics, and depth are all meant to be consequences of one fact (no self-total hold), so a payoff can look earned in its own file while secretly being the shared collapse relabelled, the order painted on, monotonicity assumed, or, the Series 9 signature risk, the spine Coincident with relational identity. Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it: the reviewer sees the whole dependency graph and can trace a "discharged" payoff to the open obligation in another file that actually carries it, and can trace the spine's independence claim through to whether the proof term is genuinely diagonal.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude, a stated limitation, not claimed independence. The objective anchors, the dependency graph, the `#print axioms` records, the strip-test results, the coincidence-check unfolding (is the spine diagonal or bisimulation), the carrier-strength check, and WS7's freeness/monotonicity ledger, are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 9:

- **WS1 is blocking.** The gate is the diagonal spine: no hold contains its own complete content, proved independent of relational identity. Nothing downstream is sound until this lands, because it is what makes the residue *free* and what repairs Series 8's coincidence. WS1 also fixes the hold-reflexive carrier and the hold primitive, ambient for all.
- **WS2 depends on WS1's diagonal.** The residue breaks the collapse only if it is free, not recoverable, and only if the spine is genuinely independent (not Coincident); WS1 secures both. WS2's plurality is stated with the diagonal's independence as a hypothesis until WS1 discharges it.
- **WS3 supplies the engine the rest consume.** The re-diagonalization map (WS3) is what WS4's depth and WS5's monotonicity run on. Build WS3's map and discharge (NL)+(NF) before closing WS4-WS5. WS3 also derives the tower order endogenously, a forward dependency for anything time-shaped.
- **WS4 consumes WS3.** Depth/tower needs the re-diagonalization map; reachability-into-depth needs the order.
- **WS5 owns the monotonicity fork and consumes WS3.** Monotonicity is a claim *about* re-diagonalization; it cannot be attempted until the map exists, and it must never be folded into the map. WS5 runs the kill condition and reports Discharged / Refuted / Partial.
- **WS6 (heuristic ceiling)** reports the universal forms of WS4 (depth) and WS5 (monotonicity) where they exceed what is rangeable, and, if the spine is Partial-on-a-witness, the universal carrier claim.
- **WS7 runs last.** It audits all others, unfolds the coincidence risk (spine diagonal vs. bisimulation) and monotonicity-by-fiat risk and carrier-strength, and aggregates the strip-test and freeness/monotonicity ledger; it cannot report until WS1-WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback, then propagated forward.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria | designs' motivating prose; charter's metaphysical framing (no "self is a paradox," no "self-reference is the engine") |
| Address (Phase E) | `spec/series-review-N.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level, plus, for Series 9, **unfold the no-self-total-hold proof and check it is a diagonal fixed-point contradiction, not a bisimulation**, and **check the carrier is genuinely hold-reflexive and `κ`-bounded**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series, the next series' plan

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 9 closes. The final `spec/series-review-N.md` and `charter-status.md` become the **seed of Series 10**, following the program's inter-series discipline:

> **Each series is a response to the previous series' honest findings, not a continuation of its plan.**

The pattern (Series 1 → 2 → ... → 9): each series takes the place the mathematics pushed back hardest in the prior series and makes *that* its question. Series 8's hardest pushback was that no-god's-eye coincided with relational identity; Series 9's response is the diagonal. Whatever Series 9's final review surfaces as its hardest resistance becomes Series 10's question. The charter forecasts three candidates: if the diagonal spine comes back **Coincident** (re-hits the Series 8 wall at greater depth), Series 10 inherits the deepest form of the monism question, whether no-self-total-hold is EVER separable from relational identity or the two are provably the same fact, which would be a profound negative result about the program's whole ambition. If monotonicity is **refuted**, Series 10's question is likely "what bounds the proliferating many if not a growing residue." If the diagonal lands independent but only on a witness (**Partial**), Series 10 inherits the universality question, whether every hold-reflexive carrier diagonalizes.

The mechanics, unchanged:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone**, its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again, design-all, build-all, then the review→address loop.

---

*Protocol for Series 9. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and, once written, `spec/wsNN-design.md` (the per-workstream contracts) and `spec/series-review-N.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `spec/series-review-N.md`. The whole-series blind review is the primary vehicle, and Series 9 sharpens it with two checks, because the series stands or falls on whether the diagonal spine is genuinely a fixed-point contradiction independent of relational identity (the coincidence check, the repair of Series 8) and whether the carrier is genuinely hold-reflexive and consistent (the carrier-strength check, the battlefield the diagonal is fought on). No em dashes in final academic paper copy; this working protocol is not final copy.*
