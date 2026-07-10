# Relational Existentialism — Series 5 Protocol

**The process. Series 5 keeps Series 4's one load-bearing idea — blind review has teeth only when the reviewer cannot see the motivation — but changes the *unit of batching*: instead of looping design→build→review per workstream, Series 5 runs each phase once across the whole series. One session designs all seven workstreams; one code session builds them all; then review and code sessions alternate at the whole-series level, mediated by a `series-review.md` document.**

*Series 3 ran a seven-phase cycle per proof obligation. Series 4 collapsed that to five steps per workstream with a per-workstream review→build loop. Series 5 collapses it further along a different axis: the phases are the same (design, build, blind review, address), but each runs **once over all seven workstreams together**, because the workstreams are tightly coupled (the tower is one object; the payoffs share the double-unboundedness fact) and reviewing them in isolation would miss exactly the cross-workstream laundering the audit exists to catch.*

---

## 0. Core principle

Two things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code and the design contracts (theorem signatures, outcome classes) and the charter's success criteria, but **not** the charter's motivating prose — no "stratification as boundlessness," no "grain not wall," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Trivialized** for WS7) with the obstruction made precise and routed — never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss.

A third, sharpened for Series 5:

3. **Strip the *why*, keep the *what* — and strip the *word*, keep the *theorem*.** Beyond the session-level blindness rule, Series 5 carries a statement-level one inherited from Series 4's adversarial review: for every payoff, delete "face" / "view" / "level" from the statement and check whether it still goes through as a bare index or cardinality fact. A payoff that survives the strip is an index fact honestly flagged; a payoff that needs the deleted structure is earned. This strip test is written into the designs (WS3/WS4/WS6) and aggregated by WS7; the reviewer runs it.

---

## 1. The documents

- **`charter.md` — the design (stable).** The question, the two collapses, the false repairs, the doubly-unbounded repair, the seven workstreams, success criteria, honest risks. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md` — the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, deliverable. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md` — the design index.** Ties the seven together: the shared ambient-theory choice, the cross-workstream triage summary, the predicted headline.
- **`charter-status.md` — the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the closed log, the series-review log. Where change lives.
- **`series-review.md` — the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it. This is the Series 5 analogue of Series 4's `project-review-N.md`, but it is the *primary* review vehicle rather than an end-of-series capstone (see §3).

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

The user's batching, stated as the session plan:

> One session to create all the designs (Phase B); one code session to build them all (Phase C); one session to review and write `series-review.md` (Phase D); the code session to address that doc (Phase E); another review (Phase D again); another code pass (Phase E again).

So the canonical Series 5 run is: **B → C → D → E → D → E** (two review passes, three code touches counting the initial build), with more D→E loops added only if a review pass still returns SERIOUS findings.

### Phase A — Charter (once)

Write `charter.md`: the question, the commitments, the framework, the workstreams, the success criteria and outcome vocabulary, the honest risks. Done. (Series 5's charter is written; this protocol and `charter-status.md` are its companions.)

### Phase B — Design all seven (one session, with context)

In a single session with the charter and repo in view, write all of `spec/ws01-design.md … ws07-design.md` plus `spec/README.md`. The repo is in view so designs reference real, reusable machinery *by name* — and, because Series 5 is standalone, name the Series 4/3 theorems that will be **transcribed** (not imported): `PkObj`, `Coalg`, `bisim_eq`, `νLk`, `lcomp`, `carrier_card_ge`, `ws2_collapse`, `ws3_faces_never_annihilate`, `ws4_no_top_cardinal`, `ws5_global_groundless_collapses`, `ws3_no_distributive_law`, `ProgramVerdict`, and so on. Every design must contain:

- **3–7 candidate framings** of the obligation — different ways to cash out the commitment as something provable — each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (ZFC/AFA encoding, functor `F`, monad `T`, distributive law `λ` if relevant), the success condition, and the explicit failure mode (collapse / non-existence / no-distributive-law / non-convergence).
- **A paper-decidable triage** per candidate — a check runnable by inspection before writing Lean — **collapsed into a table**, with the framing choice *downstream* of the triage, not a substitute for it.
- **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on imported (transcribed) upstream theorems.
- **Outcome classes** (Discharged / Impossibility / Partial / Failed / — WS7 — Trivialized) with pre-registered honest alternatives, and the **strip-test annotation** per payoff.

Designs are written together so cross-workstream dependencies (§4) are settled in one coherent pass rather than negotiated across sessions. Once the batch is committed, the designs are the stable contracts for the build.

### Phase C — Build all seven (one session, with repo context)

In a single session, realize every design in `formal/wsNN.lean`, building `Series5.lean` and `AxiomCheck.lean`, self-contained (transcribe Series 4/3 machinery; import nothing from `series-4/` or `archive/`). Respect the dependency order (§4): WS1 first (blocking), then WS2, then WS3–WS6, then WS7. The build produces theorems (or precise impossibilities) matching the designs' signatures. Please update `charter-status.md` as you go.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (it is the same session's artifact) or report the workstream Partial with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield.

Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS6 needing a uniform `F_∞` that WS1's `destInf` does not provide) is handled by the pre-registered fallback in the affected design (WS1's colimit-functor escalation), not by an ad hoc patch — the designs anticipate their own escalations precisely so the batched build does not stall.

### Phase D — Blind series-review (one session) → `series-review.md`

In a fresh session:

Can you clone this repo and read the series 5 charter, charter status, design documents, and lean files? Please view the series 5 working branch.
[colleen-love/relational-existentialism: A view of the universe](https://github.com/colleen-love/relational-existentialism)

Once you are finished, please do an adversarial review of the formalization. 

Please answer, adversarially and across the whole series at once: does the code prove these theorems; do the theorems meet the designs' stated targets; do they satisfy the charter criteria they claim — with no `sorry`, no custom axiom, no signature that quietly weakens the target? Specifically for Series 5, please run:

* The strip test on every payoff (§0.3): does no-top still go through with "no last level" deleted? does no-completing-view still go through with "face" deleted? Flag every payoff that survives stripping as an index/cardinality fact, not an earned carrier theorem — exactly the S1/S2 findings that reshaped Series 4.
* Cross-workstream laundering — a claim discharged in isolation that leans on a hypothesis another workstream left open (e.g. WS4's V3 depending on WS6's cross-level face; WS2's no-first-level depending on WS6's descending map). The batched review is the only place this is visible.
* The coincidence rule where it applies — is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS3 `ws3_wall_vs_grain`, WS6 `ws6_relating_is_composition`, WS6 `ws6_unknowable_eq_noview`.)
* The trivialization verdict — do the payoffs reduce to distinct consequences of double-unboundedness (WS7's distinctness ledger) or collapse into one definition? Confirm or refute Trivialized at the whole-program level.
* The axiom-check status — was `#print axioms` actually run, or is the claim still static?

Please write a `series-review.md`: findings graded SERIOUS (the verdict rests on it — e.g. a flagship payoff laundering), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed — no goalpost-moving: the review says "relabel this / prove that / strip and re-prove," never "lower the bar."

### Phase E — Address `series-review.md` (one session)

In a code session with `series-review.md`, all code, and all designs in view, address every finding. Following Series 4's discipline: **attempt the charter-strength theorem first**; where it provably resists, deliver an honest Partial/Impossibility with the obstruction precise. Many corrections will be *relabels, not fixes* (a payoff shown to be an index fact is renamed and demoted from the payoff list, as Series 4's `ws4_no_top_endogenous → ws4_no_top_reach`), and that is a correct outcome, not a failure. Record every change in `charter-status.md` (the series-review log and the affected workstream rows); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

Then loop back to Phase D for another blind pass, which regenerates `series-review.md` against the addressed build. Exit when a review pass returns no SERIOUS findings and the remaining REAL items are correctly-labelled terminal Partials/Impossibilities — **not** "the build finally passes at charter strength." Do not grind a genuine impossibility against the review; report it.

---

## 3. Why the review is batched at series level (not per workstream)

Series 4 reviewed per workstream and caught most gaps, but its *sharpest* findings (S1: the verdict imports the cardinal fiat; S2: the endogenous wall is a reachability wall with faces painted on) came from its **end-of-series adversarial project review**, which saw all workstreams at once. Series 5's payoffs are even more tightly coupled — they are meant to be consequences of a single fact (double-unboundedness) — so the laundering risk is *specifically* cross-workstream: a payoff can look earned in its own file while secretly being the shared index fact relabelled. Reviewing the whole series at once, blind, is the only configuration that surfaces this. So Series 5 promotes the whole-series blind review from an end-of-series capstone to **the primary review vehicle**, run every pass, writing `series-review.md`.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it — the reviewer sees the whole dependency graph and can trace a "discharged" payoff to the open obligation in another file that actually carries it.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude — a stated limitation, not claimed independence. The objective anchors — the dependency graph, the `#print axioms` records, the strip-test results, and WS7's distinctness ledger — are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 5:

- **WS1 is blocking.** The colimit gate is existential; nothing downstream is sound until `W_∞` is shown to carry a coalgebra with bisimulation-is-identity (or the amalgamation is redirected). Built and reviewed first.
- **WS2 fixes the index the whole tower uses.** `ℤ` (no least/greatest/self-dual) and the unbounded cardinals feed WS3 (no-global-cap), WS4 (poles, unboundedness), and WS6 (floor-free grade). WS2's Explosion Dilemma horns are transcribed Series 4 theorems and must be in place before the forced answer.
- **WS3 and WS4 consume WS1 + WS2.** No-top (WS3) needs the colimit and the unbounded cardinals; groundless-no-collapse and the poles (WS4) need the index facts.
- **WS4's V3 has a forward dependency on WS6.** The genuine no-view (`ws4_no_completing_view`) needs WS6's cross-level face. Build WS6's graded face before closing WS4's no-view; until then WS4's V3 is stated with the WS6 face as a hypothesis. The batched build is what makes this forward edge tractable — both files are open in the same session.
- **WS2's no-first-level has a forward dependency on WS6.** `ws2_no_atom_floor` needs WS6's descending cross-level map to be earned rather than posited.
- **WS6 is the deepest.** Leak-free transport and the graded weak distributive law both hinge on the grade being an inert `ℤ`-label (GF1); its fallback (functorial grade GF2) and WS1's colimit-functor fallback are the pre-registered escalations.
- **WS7 runs last.** It audits all others and aggregates the strip-test ledger; it cannot report until WS1–WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. This is the one strict place: **upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback, then propagated forward — not deferred to a later loop.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria | designs' motivating prose; charter's metaphysical framing |
| Address (Phase E) | `series-review.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series — the next series' plan

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 5 closes. The final `series-review.md` and `charter-status.md` become the **seed of Series 6**, following the program's inter-series discipline:

> **Each series is a response to the previous series' honest findings — not a continuation of its plan.**

The pattern (Series 1 → 2 → 3 → 4 → 5): each series takes the place the mathematics pushed back hardest in the prior series and makes *that* its question. Series 4's hardest pushback was that boundedness/positioning could not be made endogenous on one carrier (faces tame quality, not branching); Series 5 is the response — relocate the bound between levels. Whatever Series 5's final review surfaces as its hardest resistance — the design forecasts it will be the trivialization tail (attention Trivialized; the reduction to one fact only partial; the poles a mere index fact) — becomes Series 6's question.

The mechanics, unchanged from Series 4:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone** — its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again — design-all, build-all, then the review→address loop.

---

*Protocol for Series 5. Companion to `charter.md` (the design), `spec/wsNN-design.md` (the per-workstream contracts), `charter-status.md` (the ledger), and `series-review.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `series-review.md`. The whole-series blind review is the primary vehicle, promoted from Series 4's end-of-series capstone because Series 5's payoffs are cross-workstream-coupled and that is where laundering hides. No em dashes in final academic paper copy; this working protocol is not final copy.*
