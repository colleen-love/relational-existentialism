# Relational Existentialism — Series 10 Protocol

**The process. Series 10 keeps the program's one load-bearing idea, that blind review has teeth only when the reviewer cannot see the motivation, and keeps the Series 5/6/8/9 batching: each phase runs once across the whole series, because the workstreams are one coupled object. The whole series stands on a single claim, that reification of a relation into a relatum, made genuine by the incompletability of self-reference, grows the world into a plurality that cannot close, and that claim is only checkable across all the workstreams together.**

*Series 3 ran a seven-phase cycle per proof obligation. Series 4 collapsed that to five steps per workstream. Series 5, 6, 8, and 9 collapsed it further: the same phases (design, build, blind review, address), each run once over all seven workstreams together. Series 10 inherits the Series 9 shape unchanged. The coupling is at least as tight: the whole series stands on the claim that one fact (a reified self-relation is free, because self-reference cannot close) drives genuine growth, the breaking of the collapse, and the no-closing-top dichotomy at once, and that is only checkable across all workstreams together. Series 10 is the program's founding equation `Ω ≅ F(Ω)` read as a generator, and it is the response to Series 9's honest limitation: a moving hole is still one hole.*

---

## 0. Core principle

Four things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria, but **not** the charter's motivating prose. No "to relate is to create," no "the growing self," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal, and reach for the pre-registered failure BEFORE the compiler.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Refuted hypothesis**, or **Bookkeeping**, or **Circular** for WS7) with the obstruction made precise and routed, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss. **This is the sin that recurs (the Series 8 lesson, §2a below): across three review passes, the Series 8 spine finding S1 was "addressed" each time by building a new, cheaper theorem that established the antecedent of the charter's own pre-registered Failed condition and then labelled the result a success, instead of simply reporting the Failed/Partial the charter had already anticipated. The loop stopped only when pass 3 did what pass 1 already directed. The charter's pre-registered failure outcomes (the Failed rows, the kill conditions, the "monism wins / Partial" clauses) are HONORABLE FIRST MOVES, not last resorts after three coats of paint. When a finding shows a pre-registered failure condition has been met, reporting it is the correct action, and constructing a theorem that avoids it is the §0.2 sin.**

**2a. The recurrence guard (the Series 8 anti-loop discipline), applied at both Phase D and Phase E.** A SERIOUS finding closes in exactly ONE of two ways, and `charter-status.md` must name which: **(Fixed)** the charter/design's *originally specified* target was built (name the theorem), or **(Relabeled)** the target was not built, the precise obstruction is recorded, and the payoff's status is demoted to the pre-registered honest outcome (Partial / Failed / Refuted / Bookkeeping). "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is NEITHER, and is prohibited: it is precisely the move that let S1 recur. Findings carry stable IDs across passes; a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count. Series 9 is the positive model: F-8 was Fixed (the map genuinely strengthened to the specified target, consequences re-proved) and F-1 was Relabeled with a real reason (the design's richness bar was cardinality-impossible, named, demoted) — two honest closures, no recurrence.
3. **Strip the *why*, keep the *what*, and strip the *word*, keep the *theorem*.** Beyond session-level blindness, Series 10 carries the statement-level strip test. For every payoff, delete the structural term, **"reification," "relatum," "growth," "tower," "fold," "productive," "blindness," "self-relation"**, and check whether the statement still goes through as a bare freeness, bisimulation-embedding, order, or fixed-point fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. The strip test is written into the WS1-WS5 designs and aggregated by WS7; the reviewer runs it.

Series 10 adds two emphases of its own, because its signature risks are the two central findings of the two prior series, inherited and relocated:

4. **Growth must be strict and internal, NOT bookkeeping (Series 9's moving hole re-hit is the first cardinal sin).** The whole repair of Series 9 rests on reification GROWING the carrier, not recording a longer history beside a fixed one. This is the exact trap Series 9 hit one level down (the residue moved but the field was fixed; series-9 F-8 flagged the accumulation living in an external `List`). The review must, for WS2 specifically, confirm `Ω_{α+1}` does NOT bisimulation-embed into `Ω_α`, i.e. the reified relatum is genuinely absent from the prior carrier, so growth is a bigger world and not a longer list. A "tower" that is constant up to bisimulation while a `List` lengthens is **Bookkeeping** and a SERIOUS finding: Series 9's moving hole re-hit at the carrier level while the prose claims a growing world. This check is PROMOTED to first-class.
5. **The bound must be endogenous-or-explicitly-scaffolding, NEVER κ-by-fiat (the second cardinal sin, Series 8's conservation relocated).** Series 10 uses a κ-bound as scaffolding, and this is honest ONLY if no result relies on κ being small and any "self-bounding" claim is measured as REFLEXIVITY, not as staying-under-κ. This is the exact trap Series 8 wrote a kill condition against (conservation baked in by fiat), relocated to the carrier boundary: a "fold" that unfolds to "the tower stayed under the κ we imposed" is the bound assumed, not shown. The review must, for WS4/WS5 specifically, confirm the fold predicate is distributed reflexivity (an endogenous fact about each stage folding back into range) and NOT a cardinality bound, and confirm every theorem holds for all sufficiently large κ (the large-κ discipline). A self-bounding claim resting on small κ is **κ-by-fiat** and a SERIOUS finding: the endogenous bound smuggled while the charter defers it to Series 11. This check is PROMOTED to first-class.

---

## 1. The documents

- **`charter.md`, the design (stable).** The question, the Series 9 moving-hole limitation it responds to, reification as generator, productive blindness, the three consequences, the false escapes (import/leaf/bookkeeping/κ-by-fiat/trivial-closure), the fold-vs-fatal fork with its kill condition, the seven workstreams, success criteria, honest risks, and the explicit deferral of the endogenous bound to Series 11. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md`, the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, strip-test annotation. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md`, the design index.** Ties the seven together: the shared carrier choice (the reifying κ-bounded carrier, fixed once in WS1 and consumed by all), the primitive decision (the hold and the diagonal from Series 9, plus `reify : F(Ω) → Ω`, charter §3), the cross-workstream triage summary, the predicted headline.
- **`charter-status.md`, the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the fold fork's running status, the closed log, the series-review log. Where change lives.
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

Write `charter.md`: the question, the Series 9 moving-hole limitation, reification as generator and productive blindness, the three consequences, the false escapes, the fold-vs-fatal fork and kill condition, the workstreams, success criteria and outcome vocabulary, honest risks, the Series 11 deferral of the endogenous bound. **Done** — Series 10's charter is written; this protocol and `charter-status.md` are its companions.

### Phase B — Design all seven (one session, with context)

**Prompt to seed the design session:**

> You are writing all seven per-workstream design docs for Series 10 in one session, with `charter.md` and the repository in view. Series 10 is standalone but transcribes (does not import) machinery from Series 9, 8, 7, and 4. Name the theorems to be transcribed: the κ-bounded functor and carrier (`PkObj κ`, `PkMap`, `dest`), reaching and hereditary non-emptiness (`SReaches`, `SHNE`), bisimulation and behavioral identity (`IsBisim`, `BehaviorallyIdentified`), the collapse engine (`hneRel_isBisim` and the atomless-bisimulation), the hold and its face, the recoverability/free import test (`Recoverable`/`plainOf`, from Series 4 via Series 9 WS2), and above all the diagonal spine (`ws1_no_self_total_hold`), its independence certificate (`ws1_diagonal_not_bisim`), and the free residue (`ws2_residue_free`, `ws2_residue_is_import`). Every design must contain:
>
> - **3 to 7 candidate framings** of the obligation, each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (the reifying carrier home; the functor; `reify : F(Ω) → Ω`; the ordinal-indexed tower; the tower order from reification sequences; the fold/reflexivity predicate), the success condition, and the explicit failure mode (bookkeeping / κ-by-fiat / import / leaf / trivial-closure-both-directions / non-well-founded-tower).
> - **A paper-decidable triage** per candidate, a check runnable by inspection before writing Lean, collapsed into a table, with the framing choice downstream of the triage.
> - **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems.
> - **Outcome classes** (Discharged / Discharged-on-scaffold / Impossibility / Partial / Refuted hypothesis / Bookkeeping / Failed / — WS7 — Circular) with pre-registered honest alternatives, and the **strip-test annotation** per payoff (which structural word, deleted, would be the test).

Two Series-10-specific design duties, settled in this batch:

- **`reify : F(Ω) → Ω` is defined once (WS1) and is ambient for all.** The forward map of `Ω ≅ F(Ω)`, κ-bounded so the adjoined relatum stays in `PkObj κ`, strong enough to genuinely grow the carrier (§0.4, not bookkeeping) yet consistent with the diagonal (§4.5, no closing top). Whichever concrete `reify` and carrier WS1 picks becomes the setting WS2-WS6 are written against. Do not let two workstreams assume different reification maps.
- **The tower order `≺` is derived once (WS3) from reification sequences and its endogeneity is the theorem.** The relation "`α ≺ β` iff `Ω_β` is reached by reifications from `Ω_α`" must be a single definite order that WS3 (the tower) and WS4 (close-or-fold) both consume; the imported-ordinal branch is designed in as a pre-registered *failure* mode to be refuted, not a fallback.

### Phase C — Build all seven (one session, with repo context)

**Prompt to seed the build session:**

> Realize every Series 10 design in `formal/Series10/wsNN.lean`, building `Series10.lean` and `AxiomCheck.lean`, self-contained: transcribe Series 9/8/7/4 machinery, import nothing from `series-9/`, `series-8/`, `series-7/`, `archive/`. Respect the dependency order (§4): WS1 first (blocking, the reifying carrier + productive blindness + `reify`), then WS2, then WS3 (the tower), then WS4-WS6, then WS7. The build produces theorems (or precise impossibilities, or a refuted crown reported FATAL, or an honest Bookkeeping payoff) matching the designs' signatures. Update `charter-status.md` as you go. Sorry-free and axiom-clean or it is not done.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial (or Bookkeeping, for the payoff) with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield. Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS3 needing `reify` to expose the tower as a first-class ordinal-indexed object WS1 did not provide) is handled by the pre-registered fallback in the affected design, not by an ad hoc patch.

The first incremental build takes longer than two minutes. Please run it as a background task at the start of the session.

**The first file is WS3's reification tower** in spirit even though WS1 builds first: WS1 establishes the reifying carrier, `reify`, and productive blindness; but the object the whole of Series 10 turns on is the tower (charter §3), and its two obligations, **(NL)** no leaf and the **endogenous order**, should be discharged early as the seed. **The fold (crown) is NOT attempted in the build until WS5**, and is never built into `reify` or the tower construction.

**The two most important build checks (Series 10's reasons to exist):**
1. When WS2's growth theorem is built, confirm it proves `Ω_{α+1}` does NOT bisimulation-embed into `Ω_α`. If growth is only a lengthening `List` while the carrier is bisimulation-constant, the payoff is **Bookkeeping**, Series 9's moving hole is re-hit at the carrier level, and that must be recorded honestly in `charter-status.md`, not papered over.
2. When WS4/WS5's fold is built, confirm the fold predicate is distributed reflexivity and every theorem holds for all sufficiently large κ. If "self-bounding" rests on small κ, it is **κ-by-fiat**, Series 8's conservation sin relocated, and must be recorded honestly. The endogenous bound is Series 11's; Series 10 must not claim it.

### Phase D — Blind series-review (one session) → `spec/series-review-N.md`

**Prompt to seed the blind review session:**

> Please clone https://github.com/colleen-love/relational-existentialism and view the series 10 working branch.

> Review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no signature that quietly weakens the target? Specifically for Series 10, without building the code, run:

- **The bookkeeping check (§0.4), the sharpest on the payoff side and the reason the series exists.** Unfold WS2's growth theorem. Does it prove `Ω_{α+1}` does NOT bisimulation-embed into `Ω_α` (genuine strict internal growth, a bigger world)? Or does "growth" reduce to a lengthening external `List`/index while the carrier is constant up to bisimulation (Series 9's moving hole re-hit)? If the latter, the payoff is **Bookkeeping**, a SERIOUS finding, and the central repair failed (honestly reported, not buried).
- **The κ-by-fiat check (§0.5).** Is the fold predicate distributed REFLEXIVITY (an endogenous fact), or does "self-bounding"/"fold" unfold to "the tower stayed under the imposed κ" (cardinality-by-fiat)? Do all theorems hold for all sufficiently large κ (the large-κ discipline), or does a result rely on κ being small? A self-bounding claim resting on small κ is **κ-by-fiat**, a SERIOUS finding, Series 8's conservation sin relocated. Confirm the endogenous bound is NOT claimed (it is Series 11's).
- **The strip test on every payoff (§0.3).** Delete "reification" from the productive-blindness payoff; delete "growth"/"tower" from the strict-growth payoff; delete "fold" from the bound; delete "self-relation" from the free-relatum. Flag every payoff that survives stripping as a bare freeness / bisim-embedding / order / fixed-point fact, not an earned reification theorem.
- **The productive-blindness verdict (WS1).** Is free reification proved to route THROUGH the diagonal (`ws1_no_self_total_hold` / `ws2_residue_free`), so the reified relatum is free BECAUSE self-reference cannot close? Or is freeness asserted by a fresh assumption independent of the diagonal (which would make productive blindness a stipulation, not a consequence)? Confirm the reified relatum's freeness reconstructs-a-self-total-hold-if-recoverable, tying it to the Series 4/Series 9 import test.
- **The CLOSE-forbidden verdict (WS4).** Is CLOSE (a totality-relatum) proved forbidden by the diagonal (a totality-relatum is self-total, `ws1_no_self_total_hold`), as an Impossibility? Or is no-closing-top asserted / built into `reify` by a definitional clause? If the tower is exhibited closing, is that correctly reported as a `reify` design defect (a smuggled self-total hold), NOT as monism re-derived?
- **The endogenous-order verdict (WS3).** Is the tower `≺` derived from reification sequences, or an imported ordinal clock wearing the name "tower"? Is the well-foundedness of the tower a theorem (each stage a genuine object), or asserted?
- **The no-leaf verdict (WS3).** Confirm (NL): reification preserves `SHNE`, the reified relation is a full relatum with its own relating, never a bare point. A reified leaf anywhere is a SERIOUS finding (the constraint the whole program respects since Series 7).
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open, e.g. WS2's strict growth depending on WS1's freeness being genuine (not a fresh assumption); WS4's CLOSE-forbidden depending on the tower's totality-relatum genuinely being a self-total hold; WS5's fold depending on WS3's order being genuinely endogenous. The batched review is the only place this is visible.
- **The coincidence rule** where it applies: is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS1 productive-blindness vs. the diagonal, which SHOULD route through it — here the check is that it genuinely does, not that it is independent; WS4 CLOSE-forbidden vs. self-totality; WS5 fold vs. the tower construction.)
- **The fold verdict, stated plainly.** Which of {Discharged-on-scaffold, FATAL/refuted, Partial} did the code deliver for the fold? Confirm it is one of these, is honestly labelled, never assumed, never resting on small κ.
- **The axiom-check status.** Was `#print axioms` actually run over every headline, or is the claim still static?

**On the second and later passes, run the recurrence check FIRST, before the ten checks above (§0.2a, the Series 8 anti-loop discipline).** This pass receives the prior `spec/series-review-{N-1}.md`. For every finding it graded SERIOUS, determine how Phase E closed it by unfolding the actual proof term, not by trusting `charter-status.md`'s prose or Phase E's self-assessment: was the charter/design's *originally specified* target BUILT (name the theorem, confirm it is that target and not an adjacent weaker one), or was the finding RELABELED to a pre-registered honest outcome (Partial/Failed/Refuted/Bookkeeping) with a precise obstruction? A finding "addressed" by a new theorem that establishes the antecedent of a pre-registered failure clause and labels the result a success, or by any target-adjacent theorem that leaves the specified target unbuilt while claiming closure, is **re-graded SERIOUS and marked RECURRING (pass count N)**. This is exactly the Series 8 S1 pattern: three passes, each "addressing" the spine finding by narrowing the object until a cheaper theorem compiled, none building the specified C3 target, until pass 3 finally reported the Partial pass 1 had already directed. Name any recurrence explicitly; a finding on its second recurrence is a signal the *charter's* pre-registered failure outcome is the honest terminus and Phase E should report it, not attempt a fourth theorem.

Write `spec/series-review-N.md`: findings graded SERIOUS (the verdict rests on it, a flagship payoff laundering, growth is Bookkeeping, the bound is κ-by-fiat, `reify` smuggles a self-total hold, **or a prior SERIOUS finding RECURRING via a target-avoiding closure**), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed, no goalpost-moving: "relabel this / prove that / strip and re-prove / run the kill condition / report Bookkeeping or FATAL honestly," never "lower the bar." For a RECURRING finding, the correction owed is stated as the binary: "build the specified target [name it], OR report the pre-registered [Partial/Failed/Refuted] — no third theorem."

If there is a serious finding, continue to Phase E. If not, conclude with Phase F.

### Phase E — Address `spec/series-review-N.md` (one session)

**Prompt to seed the address session:**

> Please pull your branch, review the most recent `spec/series-review-N.md` file, and address every finding. For each SERIOUS finding, run this sequence in order, and do not skip to building a theorem until you have done the first two steps:
>
> 1. **Locate the charter's pre-registered honest-failure outcome for the owning workstream** — the Failed row, the kill condition, the Partial/Bookkeeping/Refuted/FATAL clause, the "monism wins" branch. It is written into the charter §5 and §8 precisely so that falling short is an honorable, anticipated move. Read it before anything else.
> 2. **Ask whether the finding shows that condition has been met.** If the finding demonstrates that the specified target provably resists, or that the pre-registered failure antecedent now holds, then **REPORT it** (demote the payoff to Partial/Failed/Refuted/Bookkeeping, retract the overclaim, record the obstruction). Constructing a new theorem that establishes the antecedent of a pre-registered failure clause and labels the result a success is the §0.2 sin and is exactly how the Series 8 spine finding recurred across three passes. Do not do it.
> 3. **Only if the pre-registered failure has NOT been met, attempt the charter/design's originally-specified target** (name it; it is in the design doc, e.g. the C-numbered construction). Build *that* target, not an adjacent weaker theorem that happens to compile.
>
> Then close each SERIOUS finding in **exactly one of two ways, and state which in `charter-status.md`**:
> - **(Fixed)** the originally-specified target was built — name the theorem and confirm by unfolding that it is that target; or
> - **(Relabeled to Partial/Failed/Refuted/Bookkeeping)** the target was not built — record the precise obstruction (a real reason, as Series 9's F-1 recorded the cardinality impossibility) and demote the payoff's status accordingly.
>
> "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is neither and is prohibited — it is the move that let Series 8's S1 survive two extra passes. Many correct closures will be **Relabels, not Fixes** (a "growth" shown to be a lengthening list is demoted to Bookkeeping and the strict-growth claim retracted; a "fold" shown to rest on small κ is demoted to κ-by-fiat and the self-bounding claim retracted; a `reify` shown to close the tower is reported as a design defect, a smuggled self-total hold, not as monism), and a Relabel to a pre-registered outcome is a SUCCESS, not a failure. If the finding is RECURRING (marked so by the prior pass), the only two permitted actions are Fixed-by-building-the-named-target or Relabeled-to-the-pre-registered-outcome; a third adjacent theorem is forbidden. Record every change in `charter-status.md` (the series-review log and the affected workstream rows, noting Fixed vs Relabeled per finding); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

### Phase F — Close (one session)

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 10 closes. Write `summary.md`, `summary-technical.md`, and update the root `README.md` to reflect the findings (a new row in the series table). The final `spec/series-review-N.md` and `charter-status.md` become the seed of Series 11, which inherits the κ-removal and the finiteness-of-attention unification (charter §10, WS6).

---

## 3. Why the review is batched at series level (not per workstream)

Series 4 reviewed per workstream and caught most gaps, but its sharpest findings came from its end-of-series adversarial review, which saw all workstreams at once. Series 5, 6, 8, and 9 promoted the whole-series blind review to the primary vehicle because their payoffs were meant to be consequences of a single fact. Series 10's payoffs are just as tightly coupled: genuine growth, the breaking of the collapse, and the no-closing-top dichotomy are all meant to be consequences of one fact (a reified self-relation is free because self-reference cannot close), so a payoff can look earned in its own file while secretly being a lengthening list (Bookkeeping), a cardinality bound (κ-by-fiat), or a `reify` that smuggled a self-total hold. Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it: the reviewer sees the whole dependency graph and can trace a "discharged" growth to the open obligation in another file that actually carries it, and can trace the fold's endogeneity through to whether it is reflexivity or a cardinality artifact.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude, a stated limitation, not claimed independence. The objective anchors, the dependency graph, the `#print axioms` records, the strip-test results, the bookkeeping check (bisim-embedding), the κ-by-fiat check (large-κ discipline + reflexivity), and WS7's freeness/growth/fold ledger, are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 10:

- **WS1 is blocking.** The gate is productive blindness: a reified self-relation is free, routing through the diagonal. Nothing downstream is sound until this lands, because it is what makes the growth genuine (not bookkeeping) and CLOSE forbidden. WS1 also fixes `reify` and the reifying carrier, ambient for all.
- **WS2 depends on WS1's freeness.** Strict internal growth holds only if the reified relatum is genuinely free (not recoverable); WS1 secures it. WS2's growth is stated with freeness as a hypothesis until WS1 discharges it.
- **WS3 supplies the tower the rest consume.** The reification tower (WS3) is what WS4's close-or-fold and WS5's fold run on. Build WS3's tower and discharge (NL) + endogenous-order before closing WS4-WS5. WS3 also proves well-foundedness (the scaffolding's job).
- **WS4 consumes WS3.** The close-or-fold dichotomy and CLOSE-forbidden need the tower and its order.
- **WS5 owns the fold fork and consumes WS3/WS4.** The fold is a claim *about* the tower; it cannot be attempted until the tower exists, and it must never be folded into `reify` or the tower construction. WS5 runs the kill condition and reports Discharged-on-scaffold / FATAL / Partial.
- **WS6 (heuristic ceiling)** reports the universal forms of productive blindness (WS1) and the fold (WS5) where they exceed what is rangeable, and states the Series 11 handoff.
- **WS7 runs last.** It audits all others, unfolds the bookkeeping and κ-by-fiat risks, and aggregates the strip-test and freeness/growth/fold ledger; it cannot report until WS1-WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback, then propagated forward.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria | designs' motivating prose; charter's metaphysical framing (no "to relate is to create," no "the growing self") |
| Address (Phase E) | `spec/series-review-N.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level, plus, for Series 10, **unfold the growth theorem and check it is a bisim-non-embedding (a bigger world), not a lengthening list**, and **check the fold is reflexivity and the results hold for all large κ**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series, the next series' plan

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 10 closes. The final `spec/series-review-N.md` and `charter-status.md` become the **seed of Series 11**, following the program's inter-series discipline:

> **Each series is a response to the previous series' honest findings, not a continuation of its plan.**

The pattern (Series 1 → 2 → ... → 10): each series takes the place the mathematics pushed back hardest in the prior series and makes *that* its question. Series 9's hardest pushback was that a moving hole on a fixed field is still one hole; Series 10's response is reification that grows the carrier. Series 10's response also DEFERS one thing by explicit design: the endogenous bound. Series 10 proves the engine on a κ-scaffold; **Series 11 inherits the κ-removal and the finiteness-of-attention unification**, this is not a discovered pushback but a pre-declared handoff (charter §10, WS6). Beyond that pre-declared inheritance, whatever Series 10's final review surfaces as its hardest resistance becomes the rest of Series 11's question. The charter forecasts the candidates: if growth comes back **Bookkeeping**, Series 11 inherits the deepest form of the plurality question, whether reification can EVER grow the world or whether the fixed carrier is essential. If the fold comes back **FATAL**, Series 11 inherits the tragic horn, whether the many can be had at all without an imported bound, and finiteness of attention is tested as the last candidate. If the fold is **Discharged-on-scaffold**, Series 11's central task is the κ-removal itself, testing whether the fold survives when the wall comes down and whether finiteness of attention is the endogenous bound the structure imposes on itself.

The mechanics, unchanged:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone**, its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again, design-all, build-all, then the review→address loop.

---

*Protocol for Series 10. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and, once written, `spec/wsNN-design.md` (the per-workstream contracts) and `spec/series-review-N.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `spec/series-review-N.md`. The whole-series blind review is the primary vehicle, and Series 10 sharpens it with two checks, because the series stands or falls on whether reification genuinely grows the carrier (the bookkeeping check, the repair of Series 9's moving hole) and whether the bound is endogenous-or-honest-scaffolding rather than the imposed cardinal (the κ-by-fiat check, Series 8's conservation sin relocated, and the reason the endogenous bound is deferred to Series 11). No em dashes in final academic paper copy; this working protocol is not final copy.*
