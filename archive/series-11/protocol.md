# Relational Existentialism — Series 11 Protocol

**The process. Series 11 keeps the program's one load-bearing idea, that blind review has teeth only when the reviewer cannot see the motivation, and keeps the Series 05/06/08/09/10 batching: each phase runs once across the whole series, because the workstreams are one coupled object. The whole series stands on a single claim, that finite attention is both the reader that makes a reified relatum real (rescuing Series 10's Bookkeeping) and the bound that keeps the proliferating tower from paradox (replacing Series 10's scaffold κ), because the same incompletability that generates the many forbids any hold from grasping the whole, and that claim is only checkable across all the workstreams together.**

*Series 03 ran a seven-phase cycle per proof obligation. Series 04 collapsed that to five steps per workstream. Series 05, 06, 08, 09, and 10 collapsed it further: the same phases (design, build, blind review, address), each run once over all seven workstreams together. Series 11 inherits the Series 10 shape unchanged, INCLUDING the anti-loop discipline Series 10 added (§0.2a), which review-2 confirmed worked on its first test. The coupling is at least as tight: the whole series stands on the claim that one operation (finite attention, holding a reified relatum, never holding the whole) both makes the many real and bounds it, and that is only checkable across all workstreams together. Series 11 is the program's terminal series, the unification of Series 08's finite hold with Series 10's reification tower.*

---

## 0. Core principle

Four things carry over unchanged, because they are what make the program honest:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria, but **not** the charter's motivating prose. No "to attend is to become," no "finite attention makes the many real," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.
2. **Never relabel a shortfall as the goal, and reach for the pre-registered failure BEFORE the compiler.** When a build falls short, the honest outcome is a **Partial** (or **Impossibility**, or **Refuted hypothesis**, or **Bookkeeping**, or **Tragic**, or **Circular** for WS7) with the obstruction made precise and routed, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss. The charter's pre-registered failure outcomes (the Failed rows, the kill condition, the Bookkeeping and Tragic clauses) are HONORABLE FIRST MOVES, not last resorts. When a finding shows a pre-registered failure condition has been met, reporting it is the correct action; constructing a theorem that avoids it is the §0.2 sin. (Series 08's spine finding recurred three times because Phase E kept building cheaper theorems instead of reporting the pre-registered Partial; Series 10 did it right on the first pass, reporting Bookkeeping and proving it.)

**2a. The recurrence guard (the Series 08 anti-loop discipline, confirmed by Series 10 review-2), applied at both Phase D and Phase E.** A SERIOUS finding closes in exactly ONE of two ways, and `charter-status.md` must name which: **(Fixed)** the charter/design's *originally specified* target was built (name the theorem), or **(Relabeled)** the target was not built, the precise obstruction is recorded, and the payoff's status is demoted to the pre-registered honest outcome (Partial / Failed / Refuted / Bookkeeping / Tragic). "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is NEITHER, and is prohibited. Findings carry stable IDs across passes; a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count. Series 10 is the positive model: all three pass-1 SERIOUS findings closed as honest Relabels (growth → Bookkeeping, proved as a theorem; the fold → definitional, retracted; CLOSE-forbidden → inspection-level, gloss retracted), no recurrence at pass 2.

3. **Strip the *why*, keep the *what*, and strip the *word*, keep the *theorem*.** For every payoff, delete the structural term, **"attention," "reads," "real," "reification," "tower," "bound," "finite," "holds"**, and check whether the statement still goes through as a bare freeness, bisimulation, diagonal, or reachability fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. The strip test is written into the WS1-WS5 designs and aggregated by WS7; the reviewer runs it.

Series 11 adds two emphases of its own, because its signature risks are the two central findings of the two prior series, inherited and relocated to attention and the κ-removal:

4. **Attention-reality must NOT be Bookkeeping re-hit (Series 10's proved failure is the first cardinal sin).** The whole rescue of Series 10 rests on finite attention being a reader GENUINELY DISTINCT from the plain quotient. This is the exact trap Series 10 proved it fell into (`ws2_reify_bisim_embeds`: the plain engine merges the reified relatum, so the label is unread, hence Bookkeeping). The review must, for WS1/WS2 specifically, confirm attention distinguishes the reified relatum WHERE THE PLAIN BISIMULATION COLLAPSES (attention-embed fails where bisim-embed holds), AND that attention is a genuine hold on real reified relata, not a fresh external labelling function. If "attention" is just a new label on the fixed coalgebra (Series 10's `labelLoop` fact relabelled), attention-reality is **Bookkeeping** re-hit and a SERIOUS finding: Series 10's proved failure returning while the prose claims a rescue. This check is PROMOTED to first-class.
5. **The bound must be holding-not-size, κ GENUINELY removed, NEVER readmitted by the back door (the second cardinal sin, Series 08's conservation / Series 10's scaffold returning).** Series 11 removes κ and this is honest ONLY if no result silently re-admits a cardinality ceiling under another name. This is the exact trap Series 08 wrote a kill condition against (a bound assumed rather than shown) and Series 10 scaffolded with an explicit κ marked for removal. The review must, for WS3/WS4/WS5 specifically, confirm the bound is (NT) no-total-attention plus bounded-holding, both facts about HOLDING refutable by exhibiting a total attention or unbounded hold, and confirm every theorem holds κ-free (no cardinality ceiling on the tower). A "self-bound" that unfolds to "attention ranges over a κ-bounded set" is κ readmitted by the back door and a SERIOUS finding: the wall rebuilt while the prose says it was removed. This check is PROMOTED to first-class.

---

## 1. The documents

- **`charter.md`, the design (stable).** The question, the Series 10 Bookkeeping it responds to, finite attention as reader-and-bound, the attention-reality spine, the three consequences, the false escapes (import/leaf/Bookkeeping-re-hit/κ-readmitted/total-hold), the crown-vs-tragic fork with its kill condition, the seven workstreams, success criteria, honest risks, and the program's terminal framing. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md`, the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, strip-test annotation. The contract a build is judged against. **All seven are committed as a batch before any build begins** (§2, Phase B).
- **`spec/README.md`, the design index.** Ties the seven together: the shared carrier choice (the κ-free reifying tower with finite attention, fixed once in WS1 and consumed by all), the primitive decision (the reification tower and diagonal from Series 10/09, plus finite attention and the κ-removal, charter §3), the cross-workstream triage summary, the predicted headline.
- **`charter-status.md`, the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the crown fork's running status, the closed log, the series-review log. Where change lives.
- **`spec/series-review-N.md`, the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it and runs the recurrence check (§0.2a) first.

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
| F | Close | 1 | Claude code with repo | summaries + root README + program close |

The canonical run is **B → C → D → E → D → E** (two review passes, three code touches counting the initial build), with more D→E loops added only if a review pass still returns SERIOUS findings.

### Phase A — Charter (once)

Write `charter.md`: the question, the Series 10 Bookkeeping it responds to, finite attention as reader-and-bound, the attention-reality spine and its three consequences, the false escapes, the crown-vs-tragic fork and kill condition, the workstreams, success criteria and outcome vocabulary, honest risks, the program's terminal framing. **Done** — Series 11's charter is written; this protocol and `charter-status.md` are its companions.

### Phase B — Design all seven (one session, with context)

**Prompt to seed the design session:**

> You are writing all seven per-workstream design docs for Series 11 in one session, with `charter.md` and the repository in view. Series 11 is standalone but transcribes (does not import) machinery from Series 10, 09, 08, and 04. Name the theorems to be transcribed: the reification tower (`reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`, `ws3_order_endogenous`), the reification section (`IsReify`: `dest (reify s) = s`, `ws1_reify_injective`), the Bookkeeping theorem (`ws2_reify_bisim_embeds`, `ws2_growth_is_bookkeeping` — transcribed as the thing attention must overturn), the diagonal spine (`ws1_no_self_total_hold`, `ws1_diagonal_not_bisim`), the collapse engine (`ws1_atomless_bisim` / `hneRel_isBisim`, the Series 07 floor), hereditary non-emptiness (`SHNE`), behavioral identity, and the recoverability/free import test (`Recoverable`/`plainOf`). Every design must contain:
>
> - **3 to 7 candidate framings** of the obligation, each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory (the κ-free reifying tower; finite attention as a hold reading a bounded part; the attention-distinction; no-total-attention as the diagonal at tower scale; the bound as holding-not-size), the success condition, and the explicit failure mode (Bookkeeping-re-hit / κ-readmitted / import / leaf / total-hold / transfinite-limit-breaks-bound).
> - **A paper-decidable triage** per candidate, a check runnable by inspection before writing Lean, collapsed into a table, with the framing choice downstream of the triage.
> - **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems.
> - **Outcome classes** (Discharged / Impossibility / Partial / Refuted hypothesis / Bookkeeping / Tragic / Failed / — WS7 — Circular) with pre-registered honest alternatives, and the **strip-test annotation** per payoff (which structural word, deleted, would be the test).

Two Series-11-specific design duties, settled in this batch:

- **Finite attention is defined once (WS1) and is ambient for all.** A hold reading a bounded part of the κ-free tower, with FINITUDE the load-bearing property (not an imported index), genuinely distinct from the plain quotient (§0.4, not Bookkeeping) and never total (§4.5, not violating the diagonal). Whichever concrete attention WS1 picks becomes the setting WS2-WS6 are written against. Do not let two workstreams assume different attention notions.
- **The κ-removal is performed once (WS1) and propagated.** Every Series 10 theorem reused must be re-checked to hold κ-free; any that relied on κ being small is reopened. The large-κ discipline of Series 10 is promoted to κ-free: no result may rely on a cardinality ceiling. The imported-ordinal / imported-cardinal branch is designed in as a pre-registered failure mode to be refuted, not a fallback.

### Phase C — Build all seven (one session, with repo context)

**Prompt to seed the build session:**

> Realize every Series 11 design in `formal/Series11/wsNN.lean`, building `Series11.lean` and `AxiomCheck.lean`, self-contained: transcribe Series 10/09/08/04 machinery, import nothing from `series-10/`, `series-09/`, `series-08/`, `archive/`. Respect the dependency order (§4): WS1 first (blocking, finite attention + the κ-removal + the attention-reality spine), then WS2, then WS3 (no-total-attention), then WS4-WS6, then WS7. The build produces theorems (or precise impossibilities, or a Tragic-horn report, or an honest Bookkeeping re-report) matching the designs' signatures. Update `charter-status.md` as you go. Sorry-free and axiom-clean or it is not done.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial (or Bookkeeping, for the payoff; or Tragic, for the fork) with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield. Because the build is batched, a mid-build discovery that reaches upstream (e.g. WS3 needing attention to expose no-total-attention as a first-class fact WS1 did not provide) is handled by the pre-registered fallback in the affected design, not by an ad hoc patch.

The first incremental build takes longer than two minutes. Please run it as a background task at the start of the session.

**The first file is WS3's no-total-attention** in spirit even though WS1 builds first: WS1 establishes attention, the κ-removal, and the attention-reality spine; but the object the bound turns on is no-total-attention (the diagonal at tower scale, charter §3), which should be discharged early as the seed. **The bound (EB) and the crown are NOT attempted in the build until WS4/WS5**, and the bound is never built into attention's definition.

**The two most important build checks (Series 11's reasons to exist):**
1. When WS1/WS2's attention-reality is built, confirm attention distinguishes the reified relatum WHERE THE PLAIN BISIMULATION COLLAPSES, and is a genuine hold on real reified relata (not a fresh external label). If "attention" is Series 10's `labelLoop` fact relabelled, the spine is **Bookkeeping** re-hit, Series 10's proved failure returning, and that must be recorded honestly, not papered over.
2. When WS4/WS5's bound is built, confirm it is holding-not-size and every theorem holds κ-free. If the bound rests on a cardinality ceiling on attention's range, it is **κ readmitted** by the back door, Series 08's/Series 10's scaffold returning, and must be recorded honestly. The crown must not be claimed by re-importing the wall.

### Phase D — Blind series-review (one session) → `spec/series-review-N.md`

**Prompt to seed the blind review session:**

> Please clone https://github.com/colleen-love/relational-existentialism and view the series 11 working branch.

> Review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no signature that quietly weakens the target? **On the second and later passes, run the recurrence check FIRST (§0.2a):** for every finding graded SERIOUS in the prior `spec/series-review-{N-1}.md`, unfold the actual proof term and determine whether Phase E BUILT the originally-specified target (name it, confirm it is that target) or RELABELED to a pre-registered honest outcome; a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count, and its correction is stated as the binary "build the named target OR report the pre-registered outcome, no third theorem." Then, specifically for Series 11, without building the code, run:

- **The Bookkeeping-re-hit check (§0.4), the sharpest on the payoff side and the reason the series exists.** Unfold WS1/WS2's attention-reality. Does attention distinguish the reified relatum WHERE THE PLAIN BISIMULATION COLLAPSES (attention-embed fails where `ws2_reify_bisim_embeds`'s bisim-embed holds), and is attention a genuine hold on real reified relata? Or is "attention" a fresh external labelling of the fixed coalgebra (Series 10's `labelLoop` fact relabelled)? If the latter, the spine is **Bookkeeping** re-hit, a SERIOUS finding, and the rescue failed (Series 10's proved failure returning, honestly reported).
- **The κ-readmitted check (§0.5).** Is the bound (NT) no-total-attention plus bounded-holding, both facts about HOLDING? Or does "self-bound"/"finite" unfold to "attention ranges over a κ-bounded set" (cardinality by the back door)? Do all theorems hold κ-free, or does a result rely on a cardinality ceiling? A bound resting on re-imported κ is **κ readmitted**, a SERIOUS finding, Series 08's/Series 10's scaffold returning. Confirm the κ-removal (WS1) is genuine and propagated.
- **The strip test on every payoff (§0.3).** Delete "attention" from the reality payoff; delete "finite" from the bound; delete "reads" from the rescue; delete "holds" from no-total-attention. Flag every payoff that survives stripping as a bare freeness / bisimulation / diagonal / reachability fact, not an earned attention theorem.
- **The attention-reality verdict (WS1).** Is attention's distinction proved FREE (not recoverable), routing through the diagonal (`ws1_no_self_total_hold`) and reification (`IsReify`)? Or is freeness asserted by a fresh labelling independent of the diagonal (which would make attention-reality a stipulation and likely an import)? Confirm the distinction reconstructs-a-self-total-hold-if-recoverable, tying it to the Series 04/09 import test.
- **The no-total-attention verdict (WS3).** Is (NT) proved as the diagonal at tower scale (a total attention is a self-total hold, `ws1_no_self_total_hold` forbids it), an Impossibility? Or is no-total-attention asserted / built into attention's definition by a clause?
- **The endogenous-bound verdict (WS4).** Is the bound derived from no-total-attention plus bounded-holding (holding-not-size), or a re-imported cardinality ceiling? Is bounded-holding endogenous, or an imported index?
- **The no-leaf verdict (WS3).** Confirm (NL): attention reads full relata, `SHNE` preserved (`ws3_reify_preserves_SHNE`), never a bare point. Attention reading a leaf anywhere is a SERIOUS finding (the constraint the program respects since Series 07).
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open, e.g. WS2's rescue depending on WS1's attention being genuinely distinct from the plain quotient; WS4's bound depending on WS3's no-total-attention genuinely being the diagonal; WS5's crown depending on the κ-removal being genuine. The batched review is the only place this is visible.
- **The coincidence rule** where it applies: is a "forced" theorem genuinely independent of its "definitional" partner, or does its proof unfold to the definition? (WS1 attention-reality vs. the diagonal, which SHOULD route through it — here the check is that it genuinely does, and that the distinction is not thereby a mere re-reading of the residue with no attention content; WS3 no-total-attention vs. self-totality; WS4 bound vs. attention's definition.)
- **The crown verdict, stated plainly.** Which of {Discharged, Tragic/refuted, Partial} did the code deliver for the crown? Confirm it is one of these, is honestly labelled, never assumed, never re-importing κ.
- **The axiom-check status.** Was `#print axioms` actually run over every headline, or is the claim still static?

Write `spec/series-review-N.md`: findings graded SERIOUS (the verdict rests on it, a flagship payoff laundering, attention-reality is Bookkeeping re-hit, the bound is κ-readmitted, attention violates the diagonal, **or a prior SERIOUS finding RECURRING via a target-avoiding closure**), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed, no goalpost-moving: "relabel this / prove that / strip and re-prove / run the kill condition / report Bookkeeping or Tragic honestly," never "lower the bar." For a RECURRING finding, the correction owed is the binary: "build the specified target [name it], OR report the pre-registered outcome — no third theorem."

If there is a serious finding, continue to Phase E. If not, conclude with Phase F.

### Phase E — Address `spec/series-review-N.md` (one session)

**Prompt to seed the address session:**

> Please pull your branch, review the most recent `spec/series-review-N.md` file, and address every finding. For each SERIOUS finding, run this sequence in order, and do not skip to building a theorem until you have done the first two steps:
>
> 1. **Locate the charter's pre-registered honest-failure outcome for the owning workstream** — the Failed row, the kill condition, the Bookkeeping/Tragic/Partial clause. It is written into the charter §5 and §8 precisely so falling short is an honorable, anticipated move. Read it before anything else.
> 2. **Ask whether the finding shows that condition has been met.** If it does, **REPORT it** (demote the payoff to Bookkeeping/Tragic/Partial/Failed/Refuted, retract the overclaim, record the obstruction — and where possible PROVE the failure antecedent as a theorem, as Series 10 proved its Bookkeeping). Constructing a new theorem that establishes the antecedent of a pre-registered failure clause and labels the result a success is the §0.2 sin.
> 3. **Only if the pre-registered failure has NOT been met, attempt the charter/design's originally-specified target** (name it, from the design doc). Build *that* target, not an adjacent weaker theorem that compiles.
>
> Then close each SERIOUS finding in **exactly one of two ways, and state which in `charter-status.md`**: **(Fixed)** the originally-specified target was built (name the theorem, confirm by unfolding it is that target), or **(Relabeled to Bookkeeping/Tragic/Partial/Failed/Refuted)** the target was not built (record the precise obstruction and demote the payoff). "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is neither and is prohibited. A Relabel to a pre-registered outcome is a SUCCESS, not a failure. If the finding is RECURRING, the only two permitted actions are Fixed-by-building-the-named-target or Relabeled-to-the-pre-registered-outcome; a third adjacent theorem is forbidden. Record every change in `charter-status.md` (the series-review log and the affected workstream rows, noting Fixed vs Relabeled per finding); keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

### Phase F — Close (one session, and the program's close)

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 11 closes, and with it the program. Write `summary.md`, `summary-technical.md`, and update the root `README.md` to reflect the findings (a new row in the series table AND, since this is the terminal series, a program-level synthesis: the four-beat arc — Parmenides / diagonal / reification / attention — and whether the crown landed or the Tragic horn was reported). State plainly what the whole program established and what it leaves open. If the crown landed, the program closes on its thesis; if the Tragic horn, on an honest defeat that is itself a finding.

---

## 3. Why the review is batched at series level (not per workstream)

Series 04 reviewed per workstream and caught most gaps, but its sharpest findings came from its end-of-series adversarial review. Series 05, 06, 08, 09, and 10 promoted the whole-series blind review to the primary vehicle because their payoffs were meant to be consequences of a single fact. Series 11's payoffs are just as tightly coupled: the rescue of reification, the endogenous bound, and the unification are all meant to be consequences of one operation (finite attention that reads but never totalizes), so a payoff can look earned in its own file while secretly being an unread label (Bookkeeping re-hit), a re-imported cardinality ceiling (κ-readmitted), or a total hold (the diagonal violated). Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it: the reviewer sees the whole dependency graph and can trace a "discharged" rescue to the open obligation in another file that actually carries it, and can trace the bound's endogeneity through to whether it is holding-not-size or a cardinality artifact.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude, a stated limitation, not claimed independence. The objective anchors, the dependency graph, the `#print axioms` records, the strip-test results, the Bookkeeping-re-hit check (attention-embed vs bisim-embed), the κ-readmitted check (κ-free discipline + holding-not-size), and WS7's freeness/no-total-attention/bound ledger, are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges for Series 11:

- **WS1 is blocking.** The gate is attention-reality: a finite attention makes the reified relatum real by a free distinction routing through the diagonal, on the κ-free tower. Nothing downstream is sound until this lands, because it is what rescues Series 10's Bookkeeping and what the bound runs on. WS1 also fixes attention, the κ-removal, and the carrier, ambient for all.
- **WS2 depends on WS1's attention-reality.** The rescue (attention-embed fails where bisim-embed holds) holds only if attention's distinction is genuine and free; WS1 secures it. WS2's rescue is stated with attention-reality as a hypothesis until WS1 discharges it.
- **WS3 supplies no-total-attention the bound consumes.** No-total-attention (the diagonal at tower scale) is what WS4's bound runs on. Build WS3's NT and (NL) before closing WS4. WS3 also derives bounded-holding endogenously.
- **WS4 consumes WS3.** The κ-free bound needs no-total-attention and bounded-holding.
- **WS5 owns the crown fork and consumes WS3/WS4.** The crown is a claim *about* the bound at all stages; it cannot be attempted until the bound exists at finite stages, and it must never be assumed or re-import κ. WS5 runs the kill condition and reports Discharged / Tragic / Partial.
- **WS6 (heuristic ceiling and program close)** reports the universal and transfinite forms of attention-reality and the bound, and the program-level synthesis.
- **WS7 runs last.** It audits all others, unfolds the Bookkeeping-re-hit and κ-readmitted risks, and aggregates the strip-test and freeness/NT/bound ledger; it cannot report until WS1-WS6 have.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it. Because the build is batched, an upstream change discovered mid-build is resolved in the same session via the affected design's pre-registered fallback, then propagated forward. (The κ-removal is the largest such propagation: any Series 10 theorem that relied on small κ reopens.)

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | — |
| Build-all (Phase C) | all designs + repo | — |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria + prior `series-review-{N-1}.md` (for the recurrence check) | designs' motivating prose; charter's metaphysical framing (no "to attend is to become," no "finite attention makes the many real") |
| Address (Phase E) | `spec/series-review-N.md` + all code + all designs | — |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level, plus, for Series 11, **unfold attention-reality and check it distinguishes where bisimulation collapses (not an unread label)**, and **check the bound is holding-not-size and the results hold κ-free**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series, and the end of the program

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 11 closes. Because Series 11 is the program's terminal series, there is no Series 12 seed in the ordinary sense; instead, Phase F writes the program-level synthesis (§2, Phase F). Should the terminal review nonetheless surface a hard resistance worth a successor (for instance, the crown Partial with a specific transfinite obstruction that a further series could attack), the inter-series discipline still applies and a Series 12 could be chartered as a response to that finding:

> **Each series is a response to the previous series' honest findings, not a continuation of its plan.**

But the program's intent is that Series 11 completes the four-beat arc (Parmenides / diagonal / reification / attention) and reports the honest terminus, crown or tragic. The mechanics, unchanged if a successor is chartered:

1. Freeze the closing series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone**, its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again.

---

*Protocol for Series 11, the program's terminal series. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and, once written, `spec/wsNN-design.md` (the per-workstream contracts) and `spec/series-review-N.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `spec/series-review-N.md`, with the anti-loop discipline (§0.2a) inherited from Series 10 where it worked on its first test. The whole-series blind review is the primary vehicle, and Series 11 sharpens it with two checks, because the series stands or falls on whether finite attention is a reader genuinely distinct from the plain quotient (the Bookkeeping-re-hit check, the rescue of Series 10's proved failure) and whether the bound is holding-not-size rather than a re-imported cardinality ceiling (the κ-readmitted check, Series 08's conservation and Series 10's scaffold returning). No em dashes in final academic paper copy; this working protocol is not final copy.*
