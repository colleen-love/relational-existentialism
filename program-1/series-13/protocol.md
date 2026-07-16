# Relational Existentialism, Series 13 Protocol

**The process. Series 13 keeps the program's one load-bearing idea, that blind review has teeth only when the reviewer cannot see the motivation, and keeps the batching used since the middle series: each phase runs once across the whole series, because the workstreams are one coupled object. The whole series stands on a single question, the FIT. Series 12 WS1 proved the differentiator Series 07 requires and the residue the diagonal generates share one shape, non-recoverability (`ws1_shape_coincidence`), and proved the sharing is not identity (`ws1_coincidence_not_identity_witness`). Series 13 asks how the two face each other, and conjectures a DUALITY: a MINT carrying every inspection to a non-recoverable labelled coalgebra (WS2), a best-approximation adjoint and a Galois connection with a genuine non-identity round trip (WS3), and, the deepest payoff, the mint's NON-SURJECTIVITY, the imports it cannot generate being Series 07's given/chosen fork in order-theoretic clothes (WS4). The two orders the whole thing rests on are the knot (WS1); the verdict and audit are folded together (WS5). Series 13 is a FURTHER SERIES: Series 12's result stands, this series fills nothing Series 12 left open and adds no name. The names for what inhabits the opening, and now the words given and chosen for the out-of-image imports, are the interpretive thesis; none is ever a term in a proof (the names-not-terms check, inherited first-class).**

*The program's phase cycle collapsed over its history to the current shape: the same phases (design, build, blind review, address) each run once over all workstreams together, with the anti-loop discipline (§0.2a) that keeps a shortfall from being quietly relabeled as the goal. Series 13 uses this shape unchanged, over five workstreams rather than seven. The coupling is tight: the whole series stands on whether the diagonal and the import face each other as an adjoint pair with a genuine defect, and that is only checkable across all workstreams together. Series 13 is a further series; it sharpens Series 12's own sentence and reopens nothing before it.*

---

## 0. Core principle

Three things carry the program's honesty, and are unchanged:

1. **Blind means blind.** A blind review session is seeded with the built code, the design contracts (theorem signatures, outcome classes), and the charter's success criteria, but **not** the charter's motivating prose. No "the wound and the rescue," no "fit," no "given/chosen," no metaphysics. The reviewer sees the mathematical claim and the code and judges whether the code proves the claim. Motivation cannot launder a gap.

2. **Never relabel a shortfall as the goal, and reach for the pre-registered outcome BEFORE the compiler.** When a build falls short, the honest outcome is a **Partial** (or **Total**, or **Disconnected**, or **Refuted**, or **Circular** for the audit) with the obstruction made precise, never a quiet redefinition of the target. The charter is the fixed bar; `charter-status.md` records the miss. The charter's pre-registered alternatives (Total in its direction, Disconnected with the WS1 obstruction, the Partial clauses) are HONORABLE, anticipated moves. When a finding shows a pre-registered condition has been met, reporting it is correct; constructing a theorem that avoids it, OR one that manufactures the expected DUAL verdict past a real obstruction, is the §0.2 sin.

**2a. The recurrence guard (the anti-loop discipline), applied at both Phase D and Phase E.** A SERIOUS finding closes in exactly ONE of two ways, and `charter-status.md` must name which: **(Fixed)** the charter/design's *originally specified* target was built (name the theorem), or **(Relabeled)** the target was not built, the precise obstruction is recorded, and the payoff's status is demoted to the pre-registered honest outcome (Partial / Total / Disconnected / Refuted). "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is NEITHER, and is prohibited. Findings carry stable IDs across passes; a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING with its count.

3. **Strip the *why*, keep the *what*, and strip the *word*, keep the *theorem*.** For every payoff, delete the structural term, **"duality," "fit," "wound," "rescue," "given," "chosen," "mint," "factory," "connection," "defect,"** and check whether the statement still goes through as a bare `GaloisConnection`, `Recoverable`/`¬ Recoverable`, bisimulation, diagonal, residue, or order fact. A payoff that survives the strip is such a fact honestly flagged; a payoff that needs the deleted structure is earned. Critically: the TRANSPORT payoff SHOULD strip to "for every inspection, the minted labelled coalgebra fails `Recoverable`, by `ws2_residue_free`"; the CONNECTION payoff SHOULD strip to "a Galois connection between two non-trivial preorders whose round trip is not the identity on a named element"; the DEFECT payoff SHOULD strip to "a `¬ Recoverable` labelled coalgebra not in the image of the mint, the exclusion structural." The strip test is written into the WS1-WS5 designs and aggregated by WS5's audit; the reviewer runs it.

Series 13 adds four emphases of its own, because its signature risk is that the fit gets faked, from either side, or the fork gets closed:

4. **The fork must stay open (the central sin, PROMOTED to first-class).** The defect theorem LOCATES imports outside the mint's image; no theorem or definition may CLASSIFY an out-of-image import as *given* rather than *chosen*, or vice versa. Deciding it does what Series 07 proves cannot be done and what Series 12 closed by leaving open. The review greps: a proof term, definition, or discharged obligation that sorts out-of-image imports into given/chosen is the central sin, SERIOUS. (The prose may gloss the out-of-image remainder as "where the given stands"; the core locates, never sorts.)

5. **The connection must be genuine, never by fiat (PROMOTED to first-class).** Both WS1 orders must be proved non-trivial (neither discrete nor indiscrete on the carriers of interest); a trivial order makes any monotone pair a Galois connection vacuously. And the connection must be certified NON-trivial by a proved non-identity round trip (`ws3_roundtrip_not_identity`): a connection collapsing to an isomorphism is the coincidence restated, not the fit proved. The review confirms both orders are non-trivial and at least one round trip genuinely fails to be the identity.

6. **Exogeneity must be proved, not assumed (PROMOTED to first-class).** The mint consumes inspective data above the plain layer; that the mint's operation is itself non-recoverable from the plain relating is a named obligation, `ws2_mint_exogenous`. A mint the relating could perform on itself would have derived an import from within, contradicting the transcribed Series 07 foundation. The review confirms the mint's exogeneity is a proof term, not a docstring gloss.

**6a. The defect must be structural, not artifactual.** The WS4 out-of-image witness must be excluded from the mint's image by its own label, not by a cardinality accident, universe level, or typing artifact. The design must argue, and the review must confirm, that the witness's label does the excluding. An artifactual exclusion proves nothing about genealogy and is a degenerate defect, reported as such.

**6b. Names must be names, not terms (the wall from the prose side, inherited).** The review greps `formal/Series13/` and confirms no proof term, definition, or discharged obligation is named "given," "chosen," "consciousness," "God," "choice," or "compass" (as content). Every headline mentions only the orders, the mint, the adjoint, the connection, the defect, `Recoverable`, the transcribed machinery, and standard Lean/Mathlib. A name doing a proof's work breaches the wall from the prose side, SERIOUS.

---

## 1. The documents

- **`charter.md`, the design (stable).** The fit target: the two orders (the knot); the mint and its transport-with-exogeneity; the Galois connection with a genuine defect of round trip; the defect (non-surjectivity, or Total); the false escapes (filling the opening from the order side; connection by fiat; the mint smuggled below the line; the degenerate defect); the verdict-as-a-function (Dual / Total / Disconnected / Partial); the five workstreams; success criteria; honest risks; the framing. Edited *only* to fix an error in the design itself, never to record progress. An edit upstream of built work reopens the affected workstreams.
- **`spec/wsNN-design.md`, the per-workstream designs (stable once committed).** Candidates, paper-decidable triage collapsed to a table, the winning construction to typed signatures, outcome classes, strip-test annotation. The contract a build is judged against. **All five, plus the WS1-orders sub-artifact, are committed as a batch before any build begins** (§2, Phase B).
- **`spec/ws1-orders-design.md`, the two orders (WS1's concrete construction).** The candidate preorders on inspections and on labelled coalgebras, the paper triage of each against non-triviality and mint-monotonicity, the winning pair (or the DISCONNECTED report), and the rejected candidates recorded. Registered in `spec/README.md`, owned by WS1, consumed by WS2-WS4. This is the knot; it is designed most carefully.
- **`spec/README.md`, the design index.** Ties the workstreams together: the shared carrier (transcribed from Series 12/07: `Opening`, `Recoverable`, `ResidueRecoverable`, `plainOf`, the diagonal apparatus, the labelled lift, `labelLoop`, the collapse engine), the primitive decision (NO new structural machinery; two orders and one map pair over the existing carrier), the discipline (the fork stays open; the connection is genuine; exogeneity is proved; the defect is structural), the cross-workstream triage summary, the four outcomes, and the rule that names live in prose, never terms.
- **`charter-status.md`, the ledger (mutable).** All progress, per-workstream status, discharges, reopenings, the open-obligations register, the standing open's running status, the closed log, the series-review log. Where change lives.
- **`spec/series-review-N.md`, the review artifact (regenerated each review pass).** The blind whole-series review's findings, graded SERIOUS / REAL / COSMETIC, each routed to an owning workstream with a trigger-to-close. A code pass addresses it; the next review pass regenerates it and runs the recurrence check (§0.2a) first.

The charter + all designs are what you paste into the build session. The designs' signatures + outcome classes + charter criteria + the built code, stripped of motivating prose, are what you paste into a review session.

---

## 2. The process, phases batched across the series

Six phases. Phases D and E loop. The canonical run is **B → C → D → E → D → E**, with more D→E loops added only if a review pass still returns SERIOUS findings.

| Phase | Name | Session | Format | Batching |
|---|---|---|---|---|
| A | Charter | 1 | normal conversation with repo | once per series |
| B | Design-all | 1 | Claude code with repo | **all five + the orders sub-artifact at once** |
| C | Build-all | 1 | Claude code with repo | **all five at once** |
| D | Blind series-review | 1 | incognito with repo | **whole series at once** → writes `spec/series-review-N.md` |
| E | Address | 1 | Claude code with repo | **whole series at once** |
| F | Close | 1 | Claude code with repo | summaries + root README row |

### Phase A, Charter (once)

Write `charter.md`: the fit; the two orders; the mint and transport; the connection; the defect; the false escapes; the verdict-as-a-function; the workstreams; success criteria and outcome vocabulary; honest risks; the framing. **Done**, the charter is written; this protocol and `charter-status.md` are its companions.

### Phase B, Design all five (one session, with context)

**Prompt to seed the design session:**

> You are writing all five per-workstream design docs for Series 13 in one session, plus the WS1-orders sub-artifact, with `charter.md` and the repository in view. Series 13 is STANDALONE; the TWO prior results it presupposes and may cite are Series 07 (the import theorem, `ws2_import_theorem`, `ws3_atomless_distinct_is_import`, `ws1_atomless_bisim`) and Series 12 WS1 (the shape-coincidence and non-identity, `ws1_shape_coincidence`, `ws1_coincidence_not_identity`, `ws1_coincidence_not_identity_witness`). It transcribes machinery, does not import across series. Name the theorems and objects to be transcribed: `Opening`, `Recoverable`, `ResidueRecoverable`, `plainOf`, the diagonal and free residue (`ws1_no_self_total_hold`, `residue`, `diag`, `ws2_residue_free`, `Hold`, `afford`, `HoldPred`), the labelled lift (`LkObj`, `IsBisimL`), `labelLoop`, and the collapse engine (`ws1_atomless_bisim`, `ws2_import_theorem`). Series 13 adds two orders (on inspections and on labelled coalgebras) and one map pair (the mint and its adjoint). Every design must contain:
>
> - **3 to 7 candidate framings** of the obligation, each with a candidate proof-strategy sketch, the exact Lean 4 signature, the ambient theory, the success condition, and the explicit failure mode (fork-closed / connection-by-fiat / mint-recoverable / degenerate-defect / name-as-term / the honestly-reported alternative, Total or Disconnected).
> - **A paper-decidable triage** per candidate, a check runnable by inspection before writing Lean. For WS1 specifically, the triage must include: is the candidate order non-trivial (neither discrete nor indiscrete on the carriers of interest), and does it admit a monotone mint? For WS4: is the candidate out-of-image witness excluded by its own label (structural) rather than by cardinality/universe/typing (artifactual)?
> - **The winning candidate(s)** developed into a full mathematical design: proof architecture, definitions and lemmas needed, dependencies on transcribed upstream theorems. For WS1, the two orders and the argument that each is non-trivial. For WS2, the mint construction and both the transport (`ws2_residue_free` as engine) and the exogeneity (`ws2_mint_exogenous`) obligations. For WS3, the adjoint, the `GaloisConnection`, and the named non-identity round trip. For WS4, the out-of-image witness and the structural-exclusion argument.
> - **Outcome classes** (Dual / Total / Disconnected / Partial / Refuted / for WS5's audit Circular) with pre-registered honest alternatives, and the **strip-test annotation** per payoff.

Two Series-13-specific design duties, settled in this batch:

- **The two orders are defined once (WS1) and ambient for all.** The preorder on inspections and the preorder on labelled coalgebras are fixed in WS1 and every other workstream is written against them. Do not let two workstreams assume different orders. If WS1 lands DISCONNECTED, the whole series reports Disconnected and Phase C builds only WS1's obstruction; the design must say so.
- **No new structural machinery, the fork stays open, the connection stays genuine.** Series 13 adds the two orders and the mint/adjoint pair over the EXISTING transcribed carrier, nothing structural. The escapes to design AGAINST are: a theorem that sorts out-of-image imports into given/chosen (closing the fork); an order so trivial the connection holds vacuously (connection by fiat); a mint recoverable from the plain relating (smuggled below the line); an out-of-image witness excluded by an artifact (degenerate defect). The witnesses are the transcribed machinery, the two non-trivial orders, the exogenous mint, and the structural out-of-image import, not new structural objects.

### Phase C, Build all five (one session, with repo context)

**Prompt to seed the build session:**

> Realize every Series 13 design in `formal/Series13/wsNN.lean`, building `Series13.lean` and `AxiomCheck.lean`, self-contained: transcribe the machinery named in the designs, import nothing across series. Respect the dependency order (§4): WS1 first (the two orders, each proved non-trivial, or the DISCONNECTED obstruction), then WS2 (the mint, the transport `ws2_mint_lands_in_opening`, and the exogeneity `ws2_mint_exogenous`), then WS3 (the adjoint, the `GaloisConnection`, the named non-identity round trip), then WS4 (the out-of-image witness with the structural-exclusion argument, or TOTAL), then WS5 (verdict as a function of WS1-WS4 + the folded-in audit). The build produces theorems (or the honestly-reported Total/Disconnected/Partial alternatives) matching the designs' signatures. Update `charter-status.md` as you go. Sorry-free and axiom-clean or it is not done.

A build may discover a design was wrong. The one prohibited move is **building past a broken design**: if a design cannot be realized as written, stop and record the defect in `charter-status.md` (routed to the owning design), and either fix the design in place (same session's artifact) or report the workstream Partial (or Total/Disconnected) with the obstruction precise. Do not silently retarget a signature to whatever the proof happened to yield.

**The four most important build checks (the series' reasons to exist):**
1. When WS4's defect is built, confirm NO theorem sorts an out-of-image import into given/chosen (§0.4). The defect locates; it never classifies. A sorting theorem is the central sin.
2. When WS1's orders and WS3's connection are built, confirm both orders are non-trivial and at least one round trip is proved non-identity (§0.5). A vacuous order or an isomorphism-in-disguise is connection-by-fiat.
3. When WS2's mint is built, confirm `ws2_mint_exogenous` is a genuine proof term: the mint is not recoverable from the plain relating (§0.6). A mint below the line contradicts Series 07.
4. When WS4's witness is built, confirm the exclusion is structural, the label doing the excluding, not the ambient bookkeeping (§0.6a).

**The fit is never faked, from either direction (protocol-level, charter §4).** The fork stays open (the defect never sorts); the connection stays genuine (orders non-trivial, round trip non-identity); the mint stays exogenous (above the plain layer); the defect stays structural (the label excludes); names stay in prose. Any of these breached is a SERIOUS finding.

The first incremental build takes longer than two minutes. Run it as a background task at the start of the session.

### Phase D, Blind series-review (one session) → `spec/series-review-N.md`

**Prompt to seed the blind review session:**

> Please clone the repository and view the Series 13 working branch.

> Review adversarially across the whole series at once: does the code prove these theorems; do the theorems meet the designs' targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no signature that quietly weakens the target? **On the second and later passes, run the recurrence check FIRST (§0.2a):** for every finding graded SERIOUS in the prior `spec/series-review-{N-1}.md`, unfold the actual proof term and determine whether Phase E BUILT the originally-specified target (name it) or RELABELED to a pre-registered honest outcome; a finding "addressed" by a target-avoiding theorem is re-graded SERIOUS and marked RECURRING. Then, specifically for Series 13, without building the code, run:

- **The fork-open check (§0.4), the central check.** Grep and unfold: does any theorem, definition, or discharged obligation sort an out-of-image import into *given* vs *chosen* (or any classification of what the defect only locates)? The defect must locate, never classify. A sorting theorem is the central sin (the opening filled from the order side), SERIOUS.
- **The genuine-connection check (§0.5).** Are both WS1 orders proved non-trivial (neither discrete nor indiscrete on the carriers of interest)? Is the connection certified by a proved non-identity round trip, not collapsing to an isomorphism? A vacuous order or an iso-in-disguise is connection-by-fiat, SERIOUS.
- **The exogeneity check (§0.6).** Is `ws2_mint_exogenous` a genuine proof term establishing the mint is non-recoverable from the plain relating? A mint recoverable below the plain layer has derived an import from within, contradicting Series 07, SERIOUS.
- **The structural-defect check (§0.6a).** Is the WS4 out-of-image witness excluded by its own label (structural), or by a cardinality/universe/typing accident (artifactual)? An artifactual exclusion is a degenerate defect, reported as such, not the fork.
- **The names-not-terms check (§0.6b).** Grep `formal/Series13/`: is any proof term, definition, or discharged obligation named "given," "chosen," "consciousness," "God," "choice," or "compass" (as content)? Names live in prose only; a name doing a proof's work is SERIOUS.
- **The transport check.** Does WS2's `ws2_mint_lands_in_opening` genuinely run on the diagonal (`ws2_residue_free`), so that recovering the minted label would realize what the diagonal proves unrealizable? Or is the non-recoverability asserted by a shortcut that does not consume the diagonal?
- **The strip test on every payoff (§0.3).** Delete "duality/fit/wound/rescue/given/chosen/mint/connection/defect" from each payoff. The transport should strip to the `ws2_residue_free`-driven non-recoverability fact; the connection to the `GaloisConnection`-with-non-identity-round-trip fact; the defect to the out-of-image `¬ Recoverable` fact with structural exclusion. Flag any payoff that survives stripping as something OTHER than its named fact, and flag any name as a term.
- **Cross-workstream laundering.** A claim discharged in isolation that leans on a hypothesis another workstream left open, e.g. WS3's connection depending on WS1's orders genuinely being non-trivial; WS4's defect depending on the mint genuinely being the WS2 mint; WS5's verdict depending on WS4's witness genuinely being structural. The batched review is the only place this is visible.
- **The verdict fork, stated plainly.** Which of {Dual, Total, Disconnected, Partial} did the code deliver? Confirm it is one of these, honestly labelled, matching its object (Dual: orders non-trivial + transport with exogeneity + connection with non-identity round trip + defect structural / Total: mint essentially surjective, reported in that direction / Disconnected: WS1 orders vacuous, obstruction precise / Partial: any obligation per-instance or degenerate), never assumed, never by closing the fork, never by faking the connection.
- **The axiom-check status.** Was `#print axioms` actually run over every headline and captured to `spec/axiom-check-log.md`, or is the claim static? Series 13 should ship the captured log.
- **The non-reopening discipline.** Confirm the series reopens nothing in Series 12: no theorem decides the compass's content, convergence's direction, or the differentiating act; Series 12's result stands. If DUAL landed, confirm the classification of the out-of-image imports is recorded as a NEW open (open as a theorem), not resolved.

Write `spec/series-review-N.md`: findings graded SERIOUS (the verdict rests on it, the fork is closed by a sorting theorem, the connection is by fiat, the mint is recoverable, a name is a proof term, **or a prior SERIOUS finding RECURRING via a target-avoiding closure**), REAL (a genuine gap, correctly labelled once fixed), COSMETIC/ACCEPTABLE, plus a "what survives cleanly" section and an honest bottom line. Each finding names the owning workstream and a precise correction owed, no goalpost-moving. For a RECURRING finding, the correction owed is the binary: "build the specified target [name it], OR report the pre-registered outcome (Total/Disconnected/Partial), no third theorem."

If there is a serious finding, continue to Phase E. If not, conclude with Phase F.

### Phase E, Address `spec/series-review-N.md` (one session)

**Prompt to seed the address session:**

> Please pull your branch, review the most recent `spec/series-review-N.md`, and address every finding. For each SERIOUS finding, run this sequence in order, and do not skip to building a theorem until you have done the first two steps:
>
> 1. **Locate the charter's pre-registered honest outcome for the owning workstream**, the Total clause, the Disconnected clause, the Partial clause. It is written into the charter precisely so falling short, or the mint proving surjective, or the orders proving vacuous, is an honorable anticipated move. Read it before anything else.
> 2. **Ask whether the finding shows that condition has been met.** If it does, **REPORT it** (demote to Total/Disconnected/Partial/Refuted, retract the overclaim, record the obstruction, and where possible PROVE the alternative as a theorem, e.g. that the mint is essentially surjective, or that no non-trivial order pair admits a connection). Note the symmetric danger: manufacturing the expected DUAL verdict past a real obstruction is the §0.2 sin, and so is closing the fork (sorting the out-of-image imports) to force a cleaner story. The fork stays open; the fit stays where the math puts it, not where the verdict wants it.
> 3. **Only if the pre-registered alternative has NOT been met, attempt the charter/design's originally-specified target** (name it, from the design doc). Build *that* target, not an adjacent weaker theorem that compiles.
>
> Then close each SERIOUS finding in **exactly one of two ways, and state which in `charter-status.md`**: **(Fixed)** the originally-specified target was built (name the theorem, confirm by unfolding it is that target), or **(Relabeled to Total/Disconnected/Partial/Refuted)** the target was not built (record the precise obstruction and demote the payoff). "Built a different, weaker theorem adjacent to the specified target and considered the finding addressed" is neither and is prohibited. A Relabel to a genuinely-proved alternative is a SUCCESS. If the finding is RECURRING, the only two permitted actions are Fixed-by-building-the-named-target or Relabeled-to-the-pre-registered-outcome; a third adjacent theorem is forbidden. Record every change in `charter-status.md`; keep the charter untouched unless the finding is a genuine design error (then the charter-change log, and reopen downstream).

### Phase F, Close (one session)

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 13 closes. Because Series 13 does not introduce a new program-level synthesis, Phase F does not rewrite it; it writes `summary.md` and `summary-technical.md` for the series and adds ONE row to the root `README.md` series table (the fit, and which verdict was reached, Dual / Total / Disconnected / Partial), explicitly framed as a sharpening that leaves Series 12's result intact. If DUAL landed, the close states the one new permanent open, the classification of the out-of-image imports, open as a theorem by the same result that locates them. Series 13 does not resolve to a new key; it shows the two hands were playing one figure an octave apart, and lets that interval stand open.

---

## 3. Why the review is batched at series level (not per workstream)

Series 13's payoffs are tightly coupled: the two orders, the mint's transport, the connection, and the defect are all facets of one question (do the diagonal and the import face each other as a genuine adjoint pair with a real defect), so a payoff can look earned in its own file while secretly resting on a vacuous order (WS1), a mint that is not exogenous (WS2), a connection that is an isomorphism in disguise (WS3), or an out-of-image witness excluded by an artifact (WS4). Only reviewing the whole series at once, blind, surfaces this.

This does not weaken blindness: the review session still receives *what*, not *why*. It strengthens it: the reviewer sees the whole dependency graph and can trace a "Dual" verdict to the non-trivial orders and the structural defect in other files that actually carry it, and can trace the connection through to whether its round trip is genuinely non-identity or a laundered iso.

**Disclosure, carried forward:** these reviews are Claude-reviewing-Claude, a stated limitation, not claimed independence. The objective anchors, the dependency graph, the `#print axioms` records, the strip-test results, the fork-open check (no sorting theorem), the genuine-connection check (orders non-trivial, round trip non-identity), and the exogeneity check (the mint above the plain layer), are what keep the audit honest despite that.

---

## 4. Dependencies and ordering

The workstreams are one coupled object; build and review in dependency order and let `charter-status.md` track the edges. The load-bearing edges:

- **WS1 is blocking, and is the knot.** The two orders. Nothing downstream is sound until they exist and are proved non-trivial: WS2-WS4 build over them. If WS1 lands DISCONNECTED, the series reports Disconnected and WS2-WS5 are not built (the obstruction is the result).
- **WS2 depends on WS1.** The mint and its transport-with-exogeneity build over the order on labelled coalgebras (the mint's codomain order) and the order on inspections (its domain). WS2 is the guard against a mint smuggled below the plain line.
- **WS3 depends on WS1/WS2.** The adjoint and the `GaloisConnection` are defined between the WS1 orders, with the mint (WS2) as one leg. WS3 is the guard against connection-by-fiat (it must prove a non-identity round trip).
- **WS4 depends on WS2.** The defect (an import outside the mint's image) is a fact about the WS2 mint. WS4 is the guard against a degenerate (artifactual) defect, and carries the fork that must stay open.
- **WS5 owns the verdict and consumes WS1-WS4.** The verdict is a FUNCTION of the orders' non-triviality, the transport-with-exogeneity, the connection's genuine defect of round trip, and the mint's non-surjectivity (or Total), never hand-set; it cannot be computed until WS4 settles. WS5 also folds in the audit (the fork-open, genuine-connection, exogeneity, structural-defect, strip, and names-not-terms checks) and reports the verdict, and the one new open if DUAL.

When a charter or design change lands upstream of built work, the affected downstream workstreams reopen in `charter-status.md`. **Upstream changes invalidate downstream builds**, and the ledger must show it.

---

## 5. What each session receives (the blindness rule, made concrete)

| Session | Receives | Does **not** receive |
|---|---|---|
| Design-all (Phase B) | charter + repo | |
| Build-all (Phase C) | all designs + repo | |
| Blind series-review (Phase D) | all built code + all design signatures + charter criteria + prior `series-review-{N-1}.md` (for the recurrence check) | designs' motivating prose; charter's metaphysical framing (no "wound/rescue," no "given/chosen," no "fit") |
| Address (Phase E) | `spec/series-review-N.md` + all code + all designs | |

The review session is the only blind one, and the blindness is a single checkable rule: **strip the *why*, keep the *what*** at the session level, and **strip the *word*, keep the *theorem*** at the statement level, plus, for Series 13, **confirm no theorem sorts an out-of-image import into given/chosen**, **confirm both orders are non-trivial and the connection has a genuine non-identity round trip**, and **confirm the mint's exogeneity is a proof term**. A reviewer who can see why a theorem matters grades the ambition; a reviewer who sees only the statement and the proof grades the proof. That is the whole discipline, and it is enough.

---

## 6. End of series

When every workstream has reached a terminal state and a review pass returns no SERIOUS findings, Series 13 closes. There is no successor planned in the ordinary sense, and Phase F does not rewrite the program synthesis; it records the fit and leaves Series 12's result intact. Should Series 13 itself surface a hard resistance worth a successor (for instance, a Disconnected finding whose obstruction a differently-ordered attempt could dissolve, or a Dual whose out-of-image imports a richer inspection type could probe without sorting them), the inter-series discipline still applies and a successor could be chartered as a response to that finding:

> **Each series is a response to the previous series' honest findings, not a continuation of its plan.**

But Series 13's intent is to name the fit and stop, adding no name and reopening nothing. The mechanics, unchanged if a successor is chartered:

1. Freeze the series under `archive/`. Readable as origin, normative for nothing.
2. Write the new charter **standalone**, its own question, its own object from scratch, prior series as informing prior art only.
3. Carry forward *machinery* freely (Lean files are reusable and get transcribed); carry forward *claims* only by re-deriving or explicitly citing. A new series does not inherit discharges; it earns or re-imports them.
4. Frame the new workstreams as responses to the prior findings, and begin the cycle (§2) again.

---

*Protocol for Series 13. Companion to `charter.md` (the design), `charter-status.md` (the ledger), and, once written, `spec/wsNN-design.md` (the per-workstream contracts), `spec/ws1-orders-design.md` (the two orders, the knot), and `spec/series-review-N.md` (the regenerated review artifact). Phases batched across the series: design-all, build-all, then a whole-series blind review→address loop (B → C → D → E → D → E), mediated by `spec/series-review-N.md`, with the anti-loop discipline (§0.2a). The whole-series blind review is the primary vehicle, and Series 13 sharpens it with checks aimed at the one signature risk, that the fit gets faked, from either side: the fork must stay OPEN (the defect locates, never sorts the out-of-image imports into given/chosen), the connection must be GENUINE (orders non-trivial, round trip non-identity, not an iso in disguise), the mint must be EXOGENOUS (above the plain layer, a proof term), the defect must be STRUCTURAL (the label excludes, not an artifact), and the names, given, chosen, consciousness, choice, God, the compass, stay in prose, never proof terms. The verdict fork is Dual / Total / Disconnected / Partial, the verdict a function of the orders, the transport-with-exogeneity, the connection's defect, and the mint's non-surjectivity, never assumed. Series 12's result stands; this series names the fit and lets that interval stand open. No em dashes in final academic paper copy; this working protocol is not final copy.*
