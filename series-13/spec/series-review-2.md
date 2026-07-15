# Series 13, Series Review 2 (Phase D, pass 2)

**The blind whole-series review of the Phase E (series-review-1 closure) state on branch `claude/series-13-design-docs-s7uthq`, per protocol §2 Phase D. Findings carry stable IDs (SR2-N). The §0.2a recurrence check on SR1-1..SR1-6 runs first, per protocol.**

**Disclosure 1 (blindness, protocol §0.1).** This pass was run substantially blind, and materially more so than pass 1: the reviewer read the code, the design signatures, `protocol.md`, `charter-status.md`, and `series-review-1.md` first, and formed every finding below against the source. The reviewer did **not** read `charter.md`'s motivating sections before reviewing the code. One leak is disclosed: reading the charter's §6 success criteria (which §0.1 explicitly *entitles* the reviewer to) placed §8 "Positioning" in the same view, so the reviewer has now seen the motivating prose (the wound/rescue, the fit, the octave figure). This happened **after** all findings below were formed against the source and changed none of them, but it is recorded rather than concealed. **Structural note for Phase F:** the charter's criteria and its metaphysics live in one file, so §0.1's seeding rule cannot be honored by any reviewer who reads the criteria from source. If blindness is to be mechanical rather than aspirational, the criteria need to be extractable separately (see SR2-4).

**Disclosure 2 (the axiom claim is STILL unverified, SR1-6 recurs as SR2-1).** No Lean toolchain is installed in this sandbox and `leanprover-community.github.io` returns `HTTP 403 x-deny-reason: host_not_allowed`. `lake build` could not run. This review therefore could not reproduce `spec/axiom-check-log.md`, exactly as pass 1 could not. What this review *could* do mechanically, and did, is verify the log's internal consistency (below). This is a coverage gap in the review, not a demonstrated defect in the build.

**Scope.** `formal/Series13/{ws1..ws5, AxiomCheck}.lean` + `Series13.lean` (1,080 lines), `spec/*.md`, `charter-status.md`, `scripts/gate.sh`, against the design contracts and the charter's §6 criteria.

---

## 0. The recurrence check (§0.2a), run FIRST

For each SERIOUS finding in `series-review-1.md`, the ledger's claimed closure was checked by unfolding the actual proof term.

### SR1-1 (SERIOUS) — claimed **Fixed**. → **VERIFIED Fixed. Not recurring.**

The ledger claims the fix is a third conjunct on `ws1_orders_lab_nontrivial` plus a new `ws2_mint_nontrivial`. Both exist and both are real.

`ws1.lean:411-413` now carries `∃ a b, a.cT = b.cT ∧ ¬ a ≤ b`, witnessed by `⟨⊤,⊥⟩` and `⟨⊤,⊤⟩`. The `a.cT = b.cT` conjunct is discharged by `rfl` — the witnesses genuinely share the residue position — so the `¬ a ≤ b` cannot be satisfied by the `cT` clause and **must** be carried by the reference clause. Unfolding the final proof step: `rintro ⟨_, href⟩; exact href trivial`. The `leC` half is discarded (`_`), and the contradiction comes from `href : (⟨⊤,⊤⟩).cF h₀ → (⟨⊤,⊥⟩).cF h₀`, i.e. `True → False`, applied to `trivial`. This is the non-vacuous antitone firing that pass 1 said was missing. The certificate now exercises the contested clause.

`ws2_mint_nontrivial` (`ws2.lean:107`) is genuine and its witnesses are actual `mintL` applications, not literals.

Correctly named **Fixed**, not Relabeled: the originally specified obligation (a §0.5 certificate) is built and now covers the contested structure.

### SR1-2 (SERIOUS) — claimed **Fixed (with a disclosed design-realization note)**. → **VERIFIED Fixed. Not recurring. The dependency-cycle finding is correct.**

This is the one that deserved the hardest look, because "the design's theorem was unbuildable, so we built it across two files" is precisely the shape of §0.2a's prohibited third move. It is not, and the reason is checkable.

The design (`ws1-orders-design.md:184-191`) specifies `ws1_orders_lab_nontrivial` witnessed by `mintL dest h₀ …`. The ledger claims this is unbuildable because `mintL` is defined in WS2 and WS1 cannot name it. **Verified:** `mintL` is defined at `ws2.lean:33`, and `ws2.lean:16` reads `import Series13.ws1`. A WS1 theorem naming `mintL` is a genuine import cycle. **The design is internally inconsistent as written** — this is a real design error, not an excuse constructed after the fact.

Given that, the obligation was split: the antitone-position certificate in WS1 (which needs no mint), the mint-point certificate in WS2 (where `mintL` exists). Both halves are built, and `ws5_audit_genuine_connection` (`ws5.lean:142`) consumes **both**. Nothing was dropped in the split; the union covers what the design's single theorem intended. That is Fixed, correctly.

One residue: the design doc still carries the unbuildable signature. See SR2-3.

### SR1-3, SR1-4, SR1-5 (REAL) — all claimed **Fixed**. → **VERIFIED Fixed.**

- **SR1-3.** Charter discrepancy **CD-1** now exists in `charter-status.md` and states the `Lab`-vs-`LkObj` narrowing accurately. `ws4_mint_not_surjective`'s docstring now states its true domain. The box the docstring promised is populated.
- **SR1-4.** `scripts/gate.sh:30` now reads `check series-13 "^import Series13(\.[A-Za-z0-9_]+)*$"`. **Executed it: green on all three series.** Independently confirmed the import closure by grep — every import resolves to `Mathlib` or `Series13.*`.
- **SR1-5.** The ledger is swept to the post-build/post-review state. No stale "Not started" rows survive.

### SR1-6 (REAL, coverage gap) — claimed **CONFIRMED** by a Phase E re-run. → **RECURS as SR2-1 (REAL, unchanged grade).**

Not a recurrence in the §0.2a sense (that tracks target-avoiding closures of SERIOUS findings; this was a REAL coverage gap and Phase E's response was to re-run the check, which is the right response). But the gap itself is unclosed **for the reviewer**, for the same environmental reason, two passes running. Detail under SR2-1.

**Recurrence verdict: NO finding recurs via a target-avoiding closure. §0.2a is satisfied. Both SERIOUS findings from pass 1 are genuinely closed.**

---

## 1. The protocol's Phase D checks, run

**The fork-open check (§0.4), the central check. PASS.**
Grepped `formal/` for `Origin`, `genealogy`, `isGiven`, `isChosen`, `classify`, `sortInto`: the only hit is `ws4.lean:17`, a docstring line stating that no such term exists. Grepped all declaration heads for `given|chosen|consciousness|god|choice|compass|origin|genealogy`: **clean**. `ws4_mint_not_surjective`'s second conjunct is `¬ ∃ insp, labEquiv h₀ (mintL h₀ insp) (outWit h₀ h₁)` — a pure membership denial up to `≈`. No predicate anywhere partitions the out-of-image remainder. **The central sin is not committed.**

**The names-not-terms check (§0.6b). PASS.** As above; the interpretive vocabulary appears in docstrings and module prose only, never as a declaration name.

**The genuine-connection check (§0.5). NOW PASSES** (it did not at pass 1). Both orders are proved non-trivial; the labelled certificate exercises the antitone reference clause non-vacuously (SR1-1/SR1-2 above); non-triviality is additionally certified at mint points; and `ws3_roundtrip_not_identity` (`ws3.lean:134`) is genuine — the interior at `bRefActive` is strictly below the identity because `gb` drops `h₀` when the reference bit is active, and the proof discharges both disjuncts of the fold (`h₀ ≠ h₀` and `¬ True`) rather than asserting the gap. Not an iso in disguise.

**The exogeneity check (§0.6). PASS, exceeding contract.** `ws2_mint_exogenous` is a proof term, grounded in `plainOf_coalg_val` (`ws1.lean:369`), which *proves* the plain projection is `i ↦ {i}` independent of `b` rather than assuming it. `ws2_mint_not_plain_function` strengthens this to refute **any** plain-recovering function. The mint is above the plain layer.

**The structural-defect check (§0.6a). PASS.** `ws4_exclusion_structural`'s three conjuncts do the work jointly: `≈` preserves `cT` fully and `cF` at `h₀`; every mint is on the link by `rfl` (i.e. by the *definition* of `residue = diag` — the diagonal is the excluder); `outWit` is off it. The exclusion is by the witness's own label. Testing up to `labEquiv` rather than literal equality is the honest choice and is reasoned for in the design (literal equality would make DUAL true by construction).

**The transport check. PASS.** `ws2_mint_lands_in_opening` genuinely consumes the diagonal: the proof drives the `⊤`-plain-bisimulation to the `(⟨true⟩, ⟨false⟩)` label match, forces `residue insp = insp h₀`, and hands it to `ws2_residue_distinct`, which is `ws1_no_self_total_hold` — Cantor, transcribed and proved at `ws1.lean:232` in four lines with no appeal to anything else. Delete the diagonal and the theorem dies. Nothing is painted on.

**The strip test (§0.3). PASS on all three payoffs.**
- Transport → "for every inspection, the minted two-region coalgebra fails `Recoverable`, by `ws2_residue_distinct`." Exactly the demanded fact.
- Connection → "a `GaloisConnection` between two preorders, both non-trivial, whose interior round trip is not the identity at `bRefActive`." Exactly the demanded fact.
- Defect → "a `¬ Recoverable` two-region coalgebra `≈`-outside the mint's image, excluded by the diagonal link." The demanded fact, on the narrowed domain CD-1 already discloses.

No payoff survives the strip as something other than its named fact. No name does a proof's work.

**Cross-workstream laundering. PASS.** Every `Audit` field (`ws5.lean:76`) traces to a real WS1–WS4 theorem, and `ws5_audit_genuine_connection` consumes both halves of the split SR1-2 certificate rather than the weaker WS1 half alone. No field is discharged by an adjacent weaker fact.

**The verdict is computed, not hand-set. PASS.** `ws5_fork` cases on `∃ h₁, h₁ ≠ h₀` via `dite`; both branches are reached by theorems (`ws5_verdict_eq → Dual`, `ws5_verdict_degenerate → Total`), and the DUAL branch fires *because* the TOTAL target was refuted by `outWit`, not because it was preferred. `verdictOfFit` branches over a four-constructor data-level fork. The verdict tracks the carrier. But see **SR2-2**: nothing proves a carrier of either kind exists.

**The coda discipline. PASS.** Nothing in `formal/Series13/` decides the compass's content, convergence's direction, or the differentiating act. The layer-stability open is confined to comments (`ws5.lean:172-174`) and is prose, not a term. The single-layer/flat scope is stated and bounds the TOTAL branch honestly ("TOTAL AT THE FLAT LAYER"). CD-1 bounds the domain claim. These are the honest-reporting discipline working.

**The axiom-check status. See SR2-1.** The log is internally consistent but unreproduced.

**The terminal fork, stated plainly.** The code delivers **DUAL at the flat layer, on the narrowed `Lab` domain, on any carrier possessing a second hold** (`ws5_verdict_eq`), and **TOTAL at the flat layer on a single-hold carrier** (`ws5_verdict_degenerate`). Both are honestly labelled, both match their objects, neither is assumed, and the DUAL is not reached by closing the fork or faking the connection.

---

## 2. Findings

### SR2-1 (REAL, inherited from SR1-6) — sorry-freeness and axiom-cleanliness remain unverified by any review pass. Owner: Phase F.

Two consecutive review passes have now been unable to run Lean: no toolchain, and `leanprover-community.github.io` is outside the sandbox's network allowlist (`403 host_not_allowed`, verified this session). The charter's bar (§7 per the ledger) is "sorry-free and axiom-clean or it is not done," and that bar is currently certified only by a log the build session wrote about itself.

What this review verified mechanically, which is more than pass 1 did:
- **Source hygiene: clean.** No `sorry`, `admit`, custom `axiom`, or `native_decide` in `formal/` (all grep hits are docstring prose).
- **The log is internally consistent.** Extracted every `#print axioms` target from `AxiomCheck.lean` (30 declarations) and every record from `axiom-check-log.md` (30 records) and diffed both directions: **exact match, no gaps either way.** All 30 records show `[propext, Classical.choice, Quot.sound]`; **zero** non-standard records, no `sorryAx`, no custom axiom.
- The log's provenance note is specific and falsifiable (branch named, post-merge, states the strengthened non-triviality is included — and `ws2_mint_nontrivial` does appear in the log, consistent with a genuine post-Phase-E re-capture rather than a stale copy).

So the log is coherent and consistent with the source. It is still a self-report. **Correction owed:** re-run `lake build Series13 Series13.AxiomCheck` on a machine with the Mathlib cache before Phase F, and, if the coda's honesty claims are to be mechanical, record that no *reviewing* session has ever reproduced it.

**Recommendation (structural).** Two passes blocked by the same allowlist is a process defect, not bad luck. Either add `leanprover-community.github.io` (and the toolchain hosts) to the review sandbox's allowlist, or accept in writing that axiom-cleanliness is builder-attested and reviewer-unverified in this program.

### SR2-2 (REAL) — no carrier is ever proved to exist, so `Dual` is conditional on hypotheses nothing discharges. Owner: WS5 (claim), WS4 (witness).

Every headline in Series 13 is universally quantified over an arbitrary `dest : X → PkObj κ X` and takes the carrier's shape as a hypothesis. `ws5_verdict_eq` requires `(h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)`; `ws5_verdict_degenerate` requires `hone : ∀ h, h = h₀`. **Nothing in `formal/Series13/` ever instantiates a concrete `dest` and exhibits either carrier.** There is no `example`, no `Nonempty`/`Inhabited` instance, no witness carrier anywhere in the series (verified by grep across all five files).

`Hold dest := {p : X × X // p.2 ∈ (dest p.1).1}` is a subtype of edges, so a two-hold carrier plainly exists mathematically (any `dest` with two edges), and `MCar`/`labelLoop` show the machinery to build one is present. This is a gap in the *certificate*, not a suspicion that the hypotheses are unsatisfiable. But the distinction the series itself insists on elsewhere — a certificate, not an argument (§0.5, and the entire SR1-1/SR1-2 exchange) — applies here too. As built, `ws5_verdict_eq` says *if* a second hold exists *then* `Dual`. The ledger and the log both state the stronger-sounding "**Computed verdict: DUAL at the flat layer**" without the antecedent in view.

This matters most for the falsifiability triple. `ws5_verdict_not_total` etc. all route through `ws5_verdict_eq` and inherit its hypothesis; on a carrier where no second hold exists, they say nothing. And `FitFork.perInstance`/`ordersTrivial` are already unreachable-by-construction (SR1-9/SR1-10, cosmetically noted). So the falsifiability certificate is: *given a carrier of interest, the verdict isn't the other three* — with "a carrier of interest exists" left unproved.

**Correction owed (small, mechanical):** exhibit one concrete carrier with two distinct holds (a two-element `X` with a total `dest`, or a self-loop pair over `ULift Bool` — `labelLoop`'s carrier already has the shape) and instantiate `ws5_verdict_eq` on it as an `example`/theorem, making `Dual` unconditional at one named point; and one single-hold carrier for `ws5_verdict_degenerate`. Alternatively, state in the ledger and the log that the verdict is conditional on carrier hypotheses that the series does not discharge. Not SERIOUS: no claim is false as stated, the hypotheses are evidently satisfiable, and the theorems are honestly quantified. It is the gap between what the theorems say and what the ledger's headline says.

### SR2-3 (REAL) — `ws1-orders-design.md` still specifies a theorem that cannot be built, with no note. Owner: WS1 design.

Phase E correctly diagnosed that the design's `ws1_orders_lab_nontrivial` (witnessed by `mintL`, `ws1-orders-design.md:184-191`) is unbuildable: `mintL` lives in WS2, which imports WS1. The realization was split across WS1+WS2 and the ledger records this as a "design-realization note."

But the design doc itself is unchanged. It still presents the cyclic signature as the contract, and `ws1-orders-design.md:69` still names that theorem as "exactly the certificate." Protocol §1 makes designs "stable once committed" and says a design is "the contract a build is judged against" — a contract that cannot be satisfied by any build should not stay silently on the books, or the next reviewer re-derives this same finding from scratch (as this one did). Protocol §2 Phase C's rule is that a build discovering a broken design must "fix the design in place... or report the workstream Partial," and the charter-status note is neither of those two, though it is close to the first in spirit.

**Correction owed:** add a note *in `ws1-orders-design.md`* at the specified theorem recording that the signature is unbuildable (import cycle: WS1 cannot name WS2's `mintL`), and that the obligation is realized as `ws1_orders_lab_nontrivial` (antitone position) + `ws2_mint_nontrivial` (mint points), consumed jointly by `ws5_audit_genuine_connection`. Cross-reference CD-1's box or add CD-2. No charter edit is implicated; this is a design defect, disclosed but not recorded where it lives.

### SR2-4 (REAL) — §0.1 blindness is not mechanically honorable: the charter's criteria and its metaphysics are in one file. Owner: protocol / Phase F.

Protocol §0.1 and §5 seed the review with "the charter's success criteria" but **not** "the charter's motivating prose." In `charter.md` these are §6 and §8, adjacent in a single file. Any reviewer who reads the criteria from source reads the positioning prose in the same view. Pass 1 breached this and disclosed it; this pass read the code and formed all findings first, then hit §8 while reading §6, and discloses it above. Two for two.

The disclosure discipline is working — both reviews caught and reported their own breach, which is the system functioning. But the protocol asks for a condition its own artifact layout makes unachievable, and "the reviewer promises they read §6 and then stopped their eyes" is exactly the kind of unfalsifiable self-report this program otherwise refuses to accept anywhere else. §3's disclosure already concedes these are Claude-reviewing-Claude and leans on "objective anchors" for honesty; blindness should be an anchor, not an aspiration.

**Correction owed:** extract §6 to `spec/success-criteria.md` (or have Phase F generate a criteria-only excerpt), and have §5's table name *that* artifact as the review's seed. Then blindness is checkable by construction: the reviewer opens a file that does not contain the prose.

### Cosmetic / acceptable (none blocks)

- **SR2-5.** `ws5_fork`, `ws5_verdict`, and `ws5_audit` (the definitions the computed verdict flows through) are not themselves in `AxiomCheck.lean`, though the theorems about them (`ws5_verdict_eq`, `_degenerate`, the falsifiability triple) are, which transitively covers their axiom dependencies. Adding the three `def`s would make the record self-evidently complete. Also uncovered, all transcribed touchstones or minor: `ws1_coincidence_not_identity`, `ws1_diagonal_not_bisim`, `ws1_insp_not_surjective`, `ws1_recovers_static`, `ws1_two_halves`, `ws2_import_theorem_static`, `ws2_residue_is_import`, `ws3_dichotomy`, `ws4_labelLoop_not_recoverable`, `ws4_label_survives_quotient`, `ws4_recoverable_not_import`, `ws5_verdict_not_disconnected`, `ws5_verdict_not_partial`. The last two are odd omissions given `ws5_verdict_not_total` **is** checked.
- **SR2-6.** SR1-9/SR1-10 were closed by docstring notes only (`FitFork.perInstance` still has payload `True`; `ordersTrivial` still lacks the labelled-order disjunct). Correct call for a build where neither branch fires, and honestly noted — flagged only because if a successor series ever reuses `FitFork`, both are latent defects rather than cosmetic ones.
- **SR2-7.** `ws3_roundtrip_closure` states `readInsp ∘ mintL = id` as a two-sided `≤` rather than an `Antisymmetrization`/`Setoid` equality. Correct (the order is a preorder, not a partial order, so literal equality is unavailable) and the docstring says "up to the order." No action; noted so a later reader does not read it as a defect.

---

## 3. What survives cleanly

**The two pass-1 SERIOUS findings are genuinely closed, and closed the honest way.** SR1-1 and SR1-2 were the series' signature risk made concrete (the order solved-for-the-map), and the fix does what pass 1 asked: the antitone reference clause now fires non-vacuously in a certificate (`True → False`, on witnesses sharing `cT` by `rfl`, so the residue clause cannot be doing the work), and the mint points are certified where the mint actually lives. The dependency-cycle diagnosis behind the two-file split is **correct on the source** and is the rare case where "the design was wrong" is verifiable rather than convenient. Neither closed as a third adjacent theorem. §0.2a is satisfied.

**WS2 remains the strongest work in the series.** The transport genuinely runs on the diagonal, and the diagonal is genuine Cantor proved from nothing. `plainOf_coalg_val` proves rather than assumes the ground of exogeneity. `ws2_mint_not_plain_function` overshoots the contract in the honest direction.

**The fork stays open.** Grep-clean and structurally clean, two passes running. The defect locates and stops. The interpretive vocabulary is entirely in prose. This is the check the whole coda turns on and it is not close to failing.

**The connection is genuine and the defect is structural.** `ws3_roundtrip_not_identity` discharges both disjuncts of the fold rather than asserting the gap. `ws4_exclusion_structural` excludes by the label via the diagonal link, not by cardinality, universe, or typing — and testing up to `≈` (rather than the cheaper literal equality that would have made DUAL true by construction) is a place where the build chose the harder honest option unprompted.

**The verdict is computed and the losing branch is built.** `ws5_verdict_degenerate` exists and fires; TOTAL was attempted on `|Hold| ≥ 2` and refuted by `outWit`; the DUAL is the residue of a refutation, not a preference. The bounding is honest throughout: flat-layer scope named, CD-1 narrowing disclosed, layer-stability open kept in prose.

**Phase E's mechanical closures are all real.** The gate now covers Series 13 and runs green (executed, not assumed). CD-1 exists and says what SR1-3 asked. The ledger is swept.

---

## 4. Honest bottom line

**No SERIOUS findings. No finding recurs under §0.2a.** Both pass-1 SERIOUS findings closed as genuine **Fixed**, verified by unfolding the proof terms rather than by reading the ledger's claim about them. The five discipline checks — fork-open, genuine-connection, exogeneity, structural-defect, names-not-terms — all pass, and the genuine-connection check, which failed at pass 1, now passes for the right reason: a certificate that exercises the contested antitone clause, not a prose defense of it.

The mathematics under the verdict is sound as far as this reviewer traced it. `Dual` is earned, on the domain and at the layer the series openly says it is drawn: flat carrier, `Lab`-narrowed (CD-1), conditional on a carrier with a second hold.

**Four REAL findings, all bounded, none touching the verdict's substance.** Two are about the gap between what is *proved* and what is *attested*: SR2-1 (no review pass has ever reproduced the axiom check; the log is internally consistent and diffs exactly against `AxiomCheck.lean`, but it is the builder's self-report) and SR2-2 (no carrier is ever exhibited, so `Dual` is conditional on hypotheses nothing in the series discharges, while the ledger's headline reads unconditional). Two are about the process's own instruments: SR2-3 (the design still carries a signature that provably cannot be built) and SR2-4 (§0.1 blindness cannot be honored mechanically while the criteria and the metaphysics share a file).

There is a pattern worth naming across SR2-1, SR2-2, and SR2-4. This series' distinctive discipline is *certificate, not argument* — it is what made SR1-1/SR1-2 SERIOUS and what their fix delivered. That discipline is applied rigorously to the mathematics and less rigorously to the scaffolding around it: the axiom claim, the carrier's existence, and the reviewer's own blindness are each currently discharged by attestation. None is likely false. All three are the kind of thing this program, elsewhere, refuses to accept on someone's word.

**Recommended:** take SR2-2 and SR2-3 mechanically (both are small), resolve SR2-1 by either fixing the review sandbox's allowlist or recording in writing that axiom-cleanliness is builder-attested and reviewer-unverified, and put SR2-4 to Phase F as a protocol amendment. Since no finding is SERIOUS, protocol §2 Phase D directs the series to **Phase F (Close)** rather than another D→E loop; the four REAL findings can be closed in the course of Phase F. If DUAL is the recorded terminus, Phase F must state the one new permanent open — the classification of the out-of-image imports, open by the same theorem that locates them.
