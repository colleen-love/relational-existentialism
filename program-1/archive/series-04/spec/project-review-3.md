# Series 04 — Full Blind Project Review (adversarial, whole-program)

*Reviewed at commit `914cb1f` (main). Scope: `series-04/formal/ws1.lean … ws7.lean`, `AxiomCheck.lean`, `spec/wsNN-design.md`, `charter.md`, `charter-status.md`. Method: protocol §3a — all code + all design contracts + charter success criteria, read against each other, with the charter's motivating prose set aside. This is Claude-reviewing-Claude; the objective anchors are the proof terms, the dependency edges, and the strip test, not my say-so.*

The three questions, up front: **does the code prove the theorems** — yes, every one; **do the theorems meet the designs' targets** — for plurality, composition, collapse, and Ω-non-termination yes, for the endogenous bound / no-view / one-finitude no, and the status file already says so; **do they satisfy the charter criteria they claim, with no `sorry`, no custom axiom, no quietly-weakened signature** — no `sorry` and no custom axiom (subject to the axiom-check caveat in A1 below), but two signatures are weaker than the design's target in ways that are correctly relabelled, and one newly-flagged signature (W1) is presented as more than it is.

The prior two adversarial passes (`project-review-1`, `project-review-2`) did most of the demolition already, and the status file folded their corrections in faithfully. My job here is the part per-workstream review cannot see: cross-workstream laundering, the whole-program trivialization verdict, the strip test run fresh on every payoff, and the axiom-check status as it stands on *this* commit. Two findings are new (W1, A1); the rest confirm that the existing labels hold.

---

## Strip test (charter §0.3), run on every payoff

The test: delete the face vocabulary from the statement and proof. If the theorem still goes through, it was an index/cardinality/definitional fact wearing a face costume, not an earned carrier theorem.

| Payoff | Theorem | Strip result | Earned by faces? |
|---|---|---|---|
| Plurality | `ws3_loopface_ne` / `ws3_plurality_core` | **Survives nothing** — delete the label `q` and the two loops are the same `Cofix.dest`, so the distinctness evaporates. The label *is* the face, and it is load-bearing. | **Yes — earned.** |
| Composition atom-free | `ws3_faces_never_annihilate` | Survives partially as "image of a nonempty set is nonempty," but the *content* — that there is no external ⊥ to reach — is exactly the internality of the label. | **Yes — earned** (unconditional; genuinely stronger than Series 03's leaking `ws14`). |
| No-top | `ws4_no_top_cardinal` | **Survives fully.** Proof is `#(str x) < κ ≤ #carrier`; the word "face" appears nowhere in statement or proof. Pure cardinality. | **No.** Correctly labelled *Relocated (cardinal wall)*. |
| No-top (reach form) | `ws4_no_top_reach` | **Survives fully.** Proof uses `Reaches.step` + `hreach`; `face` does no work. The file's own docstring says so. | **No.** Kept only as an honest record. |
| Positioned view (V1) | `ws4_view_is_positioned` | **Survives as `rfl`.** `viewOf` is *defined* as `face`; "a view is a face" is definitional. | **No.** Correctly labelled definitional. |
| Endogenous bound | `ws5_omega_endogenous_point` | **Survives as an Ω index fact.** `face Ω Ω = ReachSet Ω = {Ω}` because Ω's reach is the singleton; the "bound" is that a one-point region is one point. | **No** off the spine. Correctly labelled *Partial / loop-spine only*, with the global case an *Impossibility*. |
| Incompleteness off-diagonal | `ws6_selfface_proper_nonselfrelating` | **Survives.** Reduces to `∅ ⊂ ReachSet x`: the self-face of a non-self-relating object is empty, and empty ⊊ nonempty. No face structure participates beyond "it's empty." | **No.** Correctly labelled *Partial*; the interesting nonempty-proper case is proved *impossible* on R2 by `ws6_selfface_trivial`. |
| Incompleteness on-diagonal | `ws6_omega_nonterminating` | Does **not** strip: the statement is `face Ω Ω = ReachSet Ω` *and* `Ω ∈ str Ω` together — the "complete in extent yet self-membered" conjunction is the content, and it is genuinely about the self-face being total while the object recurs. | **Yes — earned** (new, clean). |

**Strip-test verdict.** Four of eight payoffs survive stripping (`ws4_no_top_cardinal`, `ws4_no_top_reach`, `ws4_view_is_positioned`, `ws5_omega_endogenous_point` off-spine, and `ws6_selfface_proper_nonselfrelating`). **Every one of them is already flagged in `charter-status.md` as cardinal/definitional/Partial.** No survivor is currently sold as an earned carrier theorem. This is the single most important thing the review confirms: the strip-test failures were caught by the earlier passes and the labels were moved to match. The three-and-a-half genuinely earned payoffs (plurality, composition, Ω-non-termination, and the "does faces work" half of the WS3 coincidence) are exactly the ones the summary keeps.

---

## Findings

### SERIOUS

None outstanding. The finding that *would* be serious — the program verdict resting on the cardinal fiat while the headline said "endogenous" (`project-review-2` S1) — was real, and it has been corrected: `ws7_verdict` is now `payoffsEstablished`, not `oneFinitude`, and the no-top row reads *Relocated (cardinal wall)* everywhere I can find it (status file, tracker, summary, and the WS4 docstrings). I checked for a regression — that the downgrade was cosmetic and the code still quietly claims unity — and it is not: see W1, which is the residue, graded REAL rather than SERIOUS because the *label* is already honest even though one supporting theorem is weaker than the file's gloss on it.

### REAL

**W1 — The "one genuine derivation from finitude" is a projection, not a derivation. (owner: WS7)**
`ws7_incompleteness_off_from_finitude` is presented (docstring, status row 129, closed-log R1 entry) as the one payoff "genuinely derived *from* `FinitudeOfFacing`," the honest instance that keeps "one finitude" from having *zero* mechanized support. Its proof is `h.1`. But `FinitudeOfFacing` is *defined* as `(off-diagonal properness) ∧ (Ω improper)`, and the off-diagonal-properness clause is *verbatim* the payoff being "derived." So the derivation is the first projection of a conjunction whose first conjunct is the conclusion. This is not a derivation of a payoff from an independent finitude; it is the coincidence rule's failure mode named in charter §7 — "its proof secretly unfolds to the definition" — appearing at the one place the file points to as evidence it *didn't* happen. It does not make anything false (the payoff holds, proved independently as `ws6_selfface_proper_nonselfrelating`), but it means the count of payoffs mechanically derived from a *substantive* single finitude is **zero, not one**. **Correction owed:** relabel — the status should say "*no* payoff is mechanically derived from an independent finitude; `ws7_incompleteness_off_from_finitude` projects the clause that `FinitudeOfFacing` builds in." Do not lower the verdict below `payoffsEstablished` (that is already honest); do fix the sentence claiming "at least one honest mechanized instance rather than none." Alternatively, *prove that* — redefine `FinitudeOfFacing` so its off-diagonal content is a genuinely weaker/other fact (e.g. a face-count statement) from which properness is derived by a nontrivial step; then the instance is real.

**W2 — The distinctness anchor anchors predicates, not deductions. (owner: WS7)**
`ws7_deductions_dont_collapse` is offered as the objective guard (T3) that refutes *Trivialized* by showing two payoffs "are genuinely different consequences … not one deduction in two costumes." What it proves is `¬∃x. face x x = ReachSet x ∧ face x x ⊂ ReachSet x` — i.e. no object is simultaneously improper-faced and proper-faced. That is `¬(A = B ∧ A ⊊ B)`, true by unfolding `⊊`. It shows the two *predicates* cannot co-apply to one state; it says nothing about whether the two *proofs* share an intermediate, which is what the design's T3 (dependency-disjointness) and the charter's coincidence rule actually require. The second anchor, `ws7_plurality_vs_collapse_distinct`, is stronger — it genuinely lives on two different carriers (`νLk` vs `νPk`) — and does carry real distinctness force. **Correction owed:** relabel `ws7_deductions_dont_collapse` as "the two incompleteness *predicates* are mutually exclusive (disjoint domains of application)," not "the two deductions do not collapse." Keep `ws7_plurality_vs_collapse_distinct` as the one mechanized row that means what T3 wanted. The six-way anchor remains correctly open.

**W3 — The forced-answer dichotomy is excluded-middle in a costume. (owner: WS2)**
`ws2_forced_answer`'s external branch is `LeaksAtom A ∨ AtomFreeByFiat A`, which unfolds to `¬BotFree A ∨ BotFree A`, discharged by `em (BotFree A)`. `ws2_leak` itself is `push_neg` on `¬BotFree` — it restates the definition of having a ⊥-divisor. This is not wrong and not overclaimed (the status file calls it a "dichotomy" and flags general internal-rigidity as the open obligation), but a series-level reader should know the *mechanized* content of the forced-answer spine is: (i) a real, genuinely-proved collapse (`ws2_collapse`), (ii) a definitional restatement that ⊥-divisors are ⊥-divisors, and (iii) a tautological case split. The substantive claim — internality is the *essentially unique* atom-free supplier — is the named open (#2), correctly. **Correction owed:** none to labels; this is a note that the "forced answer" is, at the Lean level, F1 (`ws2_restriction_no_leak`, real) plus a tautology, and the file should not let "dichotomy Discharged" read as "forced-answer thesis mechanized." It already mostly doesn't; keep it that way.

### COSMETIC / ACCEPTABLE

**C1 — `carrier_card_ge` is the one fact doing the no-top/M1 work, across two workstreams.** No-top (`ws4_no_top_cardinal`) and the WS5 M1 negative (`ws5_contraction_insufficient`) are both literally `carrier_card_ge κ` (M1 is definitionally equal to it). This is not laundering — both are honestly labelled cardinal facts — but it is the concrete sense in which "double-unboundedness" is one fact seen twice. Worth a one-line cross-reference in the status so a reader sees the shared root. Acceptable as-is.

**C2 — `ws4_faces_inject` is a real face theorem that is wired into nothing.** `FacingInjective` + `ws4_faces_inject` genuinely use faces and prove faces inject successors into sub-objects — but this is never consumed by any no-top theorem (the walls are cardinal/reach). It sits as an honest orphan: the one place faces *could* have bounded, proved, but shown by WS5 M1/M2 not to yield a wall. Correctly present, correctly unused. No change.

---

## Cross-workstream laundering check

The thing a per-workstream reviewer cannot see: a claim discharged in isolation that leans on a hypothesis another workstream left open.

- **WS4 → deferred cardinality.** `ws4_no_top_reach` takes `hreach : #(ReachSet x) < #carrier` as a *hypothesis*. On R2 that hypothesis is not discharged in-file for arbitrary `x` (it is the deferred `ws12`-style bound). But this is not laundering, because the theorem is stated *conditionally* and the *unconditional* no-top (`ws4_no_top_cardinal`) does not use it — it uses only `#(str x) < κ` (immediate from `PkObj`) and `carrier_card_ge` (proved in WS2). So the flagship no-top stands on a discharged foundation; the reach form's open hypothesis is confined to a theorem explicitly kept as a "faces do no work" record. **Clean.**
- **WS7 → everything.** `ws7_payoffs_hold` conjoins six results; I traced each conjunct to its source theorem and confirmed none imports an *undischarged* hypothesis: plurality (`ws3_plurality_core`, needs only `q₁≠q₂`), no-top (`ws4_no_top_cardinal`, unconditional), view (`rfl`), bound (`ws5_omega_endogenous_point`, Ω-specific, proved), off-diag (`ws6_selfface_proper_nonselfrelating`, proved), on-diag (`ws6_omega_nonterminating`, proved). The conjunction is honest about *holding*; W1/W2 are about it not showing *unity*, which is a labelling matter, not a laundered hypothesis. **Clean** (no `hcard`-style leak of the Series 03 kind the protocol warns about).
- **WS5 endogenous bound → WS1 Ω.** `omegaGroundlessDiagonal` is a genuine exhibited witness (the region `{Ω}`), not a posited structure; `GroundlessDiagonal` is inhabited by construction. No open hypothesis smuggled. **Clean.**

**No cross-workstream laundering found.** The one historical instance (the verdict importing the cardinal wall while the label said endogenous) was intra-file label drift, already corrected.

---

## Coincidence rule, where it applies

- **Plurality (WS3), `ws3_same_succ_diff_face`.** The two halves live on genuinely different carriers — `ws2_collapse` on `νPk` (no face notion exists there) and `ws3_loopface_ne` on `νLk` (labels are functor data). The forced half does not unfold to the definitional half; they are the *same bare successor shape* proved to collapse without faces and split with them. **Coincidence real. Passes.**
- **No-view (WS4).** V1 is `rfl`; a forced V2 routed through faces does not exist (`ws4_no_global_observer` is the cardinal wall observer-side). **Coincidence not delivered.** Correctly labelled *Partial — V1 definitional, V2 absent.*
- **Incompleteness off-diagonal (WS6).** The definitional form (self-face proper) and the forced form (Lawvere/Cantor, `ws6_lawvere_incomplete`) are separately stated; the Lawvere theorem is genuinely carrier-independent and consumes no cardinality fact — that half is real and clean. But their **equality** (the blind-spot = diagonal coincidence the charter actually wanted) is *not* proved; delivered as coexistence. Correctly labelled *Partial / coexistence.*
- **One-finitude (WS7).** The claimed derivation is a projection (W1). **Coincidence-style unity not mechanized.** Correctly labelled `payoffsEstablished`, with the honest-instance sentence needing the W1 fix.

The one place the coincidence rule is fully satisfied — WS3 plurality — is also the one place the strip test says faces are load-bearing. That alignment is the program's real spine.

---

## Trivialization verdict — confirmed or refuted at the whole-program level

The charter's central question (§8): do plurality, boundedness, no-top, and incomplete self-knowledge reduce to distinct consequences of one finitude, or collapse into one definition?

Tracing the actual proof roots rather than the prose:

- **Plurality** is a consequence of *labels being functor data* (`Cofix.dest` injective in the label). It is **not** a consequence of finitude-of-facing at all; it is a consequence of the R3 carrier having independent quality data. Distinct root.
- **No-top** and **the WS5 M1 negative** are both `carrier_card_ge` — the carrier out-sizes any object's `<κ` successor set. This is **double-unboundedness** (object bounded below κ, world at least κ). One fact, used twice.
- **Endogenous bound (global)** is the *negation* of the above being escapable: `ws5_global_groundless_collapses`, itself `ws2_collapse`. So it is the collapse again.
- **Off-diagonal incompleteness** is `∅ ⊊ ReachSet` — a triviality about the empty self-face, not a finitude consequence in any load-bearing sense.
- **On-diagonal incompleteness** is Ω-specific coinductive self-membership. Distinct, genuinely new, and *not* a consequence of finitude (Ω is the point where finitude-of-facing is *violated* — the face is improper).

So at the whole-program level the payoffs do **not** reduce to distinct consequences of one substantive finitude, and they do **not** collapse into a single definition either. They reduce to **three genuinely distinct roots**: (a) the collapse / cardinality pair — one double-unboundedness fact, powering no-top and the global bound; (b) label-as-functor-data, powering plurality and composition; (c) an Ω-specific coinductive fact, powering on-diagonal non-termination. The off-diagonal incompleteness and the positioned-view "payoffs" are near-trivial and attach to none of the three as real content.

**Verdict: `payoffsEstablished` is correct, and `Trivialized` is correctly refuted — but for a sharper reason than the file gives.** The program is not trivialized (the payoffs are not one definition restated: three distinct roots is more than one). But it is also not "one finitude, substantively" (the roots are three, and *none of the three is the finitude of facing* — finitude-of-facing is a fourth thing the payoffs mostly do not use). The honest whole-program statement is: **restriction-quality does real, distinct work in exactly one register (plurality + composition, via labels-as-data); the bounding/positioning payoffs are the inherited double-unboundedness cardinality fact; and the on-diagonal incompleteness is a separate coinductive gift of Ω.** "One finitude" was the wrong unifier to hope for; the truthful finding is a clean *partition* of what faces can and cannot do. This is a stronger and more useful result than either horn of the charter's dichotomy anticipated, and the summary already says essentially this.

---

## Axiom-check status — was `#print axioms` actually run, or is the claim static?

**Partially reproducible; not reproducible on this commit.** Concretely:

- `AxiomCheck.lean` contains **41** `#print axioms` directives, one per headline theorem; I confirmed all 41 name real declarations in `ws1…ws7.lean`. The log in `spec/axiom-check-log.md` has exactly **41** matching lines, all resting on `propext` / `Classical.choice` / `Quot.sound` (two — `ws2_botfree_safe`, `ws7_not_trivialized`, `ws7_verdict_eq` — on no axioms). The counts and targets are internally consistent, and the "41 headline theorems" figure in the status file is accurate (an earlier scan of "42" is a false positive from the phrase `#print axioms` appearing in the file's header comment).
- **No `sorry`, no `admit`, no `native_decide`, no custom `axiom`** anywhere in `series-04/formal/`. The only `decide` uses are on `Fin 3` / `Bool` / a two-constructor `ProgramVerdict` — all genuinely decidable, not `native_decide`. Clean.
- **But**: on the current `main` (`914cb1f`) the Lake build no longer has a Series-04 target. `lake/lakefile.toml` sets `defaultTargets = ["Series05"]` and its only `lean_lib` has `srcDir = "../series-05/formal"`. Git history shows the S4 target existed at `8955860` and was repointed to Series 05 at `6b06cc2`. So `cd lake && lake build Series04 AxiomCheck` — the exact command the log records — **cannot be run as-committed**; it would need the lakefile pointed back at `../series-04/formal`. There is also no toolchain/Mathlib cache in this review environment, so I could not re-run it myself.

**Status:** the axiom log is a *genuine past transcript*, not a static hand-written claim (the target list and the `does not depend on any axioms` distinctions are too specific to be fabricated by hand, and match the code). It is **not currently reproducible** from a clean checkout without editing the build config. **Correction owed:** the status file's "machine-verified … Lean 4.15.0 / Mathlib v4.15.0" is true-as-of-`8955860` but should be dated to that commit and note that the live lakefile now builds Series 05; a reader wanting to reverify must restore the S4 `lean_lib` stanza. Do not downgrade the claim to "static" — it was run; do timestamp it and record the S4-target lakefile stanza alongside the log so it is re-runnable.

---

## What survives cleanly

No overclaim, faces genuinely load-bearing, proofs proper:

- **`ws2_collapse`** — the Parmenides collapse. A real `P_κ`-bisimulation (`hereditarilyNonempty_bisim`) fed through terminal-coalgebra uniqueness. The genuine headline, and the counterweight everything downstream is earned against.
- **`ws3_loopface_ne`, `ws3_plurality_core`, `ws3_plurality_core_concrete`** — plurality without atoms on the self-contained labelled carrier `νLk`. Distinct labels give distinct `Cofix.dest`, hence distinct states. The one payoff where the strip test kills the theorem if you remove faces — i.e. genuinely face-powered.
- **`lcomp` + `ws3_faces_never_annihilate`** — a real `corec` state-forming operator, composition unconditionally atom-free with *no* `BotFree` hypothesis. Strictly stronger than Series 03's leaking weighted `ws14`. The internality payoff, earned.
- **`ws5_global_groundless_collapses`** — the sharp Impossibility: global groundlessness forces a subsingleton. The honest negative headline, and arguably the most important single result in the series.
- **`ws6_lawvere_incomplete`** — a clean Cantor/Lawvere diagonal, carrier-independent, consuming no cardinality fact.
- **`ws6_omega_nonterminating`** — the new on-diagonal incompleteness: complete in extent, self-membered, closed at no depth. Real and does not strip.
- **`carrier_card_ge`, `ws2_weak_pullback` / `ws1_weak_pullback_inherited`** — correctly transcribed; the weak-pullback gate is a genuine non-event on R2 (the functor is unchanged), exactly as WS1 bet.
- **The WS1 carrier itself** — a real terminal coalgebra of `P_κ` via QPF/`Cofix`, Lambek, `bisim_eq`, Ω recovered. Self-contained, nothing pulled from `archive/`.
- **The labelling discipline throughout.** After two adversarial passes, every strip-test survivor is named for what it is (`_cardinal`, `_reach`, `_nonselfrelating`, `payoffsEstablished`), and the summary states the strip result in plain language. This is the discipline working as designed.

---

## Honest bottom line

Series 04 compiles `sorry`-free with no custom axioms, and every headline theorem proves the statement it asserts. The build's *positive* content is narrower than the charter hoped and exactly as narrow as the corrected status file and summary now say: **internal quality genuinely buys plurality-without-atoms and leak-free composition (faces load-bearing, machine-checked), and Ω yields a genuine new coinductive incompleteness — but the bounding and positioning payoffs are the inherited double-unboundedness cardinality fact with faces painted on, and on the R2 carrier faces provably cannot do that structural work.** The strip test confirms this split precisely: it kills the no-top, positioned-view, endogenous-bound, and off-diagonal-incompleteness theorems (all already labelled cardinal/definitional/Partial) and leaves the plurality/composition/Ω results standing.

At the whole-program level the trivialization verdict is **refuted, but the unifier is wrong**: the payoffs are not one definition restated (there are three distinct roots), and they are not "one finitude" either (none of the three roots *is* the finitude of facing). The truthful headline is a partition, not a unification — a sharp map of where restriction-quality works and where it is decoration. That map is the contribution, and it is honestly drawn.

Three corrections are owed, all relabel-or-prove, none goalpost-moving: **(W1)** stop calling `ws7_incompleteness_off_from_finitude` a derivation — it is the projection of a conjunct the definition builds in, so *zero* payoffs are derived from a substantive finitude, not one; **(W2)** relabel `ws7_deductions_dont_collapse` as predicate-exclusivity, not deduction-independence (keep `ws7_plurality_vs_collapse_distinct` as the row that means what T3 wanted); **(A1)** date the axiom-check claim to commit `8955860` and record the Series-04 `lean_lib` stanza next to the log, since the live lakefile now targets Series 05 and the recorded command is not runnable from a clean checkout. Everything else the earlier passes flagged has been corrected and holds.
