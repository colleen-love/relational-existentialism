# Series 7 — Adversarial Series Review

*Reviewer: adversarial pass across the whole of Series 7 at once. Object of review: does the Lean
prove the theorems; do the theorems meet the designs' targets; do they satisfy the charter criteria
they claim — with no `sorry`, no custom axiom, no signature that quietly weakens the target.
Method: source audit of all seven workstreams plus `Series7.lean` and `AxiomCheck.lean`, the strip
test on every payoff, cross-workstream laundering, the coincidence/independence rule, the
trivialization verdict, and the axiom-check status.*

---

## Build & axiom-check status — READ THIS FIRST (a limitation of this review)

I could **not** compile the build in my environment. The Lean toolchain host
(`release.lean-lang.org`) is outside the network allowlist and there is no committed `.lake`
cache, so `lake build` / `lake env lean Series7/AxiomCheck.lean` could not run. **Everything below
about compilation and `#print axioms` is a source-level audit, not a machine-checked confirmation.**

Consequently the axiom-check remains, *from this review's vantage point*, a **static claim**: the
repo ships `spec/axiom-check-log.md` (46 theorems, standard three, regenerated 2026-07-10) and an
`AxiomCheck.lean` that would emit the record if run. I read the log and the `#print axioms`
targets; I did not re-run them. The source is consistent with the claim — no `sorry`, `admit`,
`native_decide`, `sorryAx`, `axiom`, `opaque`, `unsafe`, or `@[extern]` anywhere in the seven
files (grep-clean); the twelve `decide` calls are all on decidable `ULift Bool` (in)equalities and
are legitimate. But **"was `#print axioms` actually run?" I cannot confirm; a reviewer with the
pinned toolchain must re-run `AxiomCheck.lean` to close this.** I flag it rather than launder it.

One real gap in the check even as claimed: `AxiomCheck.lean` prints axioms for `ws7_verdict_eq`
but **not** for `ws7_verdict` itself, and not for `ws5_loophole_adjudication` or `ws6_universal`
(the three `def`-valued verdicts). Those are `def`s not theorems, so `#print axioms` is less
meaningful, but the *verdict constant the whole series reports* deserves an explicit line. Minor;
noted under COSMETIC.

---

## SERIOUS

**None at the term level.** I went looking for the two SERIOUS shapes specifically — a flagship
payoff laundering, or the engine painted on — and neither is present. Recording the negative
results explicitly, because they are the ones that would sink the series:

- **The engine is not painted on.** `WS1.hneRel_isBisim` proves the "both-atomless" relation
  `hneRel dest x y := SHNE dest x ∧ SHNE dest y` satisfies the *genuine* `IsBisim` predicate over
  the *actual* bounded-powerset destructor `dest : X → PkObj κ X`. `IsBisim` is the real
  back-and-forth condition on `(dest x).1`; `SHNE` is genuine hereditary non-emptiness (every
  `SReaches`-reachable state has non-empty successor set). Neither is rigged. The lemma is one
  honest relation and one honest line, exactly as the charter §3.1 advertises, and it is strictly
  more general than a terminal-coalgebra collapse. This is the load-bearing claim and it holds.

- **The flagship does not launder.** `WS2.ws2_import_theorem` quantifies over an *arbitrary*
  `dest : X → PkObj κ X` and concludes `¬(BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧
  ∃ x y, x ≠ y)`. The conclusion is real plurality (`∃ x y, x ≠ y`), not a definitional stand-in.
  The proof route (`ws1_atomless_bisim → hbehav → Subsingleton`) uses each hypothesis. The strip
  test passes on it (see below): drop `atomless` and `WS7.leafCoalg` is a genuine
  behaviorally-identified plural counterexample *with a leaf*, proved (`leafCoalg_behav`,
  `leafCoalg_has_leaf`). So the atomlessness hypothesis is load-bearing, not decoration.

The Import Theorem, its engine, and the two recovered collapses (`ws1_recovers_static`,
`ws1_recovers_dynamic`/`ws1_productive_unique`) are the deliverable and they survive the adversarial
pass cleanly.

---

## REAL (a genuine gap, correctly labelled once fixed)

### R1 — The drop-1 catalogue witness is only *first-level* nonempty, not atomless. `Owner: WS4.`

This is the one substantive term-level finding. The charter's ingredient (3) is **genuine
every-moment / hereditary atomlessness** (`SHNE`). The Import Theorem uses exactly that. But the
witness that is supposed to show "you can have (2)+(3)+(4) by dropping (1)" — the labelled
`labelLoop` — is proved only **first-level nonempty**: `ws4_labels_are_import` establishes
`∀ i, (labelLoop hinf i).1 ≠ ∅`, *not* `∀ i, SHNE (labelLoop hinf) i`. The docstring discloses this
honestly (interim-review C3: "ingredient (3) here is the MINIMAL first-level-nonempty witness ...
not a hereditary `SHNE`"). So the drop-1 row of the catalogue does **not** exhibit an object meeting
the theorem's own ingredient (3); it exhibits one meeting a weakened version of it.

Why REAL and not SERIOUS: the flagship (`ws2_import_theorem`) uses full `SHNE` and does not depend
on `labelLoop`; the drop-1 witness is a catalogue illustration, not a spine load-bearer. And the
weakening is labelled at the site. But the charter's WS4 target is "labels are the forced ingredient-1
drop," and a witness that quietly satisfies a *weaker* atomlessness than the theorem forbids does not
fully close the parallel: strictly, `labelLoop` might escape the theorem partly *because* it isn't
hereditarily atomless, muddying "it escapes *by dropping plainness*."

**Correction owed (prove that, don't lower the bar):** prove `∀ i, SHNE (labelLoop hinf) i` (the
label self-loop is manifestly hereditarily non-empty — its successor set is always the singleton
`{(i,i)}`, so this should be a short `SReaches`-induction mirroring `twoLoop_HNE`). Then restate
`ws4_labels_are_import` / `ws4_program_explained`'s drop-1 conjunct with hereditary `SHNE` on
`plainOf (labelLoop)`, so the witness meets ingredient (3) at the theorem's own strength. Until
then, the drop-1 row is "labelled + first-level-nonempty," which is a hair weaker than the charter's
"labelled + atomless."

### R2 — "Program explained" is proved for the free-label escalation only; the endogenous prior cases are reclassified, not catalogued. `Owner: WS4.`

`ws4_program_explained` is a real conjunction of real theorems, but what it *proves* is narrower than
the charter §5.4 / §8(iv) target "weights, labels, levels each the forced ingredient-1 drop of their
series." After the pass-2 alignment fix, the honest content is: (a) *free* labels are imports
(`ws4_free_label_is_import`, semantic — plain-bisimilar yet label-distinct); (b) `twoLoop` is a
drop-2 non-reduction; (c) the theorem predicts *a* drop on the plain toy; (d) S6 collapsed. The
Series 4 face `x↾(x,y)` is **reclassified as recoverable, hence not an import** (a leaf / faced
boundary), and Series 4's plurality is recast as a free-label *escalation*. Series 3 weights and the
Series 5 `Winf` index are **not** mechanized at all (S3 explicitly Partial; the index is asserted
"reuses the label mechanism" in prose). This is disclosed thoroughly in the status file and the
summary — it is correctly labelled — but the charter target as literally written ("the program
explained," all four series) is **Partial**, met on minimal witnesses for the free-label mechanism
and by reclassification/prose for the rest.

**Correction owed (relabel + prove-more where feasible):** keep the honest re-scoping already in
place (this is not goalpost-moving — the charter's own §4.1 semantic definition of "import" is the
fixed bar, and the build aligned to it). The residual owed is (i) a Lean witness that the Series 5
index is genuinely *non-recoverable* on some minimal tower-shaped carrier, or an explicit statement
that it is endogenous-hence-recoverable like the S4 face; and (ii) an honest one-line status entry
that Series 3 weights carry *no* Series-7 witness (currently "covered generically," which overstates
— the generic import witness is a free label, not a weight). Do not relabel "Partial catalogue" as
"program explained" in the headline; the summary already avoids this, the charter-status result
tracker mostly does, but `ws4_program_explained`'s *name* still asserts the full target.

### R3 — WS3 "trichotomy" is a dichotomy; the third and fourth kinds are prose. `Owner: WS3.`

Correctly labelled already, recorded here because it is a genuine gap against the charter's WS3
target ("the trichotomy of distinction ... the theorem's teeth"). On a single plain coalgebra the
proved statement is a **dichotomy** (`ws3_dichotomy`: leaf or import) — honestly renamed from
"trichotomy," with the "no fourth kind / teeth" framing explicitly withdrawn. The third kind
(`LeafyThreadDiff`) is contentful but lives only on `Proc` and its inhabitant (Ω vs the empty
process) is really a *leaf* difference, not the design's same-limit haecceity — disclosed
(`ws3_no_same_limit_haecceity` proves the genuine haecceity witness is structurally *absent*). The
candidate fourth kind (the faced boundary) is a **comment block**, no Lean content. So the charter's
"exhaustive ... every distinction is a leaf, import, or history" is **Partial** across any
construction and the "teeth" (exhaustiveness) is an acknowledged open, not delivered.

**Correction owed:** none beyond what's done — this is the pre-registered honest Partial (charter
§5.3, §9). The relabel from trichotomy→dichotomy is exactly the right move and is in place. The one
thing owed is to keep the charter's §5.2 "Trichotomy (target of WS3)" from reading as *delivered* in
any summary; the current docs correctly call it Partial. Do not let a future revision quietly promote
`ws3_dichotomy` back to "the trichotomy."

---

## COSMETIC / ACCEPTABLE

- **C1 — `ws2_non_circular` conjunct 1 is `Iff.rfl` on a definitional alias.** `NoImportedAtom :=
  BehaviorallyIdentified` (literal `def`), so `NoImportedAtom dest ↔ BehaviorallyIdentified dest`
  is `Iff.rfl` and carries zero information. This is *acknowledged* in WS7's self-audit ("NC1 ...
  deliberately NOT counted as a Lean anchor ... it would be `Iff.rfl` on a definitional alias") and
  the real non-circularity weight is carried by `ws2_escapes_are_imports` /
  `ws4_free_label_is_import` (genuine theorems). Acceptable *because it is disclosed and not
  load-bearing*, but the conjunct's presence in `ws2_non_circular` still reads as if it were
  evidence. **Correction owed:** drop the `Iff.rfl` conjunct from the theorem statement (it proves
  nothing) or annotate it in-signature as the definitional identity it is, so the theorem's
  content is exactly the escape refutation.

- **C2 — the "atom OR will" capstone is prose, not a formal disjunction.** The only Lean content is
  `att_cannot_distinguish_atomless_histories`, a one-line true theorem (an `att : Proc κ → Q`
  returns equal values on productive threads, because they are *equal* — `ws1_productive_unique`).
  That is correct and non-vacuous. But the headline philosophical claim ("the price is an atom or a
  will; the formalism cannot decide which") lives entirely in the docstring. Honestly framed
  ("that silence is the result, not a gap"), so ACCEPTABLE — but it must never be cited as a
  *proved* disjunction. It is a true lemma plus an interpretation.

- **C3 — `verdict` takes the audit certificate as an unused (`_cert`) argument.** The wiring is
  nonetheless real: `verdict` *requires* an `Audit κ hinf`, so `ws7_verdict = verdict (ws7_audit
  hinf) false` cannot be formed unless `ws7_audit` (every field a theorem) typechecks, and
  `ws7_verdict_eq`'s `rfl` transitively depends on it. Break any audit field and the verdict fails
  to build — the S1 fix is genuine. The `_` underscore is cosmetically alarming (it *looks* like
  the certificate is ignored) but the dependency is through type-formation, not use. ACCEPTABLE;
  optionally rename to `cert` and add a trivial `have := _cert` to make the dependency visually
  obvious.

- **C4 — the `exhaustive : Bool` flag is hand-passed `false`.** `ws7_verdict` passes `false`
  literally, so `payoffsEstablished` vs `importForced` is gated on a hand-set Boolean, not on a
  proof of exhaustiveness. This is *correct* (exhaustiveness across any construction is the
  un-rangeable quantifier, genuinely open) and honestly the whole point of `payoffsEstablished` —
  but it means the verdict's *ceiling* is manually chosen, not derived. Fine as-is given the open
  is real; noted so no one reads `importForced` as "one theorem away."

- **C5 — AxiomCheck omits the verdict `def`s.** `#print axioms` is run over `ws7_verdict_eq` but not
  `ws7_verdict`, `ws5_loophole_adjudication`, or `ws6_universal`. Minor (they're `def`s); add the
  lines for completeness.

---

## What survives cleanly

- **The engine — `WS1.ws1_atomless_bisim`.** On *any* plain `PkObj κ`-coalgebra, any two hereditarily
  non-empty states are related by a genuine bisimulation (the both-atomless relation). Real,
  general, one line. This is the program's Parmenides collapse at the generality the charter
  promised, and it is the true root of the static and dynamic collapses.

- **The Import Theorem — `WS2.ws2_import_theorem` and `ws2_import_theorem_static`.** Genuine,
  non-vacuous, arbitrary `dest`, real plurality in the conclusion, every hypothesis load-bearing.
  The strip test passes (leaf counterexample when atomlessness is dropped; label counterexample
  when plainness is dropped; `twoLoop` when behavioral identity is dropped). The central deliverable,
  and it is an impossibility — first-class in this program.

- **The recovered instances.** `ws1_recovers_static` (abstract behavioral-identity form subsuming
  `νPk`) and `ws1_productive_unique` (the dynamic collapse, transcribed) are both genuine and
  correctly presented as *instances* of the one engine.

- **The strip witnesses are real terms, not flags.** `WS7.leafCoalg` (behaviorally-identified,
  plural, *with* a leaf — `leafCoalg_behav` + `leafCoalg_has_leaf`), `labelLoop` (survives the
  label quotient), `twoLoop` (plain, atomless, bisimilar-yet-unequal). The strip ledger's
  cleanliness is contingent on these typechecking, which is the right design (the pass-1 self-
  fulfilling Bool ledger is genuinely fixed).

- **The semantic import test — `ws4_free_label_is_import`, `ws4_recoverable_not_import`,
  `ws4_recoverable_atomless_collapses`.** This is the pass-2 fix and it is substantive: "import" is
  now the charter's §4.1 *semantic* predicate (a coordinate the plain relating cannot recover), not
  "a `Q` in the signature." The recoverable-label collapse is a clean general theorem. The
  reclassification of the Series 4 face as recoverable-hence-not-import is mechanized on minimal
  witnesses (`facedLoop` recoverable, `labelLoop` not).

- **The coincidence/independence check passes where it applies.** The three kinds are proved to have
  different extensions (`ws3_leaf_not_import`, `ws3_import_not_leaf`) — a genuine non-partition, not a
  definitional carve-up. The "forced" collapse (engine) does not unfold to its "definitional"
  partner: `BehaviorallyIdentified` is the founding predicate, and the escape is refuted by a real
  theorem (`ws2_escapes_are_imports`), not by a rigged `atomless`. The one definitional coincidence
  that *does* exist (`NoImportedAtom = BehaviorallyIdentified`) is openly declared and pulled out of
  the load-bearing anchors (C1).

- **Honesty of the ledger.** The status file and summary disclose the discounted interim review, the
  pass-2 misalignment, the first-level-vs-hereditary weakening, the un-transcribed carriers, the
  prose-only fourth kind, and the atom-or-will fork as interpretation. The self-review discipline is
  real; findings were folded in by proving more or relabelling, and I did not catch a case of a
  shortfall being renamed as the goal.

---

## Trivialization verdict

**Not trivial.** The characteristic risk the charter names (§8) is that "atomless" and "no import"
were *defined* to make plurality impossible. They were not. `SHNE` is honest hereditary
non-emptiness; the engine is a real bisimulation over the real functor; the atomlessness hypothesis
is provably load-bearing (strip it → `leafCoalg` counterexample); and the escapes are refuted as
theorems. The theorem says something true about plain relating that the definitions do not trivially
encode. The `Circular` arm is live and correctly *not* taken.

The honest deflation is smaller and already labelled: (i) the *catalogue* half of the program
(WS4's "explains all four prior series") is Partial — proved for the free-label mechanism, reclassified
for S4, prose for S5, absent for S3; (ii) the *exhaustiveness* half (WS3's teeth) is the acknowledged
un-rangeable open; (iii) the drop-1 witness meets a first-level-nonempty weakening of ingredient (3)
(R1). None of these touches the impossibility itself.

## Axiom-check verdict

**Static, pending re-run.** The claim (sorry-free, standard three, 46 theorems) is *consistent* with a
clean source audit — no `sorry`/`axiom`/`native_decide`/`sorryAx`/`opaque`/`unsafe` anywhere; `decide`
only on decidable `Bool`. But I could not run `AxiomCheck.lean` (toolchain host blocked, no cache), so
I cannot certify it was actually machine-checked at this commit. A holder of the pinned Lean 4
v4.15.0 / Mathlib v4.15.0 toolchain should run `lake env lean series-7/formal/Series7/AxiomCheck.lean`
and confirm the log; add the three missing verdict-`def` lines (C5) while doing so.

---

## Honest bottom line

The spine of Series 7 is real and clean. The engine (`ws1_atomless_bisim`), the Import Theorem
(`ws2_import_theorem`), and the two recovered collapses are genuine, non-vacuous, and survive the
strip test, the laundering test, and the coincidence test. The signature risk — a theorem true only
because its definitions excluded the escapes — is refuted, and refuted the right way (by exhibited
counterexample terms, not by fiat). **The verdict `payoffsEstablished` is the correct verdict**, and
the reasons it is not `importForced` are exactly the two the charter pre-registered: the trichotomy's
exhaustiveness is an un-formalizable quantifier, and the interpretive catalogue is Partial.

The gaps that remain are in the *interpretive skirts*, not the impossibility: the drop-1 witness
weakens ingredient (3) to first-level-nonempty (R1, prove `SHNE`), the "program explained" theorem
proves the free-label mechanism and reclassifies/omits the rest (R2, keep the honest re-scope and
stop the *name* asserting the full target), and the "trichotomy" is a dichotomy plus prose (R3,
already relabelled). The `Iff.rfl` non-circularity conjunct (C1) and the prose "atom-or-will"
capstone (C2) should never be cited as evidence, and they mostly are not.

The one thing this review cannot sign off on is the machine-check itself: **I read the axiom log; I
did not reproduce it.** Treat the sorry-free / axiom-clean status as verified-in-source and
pending-re-run, not as independently confirmed here.

Net: a genuine impossibility theorem, honestly scoped, with a self-review discipline that mostly
polices itself — and three correctly-labelled Partials plus one small term-level weakening (R1) that
are owed a prove-more, not a lower-the-bar.
