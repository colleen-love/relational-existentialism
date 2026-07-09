# Series 5 — Blind whole-series review (`series-review.md`)

*Adversarial batched review, Phase D. Regenerated against the Phase-F + pass-2 build
(branch `claude/series-5-lean-setup-uhzg6i`). Reviewer saw the built code, the design
signatures/outcome classes, and the charter success criteria. This pass was run as an
independent read of the Lean source, theorem by theorem, across all seven workstreams at
once. Disclosure carried forward: this is Claude-reviewing-Claude; the objective anchors
are the dependency graph, the strip tests, the distinctness ledger, and the axiom record.*

**Reviewer's build note (bears on S-AX below).** The pinned toolchain
(`leanprover/lean4:v4.15.0` + Mathlib `v4.15.0`) was **not** available in the review
environment, and Mathlib could not be fetched (restricted network). So the compile and the
`#print axioms` emit were **not** re-run this pass. Every "the code proves X" judgement below
is from *reading the proof term*, not from a verified build. The textual audit (no `sorry`,
no `admit`, no `axiom`, no `native_decide` outside doc-comments) and the import-closure audit
(nothing from `series-4/` or `archive/`) **were** run and pass.

---

## Bottom line up front

The program's own headline — **`payoffsEstablished`, not `oneDoubleUnboundedness` and not
`trivialized`** — is the correct verdict, and the build supports it. There is **no SERIOUS
finding**: no flagship payoff is laundering an open hypothesis while being reported as
discharged, because every payoff that leans on an open obligation is *already labelled* as
leaning on it, in the code and in `charter-status.md`. The build is genuinely `sorry`-free
and carries no custom axiom (subject to S-AX: the axiom emit was not re-run here). The real
mathematical content that survives cleanly is substantial (see "What survives cleanly").

What remains is a cluster of **REAL** items, every one of which the project has *already
labelled correctly* — they are terminal Partials / open obligations, not mislabelled
discharges. The single item that a blind reviewer would independently escalate toward
SERIOUS, and that the design did *not* pre-authorize as acceptable, is **R-WS4/6**: the
"earned" no-view payoff V3 does not in fact earn its face structure — it is no-top read
positionally, exactly the shape of the Series 4 failure the workstream existed to escape.
The project catches this in its own comments and demotes it, so it lands REAL, not SERIOUS;
but the demotion is load-bearing and must stay visible, because the *design contract* for
WS4 promised more.

---

## The five checks the review was asked to run

### 1. The strip test on every payoff (§0.3)

Run independently against the built statements.

- **no-top (`ws3_no_top`, WS3): EARNED — survives with "no last level" deleted → it FAILS,
  which is the pass condition.** Delete the `hunb` hypothesis (no last level / unbounded
  cardinals) and the proof cannot produce the escaping level `β` (`obtain ⟨β, hβ⟩ := hunb …`
  is the load-bearing step); the theorem is not merely unprovable but unstatable as written.
  The escaping object genuinely lives at a higher level that exists *because the index has no
  greatest element*. This is the S1/S2 test from Series 4 passing for the first time: no-top
  is not the single-carrier cardinal wall relabelled. ✔ Earned carrier theorem.

- **no-completing-view (`ws4_no_completing_view` / `ws6_tower_unknowable`, WS4/WS6): SURVIVES
  STRIPPING "FACE" → therefore NOT earned as a face theorem.** `FaceReaches T v y` is *defined*
  as `RelatesInf T (toColim T v.obj) y`; the `ViewAt` wrapper contributes only `v.obj`, a bare
  colimit object. Strip the face/view structure and the statement is `ws3_no_top` at
  `toColim T v.obj` — which is exactly how the proof is written (`have h := ws3_no_top …; exact
  h`). There is **no independent face-reach cardinality argument**. So by the §0.3 rule this
  payoff is an index/no-top fact with a view wrapper painted on, not an earned carrier theorem.
  ⚠ Flagged — see R-WS4/6. (The code comment on `ws4_no_completing_view` states this outright;
  the finding is that the *design* promised the opposite.)

- **poles (`ws4_poles_coincide`, WS4): SURVIVES stripping → bare index fact, correctly
  flagged.** The statement is a pure `ℤ` order equivalence with no carrier, no face, no tower.
  Its philosophical reading (descent = ascent of *relating*) is interpretation. Honestly
  labelled as such in code and design. ✔ Correctly demoted, not reported as an earned payoff.

- **groundless-no-collapse plurality half (`ws4_groundless_no_collapse`, WS4): EARNED.** The
  distinctness witnesses are two faced loops `loopState q1`, `loopState q2` whose distinctness
  is `ws3_loopface_ne` (a face fact) transported by `toColim_level_inj` (colimit injectivity).
  Strip the carrier/face and there is nothing to be distinct. ✔ Survives.

- **leak-free (`ws6_crosslevel_never_annihilate`, WS6): EARNED (and independent of the tower).**
  It is `ws3_faces_never_annihilate` at the graded label set, a genuine corecursive
  non-annihilation proof. Strip the face and "the composite face never drains to empty" has no
  referent. ✔ Survives.

- **descent (`ws6_descent_nonterminating` / `ws7_descent_nofirst_on_spine`, WS6/WS7):
  earned as an index fact on a bespoke spine, NOT as a carrier derivation** — and labelled
  exactly so. It consumes only "ℤ has no least element" and lives on `descState`, not on
  `Winf T`. ✔ Correctly scoped (this is open obligation #2, below).

- **relating-to = composed-of (`ws6_relating_is_composition`, WS6): does not reach the strip
  test — it is `Iff.rfl` on one identical definition.** See check 3. ✔ Correctly not reported
  as a coincidence.

### 2. Cross-workstream laundering

This is the check the batched review exists for. Both named candidate edges were traced:

- **WS4's V3 depending on WS6's cross-level face.** The dependency is real and is resolved by
  *definition*, not by an open hypothesis: WS6 owns `FaceReaches`/`ViewAt`/`ws6_tower_unknowable`
  and WS4 re-exports. Because `FaceReaches := RelatesInf`, V3 does not depend on any *open* WS6
  obligation — it depends on `ws3_no_top`, which is closed. So there is **no laundering of an
  open hypothesis** here. The issue is the opposite of laundering: the WS6 face structure V3
  imports is inert, so V3 gets no extra content from WS6 at all. (R-WS4/6.)

- **WS2's no-first-level depending on WS6's descending map.** `ws2_no_atom_floor` is the literal
  identity function `:= hnb` — it assumes its own conclusion (the index no-least fact) and does
  **not** invoke any WS6 carrier map. The carrier-level descending map (the thing that would
  *earn* no-first-level) is open obligation #2 and is **not** silently consumed anywhere: no
  theorem reported as discharged depends on it. `ws6_descent_nonterminating` exists only on the
  standalone `descState` spine and is never used to close a `Winf T` statement. So again **no
  laundering** — the gap is left open and labelled, not hidden in another file. ✔

- **Swept for others.** The flagship `ws7_payoffs_hold` / `ws7_payoffs_unconditional` conjoin
  four payoffs; each conjunct traces to a closed theorem (`ws3_no_top`,
  `ws4_groundless_no_collapse`, `ws7_crosslevel_leakfree`, `ws4_no_completing_view`). The only
  open-obligation-adjacent conjunct is the fourth (V3), and its openness is the *design-target*
  gap of R-WS4/6, not a hidden hypothesis — the theorem is fully proved as stated. No conjunct
  is discharged-in-isolation on another workstream's open lemma. ✔

Verdict on laundering: **none found.** The tight coupling the protocol worried about is real,
but the couplings are discharged by definitional re-export or left explicitly open, not
laundered.

### 3. The coincidence rule, where it applies

- **WS3 `ws3_wall_vs_grain`: PASSES as a genuine two-object coincidence.** The two conjuncts are
  `ws4_no_top_cardinal_at` (single level: the imposed cardinal wall, proof runs `nuLk_card_ge`)
  and `ws3_no_top` (colimit: no-top forced by no-last-level). These are *different statements
  about different objects* (one level vs `Winf T`) with *different proofs* (fiat κ vs
  higher-level overshoot). Neither unfolds to the other. This is a real coincidence theorem, the
  legitimate analogue of Series 4's `ws3_same_succ_diff_face`. ✔ (Same holds for WS5's
  `ws5_stratification_frees_bound` = `⟨carrier_card_ge, hunb⟩`: two true facts about two objects,
  legitimately conjoined; it carries no more than that and does not claim to.)

- **WS6 `ws6_relating_is_composition`: FAILS the coincidence rule — and is reported as failing.**
  `RelatesAtGrade` and `IsComposedOfAtGrade` are character-for-character the same definition, so
  the theorem is `Iff.rfl`. A "forced" partner that unfolds to the "definitional" one is exactly
  what the rule forbids reporting as Discharged. The code and ledger report it **OPEN** (register
  #12), not discharged. ✔ Correctly handled — the rule did its job.

- **WS6 `ws4_unknowable_eq_noview`: is an alias identity (`rfl`), reported as "one theorem by
  construction," NOT as a proved coincidence.** Since V3 is *defined as* INC2, the equality is
  `X = X`. The charter's "one theorem or two?" duty is answerable "one," which is legitimate —
  but the code is careful to state this carries no coincidence content. ✔ Correctly labelled.
  (This is the honest handling; the substantive problem is upstream, at V3 itself: R-WS4/6.)

Net: the coincidence rule is applied correctly in all three named places. One genuine
coincidence (WS3), two correctly-refused ones (WS6 relating=composition, WS6 unknowable=noview).

### 4. The trivialization verdict (WS7)

**Confirmed: `payoffsEstablished` is the honest verdict; `trivialized` is correctly refuted and
`oneDoubleUnboundedness` is correctly refuted.**

- *Refuting `trivialized`:* the three distinctness anchors (`ws7_notop_vs_collapse_distinct`,
  `ws7_tower_vs_carrier_distinct`, `ws7_poles_vs_notop_distinct`) are genuine — they exhibit
  contradictory properties on provably different objects (colimit vs single carrier; plural
  tower vs collapsing carrier; bare `ℤ` order fact vs `Winf`-quantified no-top). The payoffs do
  not collapse into one definition. ✔
- *Refuting `oneDoubleUnboundedness`:* leak-freeness provably holds of the walled `constTower`
  (`ws7_leakfree_NOT_from_du`), which is *not* doubly-unbounded — so at least one payoff is a
  second, independent fact, and the payoffs are a conjunction, not a single derivation. ✔
- *Honest derivation count:* exactly **one** payoff (no-top) genuinely derives from
  double-unboundedness (it consumes `hunb`). This is the pass-2 S1 correction (from "two" to
  "one"), and reading the code confirms one: descent does not take `DoubleUnboundedness`; V3 is
  no-top again; leak-free is the walled-tower second fact.

So at the whole-program level the reduction "the payoffs are distinct consequences of
double-unboundedness" is **partial**: one true derivation + one demonstrably independent fact +
three distinctness anchors. That is neither full trivialization nor full unification. The typed
verdict matches. ✔ **Trivialized is refuted at the program level, correctly.**

One honest caveat for the ledger: `ProgramVerdict` is a 3-constructor type and
`ws7_not_trivialized` / `ws7_verdict_eq` are `decide`/`rfl` over a *chosen* constant. The
verdict's *content* lives in the anchor theorems and `ws7_leakfree_NOT_from_du`, not in the
`decide`. This is the same structural point as WS2's `ws2_forced_answer` and is correctly
understood in the code (the verdict is "a summary label"; the anchors carry it). Not a defect —
noting it so no future pass mistakes the `decide` for the evidence.

### 5. The axiom-check status

**Static, not re-verified this pass — downgraded from the ledger's "closed with evidence."**
`spec/axiom-check-log.md` is a committed transcript claiming every headline theorem depends only
on `propext` / `Classical.choice` / `Quot.sound`, with `Build completed successfully`. It reads
as a genuine emit (per-theorem lines, two axiom-free entries for `ws2_no_least`/`ws2_no_great`
that match their `omega`/`rfl` proofs, a plausible `Classical.choice` provenance). But it is a
*text file*, and in this review environment the toolchain and Mathlib were unavailable, so
`#print axioms` was **not** re-run against the addressed build. `AxiomCheck.lean` exists and is
correctly wired (it imports `Series5` and prints the right theorem list), so the check *is*
reproducible where the toolchain exists — but "was it actually run against *this* build" cannot
be confirmed from inside this pass. See S-AX.

---

## Findings

### SERIOUS

**None.** No flagship payoff is reported Discharged while resting on an open obligation; the one
payoff whose "earned" status is overstated (V3) is caught and demoted in the code itself, so the
*reported* verdict does not rest on it. The program headline (`payoffsEstablished`, tower built)
does not depend on any mislabelled result.

### REAL

**R-WS4/6 — V3 ("no completing view") does not earn its face; it is no-top read positionally.
Owner: WS4 (with WS6, which owns the objects).**
The design contract for WS4 (`ws04-design.md`, V3) promised a form that "survives the strip test
because removing the face removes the theorem," with "the *missing* … a fact about the face's
reach." The built `ws4_no_completing_view` does not meet that: `FaceReaches := RelatesInf`, the
`ViewAt` wrapper is inert, and the proof is `ws3_no_top` verbatim. So V3's genuine gain over
Series 4 is *only* that no-top is now forced by no-last-level (real, via `hunb`) — **not** that
the face's reach is an independent mechanism. The code comments already say this; the gap is that
the design's V3 target is not met.
*Correction owed (no goalpost-moving):* either (a) **prove** the stronger V3 — build a genuine
face-reach object with its own `< κ_α` cardinality bound and cross-level finite-descent bound,
and show it misses an object by a face argument *not* reducible to `ws3_no_top` — or (b) **relabel**
V3 in the design and payoff tracker from "the earned no-view payoff / winner for Part C" to
"no-top read positionally (face wrapper inert); the earned content is no-top's, forced by
no-last-level," and record that the *distinct-face-mechanism* form is an open obligation. Do not
lower the WS4 success criterion; report the shortfall.

**R-#2 — No-first-level is definitional (index-level only); the carrier descent on `Winf T` is
unbuilt. Owner: WS2/WS6.**
`ws2_no_atom_floor` is `:= hnb` (assumes its conclusion); `ws6_descent_nonterminating` earns
non-termination only on the standalone `descState` spine, never on a genuine colimit object.
Already labelled Partial — definitional (register #2). Correctly labelled.
*Correction owed:* build a cross-level descending edge into a lower level on the tower carrier
`Winf T` and prove it never bottoms out; until then keep the "definitional / index-level" label.
Not a relabel-down — this one is "prove that."

**R-#12 — relating-to = composed-of is `Iff.rfl` on one definition; identification duty unmet.
Owner: WS6.** Correctly labelled OPEN.
*Correction owed:* build a genuinely separate composition-side relation from `lcomp` (the design's
"one from `destInf`, one from `lcomp`") and prove it `↔` the observation side. "Prove that."

**R-#13 — the DL2 positive is a grade-shift observation-coherence, not a distributive law.
Owner: WS6.** `GradedObsCoherentShift` carries none of the `DistLaw` monad laws; the genuine
graded weak distributive law (Egli–Milner `λ` commuting with observation *and* grade, bialgebra
laws) is unbuilt. Correctly relabelled in pass 2 (was `GradedWeakDistLaw`, which over-claimed).
The paired impossibility `ws6_no_strict_graded_law` is a genuine, substantial KS-diagonal proof
and stands. *Correction owed:* build the weak `λ` (or prove it cannot exist); keep the DL2
result named as a coherence, not a law. Correctly a terminal open, not a mislabel.

**R-#3 — the forced answer is a dichotomy over a stipulated 2-constructor type, not
essential-uniqueness. Owner: WS2.** `ws2_forced_answer` is `cases` over `Boundless`'s two
constructors; `WallsByFiat`/`CardinalValuesChosen` are `:= True` report-flags. Correctly labelled
heuristic/open (register #3). *Correction owed:* either prove essential-uniqueness ("every
boundless-and-plural construction is a doubly-unbounded tower") or keep it reported as heuristic,
as the charter §9 pre-authorizes. Correctly handled.

**R-#8 — attention as grade-shift is Trivialized. Owner: WS6/WS7.** `attend` is definable; no
coincidence with an independent attention notion (replicator / convergence) is shown. Reported
Trivialized, which the charter counts as an honest negative / success. Correctly handled — this is
a *terminal* REAL, not a gap to close.

### COSMETIC / ACCEPTABLE

- **C-1 — passthrough "lemmas."** `ws3_no_global_cap := hunb`, `ws4_unbounded_above := hna`,
  `ws4_unbounded_below := hnb` are identity functions that restate their hypothesis. Harmless as
  *feeding lemmas* and labelled "bare index fact," but they are not theorems in any load-bearing
  sense. Acceptable; consider a comment that they are re-exports, not results.
- **C-2 — `ws4_poles_coincide` / self-duality.** Bare `ℤ` order facts, correctly flagged as
  index properties with the philosophical reading marked interpretation. Acceptable as labelled.
- **C-3 — `constTower` is degenerate.** The only *unconditionally* concrete `Tower` with `ι = id`;
  it does not satisfy `DoubleUnboundedness` by design. Acceptable — `growingTower` (genuine
  injective non-identity legs) and `cardinalTower` (doubly-unbounded) carry the real weight.
- **C-4 — the typed verdict `decide`/`rfl`.** As noted in check 4, the verdict constant's proofs
  are trivial; the content is in the anchors. Acceptable and understood in-code.
- **C-5 — `ColimBisim` bakes in the common-level reduction.** The gate `ws1_bisim_eq_colim` is
  proved for bisimulations that *already* restrict to a common level. This is the design's stated
  reduction (D2), not a hidden weakening, but a reader should know the gate is "level-local
  bisim-is-identity transported," not an unconditional colimit coinduction principle. Acceptable
  as the design scopes it; worth a one-line pointer in the WS1 header.

---

## What survives cleanly (the earned core)

These are genuine, non-trivial, correctly-proved results that pass their strip tests and do not
launder anything:

1. **The colimit machinery (WS1).** Real terminal-coalgebra development for both `νPk` and the
   labelled `νLk`: Lambek (`lambek`, `lambekLk`), bisimulation-is-identity (`bisim_eq`,
   `nuLk_bisim_eq` from `Cofix.bisim_rel`), a genuine directed colimit as a quotient
   (`ws1_colim_equiv`), and the gate `ws1_bisim_eq_colim` (level-local, as designed). The QPF
   instances (`qpfPk`, `qpfLk`) are real constructions, not axioms.
2. **The Explosion Dilemma (WS2).** Both horns are honest transcribed theorems: the Parmenides
   collapse `ws2_collapse` (a real `P_κ`-bisimulation argument via `hnZeta`) and the
   global-groundless collapse; conjoined as `ws2_explosion_dilemma`. The cardinal wall
   `ws4_no_top_cardinal` runs a real Cantor/`carrier_card_ge` argument. This is a genuine sharp
   negative (Impossibility), the program's motivating engine.
3. **No-top on the colimit (WS3), forced by no-last-level.** `ws3_no_top` is the flagship, and it
   is *earned*: it consumes `hunb`, produces an escaping object at a higher level, and passes the
   strip test. `nuLk_card_ge` (the labelled carrier lower bound) is real, non-trivial work. The
   coincidence `ws3_wall_vs_grain` is a genuine two-object coincidence.
4. **A genuinely built doubly-unbounded tower (WS3/WS7).** `boundRelax` (bound-relaxing injective
   coalgebra morphisms via terminality), `boundRelax_injective` (a real `νLk`-bisimulation
   argument), `growingTower` (strictly increasing cardinals), and `cardinalTower : Tower.{u,u+1}`
   with proper-class index `Cardinal.{u} × ℤ`, proved to satisfy `DoubleUnboundedness`
   (`ws7_cardinalTower_du`). This closes the charter-§9 "most likely single point of failure": the
   flagship payoffs hold of a constructed object (`ws7_payoffs_unconditional`), not just a sound
   conditional. This is the single most important thing that changed since pass 1 and it is real.
5. **Plurality survives the colimit (WS3/WS4).** `ws3_loopface_ne` + `toColim_level_inj` give
   genuinely distinct objects in `Winf T`. Earned.
6. **Leak-free cross-level composition (WS6).** `ws3_faces_never_annihilate` transported verbatim
   to the graded carrier — a real corecursive non-annihilation proof, holding even on a walled
   tower (hence a genuine second fact for the verdict).
7. **The incompletenesses (WS6).** `ws6_lawvere_incomplete` (real `Function.cantor_surjective`
   diagonal) and `ws6_omega_nonterminating` (real face/reach computation on Ω).
8. **No strict distributive law (WS6).** `ws6_no_strict_graded_law` is a full, substantial
   Klin–Salamanca four-set diagonal impossibility, mechanized honestly. This is the deepest single
   proof in the series and it stands.
9. **The set-indexed wall (WS7).** `ws7_setindexed_walls` (with the honest `[Small.{u} T.Idx]`
   scope) correctly mechanizes why a small-indexed tower walls — the §4.1 "tower with a top,"
   proved, and correctly *not* applied to `cardinalTower`.
10. **The verdict apparatus (WS7).** The three distinctness anchors and `ws7_leakfree_NOT_from_du`
    are the objective guard, and they genuinely refute both `trivialized` and
    `oneDoubleUnboundedness`.

---

## Honest bottom line

Does the code prove the theorems? **Yes**, on a read of the proof terms — modulo S-AX (the axiom
emit and compile were not re-run in this environment; re-run required to *confirm* clean, but
nothing in the source suggests otherwise, and the textual/import audits pass).

Do the theorems meet the designs' stated targets? **Mostly, with one genuine shortfall.** WS1,
WS2, WS3, WS5, WS7 meet their targets. WS6 meets its leak-free/impossibility/descent-spine targets
and correctly *reports* its three shortfalls (relating=composition, genuine weak law, attention).
The one place a built theorem is weaker than its design contract while the design had promised
otherwise is **WS4's V3** (R-WS4/6): the face was supposed to be load-bearing and is not.

Do they satisfy the charter criteria they claim? **Yes for what is reported, because the reporting
is honest.** The charter's criteria (§8) explicitly admit "delivered but definitional-only" and
"obstructed" as terminal successes, and require the *Trivialized* catch as a success — and the
program uses exactly those honest outcome classes rather than overclaiming. Criterion (iv)'s
cross-level identity and (v)'s attention are reported open/Trivialized, not claimed. Criterion
(vii)'s no-view is the one that is *reported* as earned (V3) but is really no-top positionally
(R-WS4/6) — the correction there is a relabel of the design's claim, and the charter criterion
itself (no-view forced by no-first-no-last, not by a cardinality cap) is *partially* met: it is
forced by no-last-level, but the "facing structure is load-bearing" sub-clause is not met.

No `sorry`, no custom axiom, no signature that quietly weakens a target **that is not flagged**:
the two `:= True` flags, the `:= hnb`/`:= hna` passthroughs, the `Iff.rfl` identification, the
`rfl` alias, and the inert `ViewAt` wrapper are all *labelled* in code. The one that is
under-labelled relative to its *design contract* (not its code comment) is V3.

Net: **`payoffsEstablished` stands, honestly earned; the tower is genuinely built; the sharp
negatives (Explosion Dilemma, no strict law) are real; and the remaining gaps (#2, #3, #8, #12,
#13, and the V3 relabel) are correctly-labelled terminal Partials or open "prove-that"
obligations — none of which the headline depends on.** This is a clean pass with one REAL relabel
owed (V3) and no SERIOUS finding. Re-run `AxiomCheck.lean` against the pinned toolchain to convert
S-AX from static to verified.

---

## Routing table (finding → owner → trigger-to-close)

| Finding | Grade | Owner | Correction owed (no bar-lowering) |
|---|---|---|---|
| R-WS4/6 V3 face not load-bearing | REAL | WS4/WS6 | Prove the distinct face-reach form, **or** relabel V3 from "earned no-view" to "no-top positional; face wrapper inert," and record the distinct-mechanism form as open. |
| R-#2 no-first-level definitional | REAL | WS2/WS6 | Build the descending carrier edge on `Winf T`; prove non-termination there. Until then keep "definitional / index-level." |
| R-#12 relating = composed-of | REAL | WS6 | Build a separate `lcomp`-side relation; prove `↔` the observation side. |
| R-#13 genuine graded weak law | REAL | WS6 | Build the Egli–Milner `λ` with bialgebra laws (or prove impossible). Keep DL2 named a coherence. |
| R-#3 forced answer heuristic | REAL | WS2 | Prove essential-uniqueness, or keep reported heuristic (charter §9 permits). |
| R-#8 attention Trivialized | REAL (terminal) | WS6/WS7 | None to close — terminal honest negative. Keep Trivialized. |
| S-AX axiom check static | REAL (process) | WS7/process | Re-run `AxiomCheck.lean` on the pinned toolchain against this build; commit the fresh emit. |
| C-1 passthrough feeding lemmas | COSMETIC | WS3/WS4 | Comment as re-exports, not results. |
| C-5 `ColimBisim` common-level scope | COSMETIC | WS1 | One-line header note that the gate is level-local as designed. |

*Regenerated Phase D. Exit criterion (protocol §2 E): no SERIOUS findings remain (met); the REAL
items are correctly-labelled terminal Partials / open proof obligations (met), except R-WS4/6 and
S-AX, which require an action (a design relabel and an axiom re-run, respectively) before the next
pass can close them. Recommend one more D→E loop to apply the V3 relabel and re-emit the axiom
log, after which the series can close.*
