# Series 05 — Blind whole-series adversarial review, pass 1

**`series-review-1.md`** · Phase D (first blind review pass) · reviews the built
`ws1…ws7.lean` + `Series05.lean` + `AxiomCheck.lean` against the design contracts
(`spec/wsNN-design.md`) and charter success criteria (`charter.md` §8), blind to
motivating prose. Grading: **SERIOUS** (the verdict rests on it), **REAL** (a genuine
gap, correctly labelled once fixed), **COSMETIC/ACCEPTABLE**. Each finding names its
owning workstream and the precise correction owed — relabel / prove / strip-and-re-prove,
never lower the bar.

*Disclosure carried forward (protocol §3): this is Claude reviewing Claude. The objective
anchors are the strip-test results, the dependency graph, and the proof terms actually in
the files — those are what the findings below rest on, not intent.*

---

## Method note — what this pass could and could not check

The Lean sources were read in full. `grep` confirms **no `sorry`, no `admit`, no custom
`axiom`, no `native_decide`** anywhere in `formal/` (the three textual hits are inside
doc-comments). Signatures were checked line by line against the design contracts and the
charter's success criteria.

What this pass **could not** do: run `lake build` or `#print axioms`. The checkout has
**no `.lake` build directory and no `.olean` artifacts**, and a full Mathlib v4.15.0 build
is not reproducible in the review environment. So every "axiom-clean, `lake build` green"
claim in `charter-status.md` and `Series05.lean` is, from this pass's evidence, **asserted,
not verified here**. This is itself a finding (S3 below). All proof-term findings below are
robust to that: they are about what the code *says*, which is checkable statically.

---

## The five requested checks — results up front

1. **Strip test (§0.3) on every payoff.** Run below per payoff. Headline: `ws3_no_top`
   **survives** (no-last-level is genuinely load-bearing — a real advance over Series 04
   S2). `ws4_poles_coincide` and `ws4_no_view_from_nowhere` (V2) **fail** and are already
   demoted in the code. `ws6_crosslevel_never_annihilate` survives (grade is inert;
   stripping it returns the genuine Series 04 theorem). **But** `ws4_no_completing_view`
   (V3) survives the *face* strip only by importing `ws3_no_top`, whose own load-bearing
   hypothesis is fed in, never witnessed — see S1.

2. **Cross-workstream laundering.** The batched view surfaces the real one: **every
   flagship payoff is conditional on a `hunb`/`DoubleUnboundedness` hypothesis that no
   built `Tower` inhabitant satisfies.** The only inhabitant, `constTower`, is *proved not*
   doubly-unbounded (`ws7_leakfree_NOT_from_du`). So the payoffs are theorems of the form
   "*if* a doubly-unbounded tower exists, then …," and the antecedent is the unbuilt
   charter-§9 existential. This is the S1 finding, and it is only visible across files.

3. **Coincidence rule.** Two of the three named "coincidence" theorems **unfold to their
   definitional partner**: `ws4_unknowable_eq_noview` is `rfl` because
   `ws4_no_completing_view` is *defined as* `ws6_tower_unknowable` (S2a);
   `ws6_relating_is_composition` is `Iff.rfl` on two literally identical definitions
   (S2b, already self-reported as definitional-only). `ws3_wall_vs_grain` is the one honest
   coincidence — two genuinely different proofs conjoined (ACCEPTABLE).

4. **Trivialization verdict.** With S1 taken into account, the verdict machinery is sound
   *as far as it goes* but rests on a narrower base than advertised: `ws7_not_one_du` and
   the three distinctness anchors do refute both `trivialized` and `oneDoubleUnboundedness`
   as **conditional** statements. `Trivialized` is correctly **refuted at the conditional
   level**; it cannot be confirmed or refuted at the "whole-program, on a real object"
   level because there is no real object. Verdict `payoffsEstablished` stands, but its scope
   must be relabelled (R4).

5. **Axiom-check status.** **Static.** `AxiomCheck.lean` is a well-formed list of
   `#print axioms` commands, but nothing in the repo records their output, and the pass
   could not execute them. The "run against the pinned build" language in the ledger is
   ahead of the committed evidence (S3).

---

## SERIOUS findings (the verdict rests on these)

### S1 — WS1/WS3/WS4/WS6/WS7: the flagship payoffs have no witnessed model; every one is conditional on an unbuilt existential

**Owner: WS1 (deliverable), with WS3/WS4/WS6/WS7 consuming.**

This is the finding the batched review exists to catch. Trace the dependency graph:

- `ws3_no_top`, `ws3_bound_is_grain`, `ws3_wall_vs_grain`, `ws5_endogenous_tower`,
  `ws4_no_completing_view`, `ws6_tower_unknowable`, `ws7_payoffs_hold`,
  `ws7_notop_from_du`, and the distinctness anchors all take
  `hunb : ∀ c : Cardinal, ∃ a, c < (T.lvl a).card` (or the packaged
  `DoubleUnboundedness T`) as a **hypothesis**.
- `hunb` is never *derived* for any concrete tower. `ws3_no_global_cap` (line 202) and
  `ws2_no_atom_floor` (line 186) are literally `:= hunb` / `:= hnb` — the hypothesis
  returned unchanged.
- The **only** built `Tower` inhabitant is `constTower` (ws1.lean:643), and
  `ws7_leakfree_NOT_from_du` (ws7.lean:87) **proves** `¬ DoubleUnboundedness (constTower …)`.

So: the doubly-unbounded tower — the object of the whole series, the subject of every
success criterion in charter §8 — **is never constructed**. The status file is candid about
this in the WS1 row and open-obligations ("a *doubly-unbounded* inhabitant … stays the
charter-§9 existential") and in the residual-opens paragraph. The SERIOUS part is that the
**payoff tracker and the program snapshot do not carry the conditional into the headline**:
they say "boundlessness without a wall **earned**," "groundless-no-collapse **earned**,"
full stop. As proved, the honest statement is "**earned conditional on the existence of a
doubly-unbounded tower, which is not built.**" The escaping object in `ws3_no_top` is real
*given* a higher level `β`; whether such a `β` exists in any actual tower is exactly what
`hunb` asserts and nothing discharges.

Note this is *not* the S1/S2 Series-04 laundering (cardinal fiat with faces painted on) —
`ws3_no_top` genuinely uses `nuLk_card_ge` at level β and survives its strip test. It is a
different and arguably larger gap: the theorem is sound but **vacuous-risk** — its content
is entirely inside an antecedent that has no model on the books.

**Correction owed (no goalpost-moving):** *Prove that.* Build one doubly-unbounded `Tower Q`
inhabitant — the bound-relaxing injective coalgebra-morphism legs between different-cardinal
`νLk κ_α Q` that WS1 §9 names — and instantiate `hunb` from it, so at least one payoff is a
theorem with **no open antecedent**. Until then, *relabel* every "earned" in the payoff
tracker and program snapshot to "**earned, conditional on the charter-§9 tower existential
(unbuilt)**," and state plainly that no payoff currently holds of a constructed object. Do
**not** lower the bar by treating `constTower` as sufficient non-vacuity: it is proved to
fail the very hypothesis the payoffs need.

### S2 — WS4/WS6: two of three "coincidence theorems" unfold to their definitional partner (coincidence-rule violation)

**Owner: WS4 (S2a), WS6 (S2b).**

The charter's coincidence rule (§7) is explicit: discharge requires "the definitional form
and an independently motivated forced form, **separately stated and proved equal**." A
theorem whose proof unfolds to the definition does not meet it.

**S2a — `ws4_unknowable_eq_noview` (ws4.lean:123–125) is `rfl` on one object, not two.**
`ws4_no_completing_view` is *defined* as `ws6_tower_unknowable T hQ hunb v` (ws4.lean:114–117
— the body is literally that term). The "coincidence"
`ws6_tower_unknowable … = ws4_no_completing_view …  := rfl` is therefore `X = X`. This is
not "one theorem read two ways" adjudicated as one; it is one theorem *aliased* and then
asserted equal to its alias. The charter's "one theorem or two?" duty is answered "one" —
which is a legitimate answer — but the *mechanism* offered as evidence (a `rfl` between a
definition and its own expansion) carries no information and must not be presented as a
proved coincidence.

**S2b — `ws6_relating_is_composition` (ws6.lean:60–66) is `Iff.rfl` on identical
definitions.** `RelatesAtGrade` and `IsComposedOfAtGrade` are *character-for-character the
same definition* (both `∃ q, ((ULift.up d, q), y) ∈ (lstr x).1`). The status file and design
already flag this as "Definitional-only," which is the honest label. The SERIOUS aspect is
only that it appears under "coincidence" in the WS6 obligations table and the payoff tracker
lists the cross-level payoff's coincidence as this theorem — a reader could take the
identification duty as *partially* met when it is **not met at all** (there is no second,
independently-motivated definition anywhere in the file).

**Correction owed:** For S2a, *relabel*: report tower-unknowability and no-completing-view
as **one theorem by construction** (V3 is defined as INC2), and delete the `rfl` "coincidence"
or restate it honestly as "these are the same term by definition, not an independently proved
coincidence." For S2b, *prove that* or *relabel down*: either give a genuinely separate
composition-side definition (built from `lcomp`, as the design's Part-B triage promised —
"one from `destInf`, one from `lcomp`") and prove the `↔`, or drop `ws6_relating_is_composition`
from the coincidence column and record the identification duty as **open**, not
definitional-only-but-listed.

### S3 — all: the axiom-clean / `lake build`-green claim is static, not shown

**Owner: all (audit infrastructure, WS7/AxiomCheck).**

`charter-status.md` states `#print axioms` was "**run** against the pinned build; all 34
headline theorems on the standard three" and marks open-obligation #11 **CLOSED**.
`Series05.lean`'s header says "the full build compiles." The repository contains no build
artifacts and no captured `#print axioms` output, and this pass cannot reproduce the build.
The code is *plausibly* clean (no `sorry`/`axiom` textually; the constructions are ordinary
QPF/`Cofix`/`Cardinal` Mathlib usage), but "plausibly clean" is not "machine-checked," and
the protocol (§0, open-obligation #11) makes machine-checking the bar.

**Correction owed:** *Prove that* — commit the actual `lake build` transcript and the
`#print axioms` output (or a CI log) alongside the claim, then #11 is genuinely CLOSED. Until
that artifact exists, *relabel* #11 and the snapshot to "**axiom-clean predicted; machine
check owed**" (its status verbatim from the top-of-file caveat, which the later rows
contradict). This is a labelling contradiction inside the ledger, not a proof gap — but the
ledger's own rule is that axiom claims are provisional "until a machine-checked `#print
axioms` … is recorded," and no record is committed.

---

## REAL findings (genuine gaps, correctly labelled once fixed)

### R1 — WS2: `ws2_no_atom_floor` is the identity function; no-first-level is not earned at the carrier

**Owner: WS2 (with WS6 owing the descent).** `ws2_no_atom_floor` (ws2.lean:184–186) is
`(hnb : P) → P := hnb` — it proves nothing beyond restating its hypothesis. The status file
labels this correctly ("Partial — definitional," open obligation #2) and the design
pre-registered it. So this is **correctly labelled**; it is REAL rather than SERIOUS only
because the ledger does not claim otherwise. The charter's index-gate risk (§9: "if it can
only be *posited*, the groundlessness is fiat") is currently **realized** — no-first-level
holds at the `ℤ` index (`ws2_no_least`, genuine) but the *carrier* descent that would make
it about objects is absent.

**Correction owed:** *Prove that* — WS6's descending cross-level map on the tower carrier
(`descState` currently lives on the standalone graded carrier `νLk κ (GLabel Q)`, not on
`Winf T`), then no-first-level becomes a carrier theorem. Keep the honest "definitional
pending WS6" label until then; do not promote it.

### R2 — WS6: `ws6_descent_nonterminating` is about a bespoke spine, not the tower's objects

**Owner: WS6.** `descState` (ws6.lean:77) is a hand-built self-descending coalgebra on
`ULift ℤ`; `ws6_descent_nonterminating` shows *it* descends forever. This is honestly scoped
in the status file ("stated for a constructed descending spine, not `∀ x` (false in
general)"). The gap: it demonstrates that *a* groundless object exists on the graded carrier,
not that the tower `W_∞` is groundless below, and it is disconnected from `Winf T` entirely
(different carrier). As a witness that "groundless descent exists and never bottoms out" it
is fine; as the charter's "descent through the tower never terminates" (point 6, §5.4
groundlessness) it is a **surrogate**, correctly flagged.

**Correction owed:** *Prove that* — connect the descending spine to `Winf T` (a descending
sequence of colimit objects), or explicitly restate the groundlessness payoff as "a
groundless spine exists in the graded carrier," which is weaker than the charter's tower-wide
claim. Relabel accordingly; the current label is honest but the payoff tracker's "earned" for
groundlessness leans partly on this surrogate plus the plurality half.

### R3 — WS4: `ws4_groundless_no_collapse` delivers plurality + a collapse anchor, but not "groundless"

**Owner: WS4.** The theorem (ws4.lean:62) proves (i) `W_∞` has two distinct objects and
(ii) a single carrier collapses under global groundlessness. Neither conjunct is *descent
groundlessness*; the descent half is explicitly deferred to WS6 (R2). So the theorem named
"groundless_no_collapse" proves "**plural**, and single-carriers collapse" — the "groundless"
in the name is carried by the deferred WS6 spine. The two delivered conjuncts are real and
the plurality half survives its strip test (uses `toColim_level_inj` on genuinely distinct
faced loops — good). The name over-promises relative to the content.

**Correction owed:** *Relabel* to `ws4_plural_and_singlecarrier_collapses` (or similar), or
*prove that* by conjoining the R2 tower-carrier descent once built. Do not report
"groundlessness without collapse" as fully earned until the descent conjunct is on `Winf T`.

### R4 — WS7: the verdict is sound but its scope is "conditional payoffs," and the snapshot states it unconditionally

**Owner: WS7.** Given S1, every input to the verdict (`ws7_notop_from_du`,
`ws7_payoffs_hold`, the anchors) is conditional on `DoubleUnboundedness T` for a *supplied*
`T`. The verdict `payoffsEstablished` and the refutations `ws7_not_trivialized` /
`ws7_not_one_du` are correct as statements about the *inductive type* `ProgramVerdict` and
about the conditional theorems. What is **not** established is that the payoffs hold of a
real object — so "the payoffs are established" over-reads what the term proves.
`ws7_verdict_eq` is `rfl` (a tautology about a `def` returning a constructor); it certifies
only that the authors *wrote* `payoffsEstablished`, not that the mathematics forces it. The
distinctness anchors are the genuine objective content and they are fine (contradictory
properties on different objects, e.g. `ws7_tower_vs_carrier_distinct`).

**Correction owed:** *Relabel* the verdict's scope: "`payoffsEstablished` **for towers
satisfying `DoubleUnboundedness`; existence of such a tower is open (S1)**." Keep the anchors
as the honest core. Do not present `ws7_verdict_eq : … = payoffsEstablished := rfl` as
evidence for the verdict — it is a definitional check, and the file's prose slightly implies
more.

### R5 — WS5: `ws5_endogenous_tower`, `ws5_stratification_frees_bound`, `ws5_residual_fiat` are conjunctions of prior facts

**Owner: WS5.** These bundle already-proved lemmas (`ws1_local_bound`, `hunb`,
`carrier_card_ge`) with `∧`. The design says the content is "in the *statement*," and the
status file agrees. That is a defensible design choice (Series 04 R1 discipline: a conjunction
is not a derivation and must not be dressed as one), and the names don't claim derivation. So
this is REAL-and-correctly-labelled, bordering ACCEPTABLE. The one caveat: `CardinalValuesChosen`
is `def … : Prop := True` (ws5.lean:93), so `ws5_residual_fiat`'s second conjunct is `trivial`
— the "residual fiat" is *reported* as a `True` placeholder, not characterized. That is honest
labelling of a non-result, but a reader should not mistake it for a theorem about the fiat.

**Correction owed:** *Relabel* — note in the payoff tracker that G4's "residual fiat" is a
prose report backed by `True`, not a formal characterization. No proof is owed (it is a
genuine honest-report outcome), but the `True` should not sit unremarked under a theorem name.

---

## COSMETIC / ACCEPTABLE

- **`ws3_wall_vs_grain` is a genuine coincidence** (ACCEPTABLE, and a positive). It conjoins
  `ws4_no_top_cardinal_at` (a real single-level cardinal-wall proof, its own argument via
  `nuLk_card_ge`) with `ws3_no_top` (the tower-grain proof). Two different proofs of two
  different statements about two different loci — this is what the coincidence rule wants.
  Contrast S2a/S2b. (Still inherits the S1 conditional on the tower half.)
- **`ws6_no_strict_graded_law`** (the KS four-set diagonal, ws6.lean:173) is a real, fully
  worked impossibility proof — not a transcription stub. Genuine content. ACCEPTABLE.
- **`ws6_graded_weak_law_exists`** exhibits a concrete witness (`gradeShiftStr`, a real
  `ℤ`-bijection commuting with `LkMap`, proved). Genuine. The one soft spot: the
  `GradedWeakDistLaw` structure requires `bij` + `comm_obs` but **not** any actual
  distributivity of composition over union — it is "a grade-shift that is a bijection and
  commutes with observation," which is weaker than "a distributive law." The name promises
  more than the structure demands. *Relabel* the structure or add the distributivity field;
  ACCEPTABLE only because the design scoped DL2 to exactly this.
- **`ws4_poles_split` / `ws4_poles_coincide`** are clean order facts, correctly flagged as
  index facts that fail the strip test. Honest. ACCEPTABLE.
- **`attend` reported Trivialized** — definable, no coincidence with AT2/AT3, exactly as
  predicted. Honest negative, a success per §7. ACCEPTABLE.
- **`ws1_bisim_eq_colim`** — the gate. Its hypothesis `ColimBisim` bakes in "restricts to a
  level-local `νLk`-bisimulation at a common level," and the proof discharges via
  `nuLk_bisim_eq` + `hx/hy`. This is faithful to the design's stated reduction, and
  `nuLk_bisim_eq` is a real derivation from `Cofix.bisim_rel`. The gate is genuinely
  discharged **for relations of the `ColimBisim` shape**; whether every "bisimulation on
  `W_∞`" one would want is of that shape is a modelling choice folded into the definition, but
  it matches the design contract. ACCEPTABLE, noted for transparency.

---

## What survives cleanly

Setting aside the S1 conditional (which touches everything downstream), the following are
real, checkable, and correctly earned *as conditional or unconditional theorems as marked*:

- **The Explosion Dilemma** (`ws2_explosion_dilemma`) — unconditional, both horns real
  (`ws4_no_top_cardinal` via `carrier_card_ge`/Cantor; `ws5_global_groundless_collapses` via
  a genuine bisimulation). This is the series' motivating negative and it stands on its own,
  no tower existential needed. The strongest result in the build.
- **`nuLk_card_ge`** — a real, non-trivial new lemma (labelled-carrier Lambek + Cantor, with
  the `#Q < κ` case split). Load-bearing for `ws3_no_top` and honestly earned.
- **`ws3_no_top` survives its strip test** — no-last-level is genuinely load-bearing (delete
  `hunb` and there is no escaping level β; the proof cannot fall back to the single-carrier
  wall). This is the concrete advance over Series 04's S2 finding, *modulo* S1 (the `hunb` is
  assumed, not witnessed).
- **`ws6_crosslevel_never_annihilate`** — `ws3_faces_never_annihilate` instantiated at the
  graded label set, verbatim; strip the grade and you recover the real Series 04 theorem.
  Genuinely transported, floor-free because `ℤ` has no bottom. Unconditional.
- **The `ℤ` index facts** (`ws2_no_least/great/self_dual`) — clean, correct, unconditional.
- **The distinctness anchors** (`ws7_*_distinct`) — contradictory properties on different
  objects, the objective guard against trivialization. Sound.
- **No `sorry`, no `admit`, no custom `axiom`, no `native_decide`** in the sources.

---

## Honest bottom line

The build is **real mathematics, honestly self-labelled at the workstream level, undone at
the headline level by one structural fact the batched review is built to surface**: there is
no doubly-unbounded tower in the repository. `constTower` is proved *not* to be one, and every
flagship payoff — no-top, groundless-no-collapse, no-completing-view, tower-unknowability, the
whole `ws7_payoffs_hold` conjunction — is a theorem *conditional* on a `DoubleUnboundedness`
hypothesis that no built object satisfies (S1). The proofs are sound; their subject is an
antecedent, not an object. The charter's own §9 flags this existential as the most likely
point of failure, and the status file is candid about it in the open-obligations register —
but the program snapshot and payoff tracker report "earned," unqualified, and that is the gap
between the ledger's fine print and its headline.

On the specific checks: the strip tests are **run and pass** where the code claims (no-top,
leak-free, plurality survive; poles and V2 fail and are demoted) — this is a genuine
improvement in discipline over Series 04. The coincidence rule is **violated twice** (S2a `rfl`
alias, S2b identical-definition `Iff.rfl`) and honored once (`ws3_wall_vs_grain`). The
trivialization verdict is **correctly refuted at the conditional level** and cannot be
adjudicated at the whole-program level because there is no whole-program object; `Trivialized`
is not confirmed, but neither is the positive reduction it denies — the verdict's scope needs
relabelling (R4). The axiom check is **static** (S3): plausibly clean, not shown.

Nothing here asks the bar to move. The corrections owed are: **build the one tower** (S1,
the real work), **relabel two `rfl`s honestly** (S2, R4), **commit the axiom transcript**
(S3), and **keep the already-honest carrier-descent and residual-fiat items labelled as the
Partials they are** (R1, R2, R3, R5). If the tower existential is genuinely out of reach on
this carrier, the honest outcome is **Partial — the doubly-unbounded inhabitant is the open
obligation**, reported as such at the headline, not "earned" with the condition in a
footnote. That relabelling, plus the single construction, is the whole distance between what
the build proves and what the snapshot says it proves.

---

*Pass 1. Findings: 3 SERIOUS (S1 conditional-payoffs / unbuilt tower; S2 coincidence-rule
`rfl`s; S3 static axiom check), 5 REAL (R1 identity-function no-first-level; R2 bespoke
descent spine; R3 over-named groundless-no-collapse; R4 verdict scope; R5 `True`-backed
residual fiat), plus COSMETIC/ACCEPTABLE and a clean-survivors section. Route each to its
owning workstream per the register. Next: a Phase E code pass addresses this doc; then Phase D
regenerates it. Exit when no SERIOUS finding remains and the REAL items are correctly-labelled
terminal Partials — not when the build "finally passes at charter strength."*
