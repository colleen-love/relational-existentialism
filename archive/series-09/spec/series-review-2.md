# Series 09 — Series Review 2 (blind, adversarial, batched)

*Phase D, second pass. Reviewer reads the whole series at once against `charter.md`, the seven
`spec/wsN-design.md`, `spec/README.md`, and the built `formal/Series09/*.lean`, plus the Phase-E
address of `series-review-1.md`. Mandate: does the code prove the theorems; do the theorems meet
the designs' targets; do they satisfy the charter criteria they claim, with no `sorry`, no custom
axiom, no signature that quietly weakens the target. Grading: **SERIOUS** (the verdict rests on it /
a flagship payoff launders / the spine is Coincident / the carrier is too weak or too strong /
monotonicity assumed-in), **REAL** (a genuine gap, correctly labelled once fixed),
**COSMETIC/ACCEPTABLE**. No goalpost-moving: each finding names the owning workstream and a precise
correction owed.*

*Method: static (source + proof-term reading), as instructed — not built. The repository ships no
`.olean` artifacts and no captured stdout; the axiom log is a committed text file (see F-2-10).*

*This pass exists because pass 1 returned two SERIOUS findings (F-1 carrier-strength, F-8 point-edit
map) and Phase E claims both "fixed at charter strength." The central task of pass 2 is to verify
those two closures rather than accept the labels — and to look, now that the map was changed, for
what the change moved rather than removed.*

---

## The mandated checks, answered first and plainly

**1. The coincidence check (§0.4) — the reason the series exists. PASSED, unchanged from pass 1.**
`ws1_no_self_total_hold` (ws1.lean 290–295) unfolds to: assume `⟨t, ht⟩` with
`ht : ∀ h, insp t h ↔ diag insp h`; instantiate at `h := t`, so `diag insp t = ¬ insp t t` gives
`insp t t ↔ ¬ insp t t`; derive `False` by the standard `p ↔ ¬p` step (`np := fun hp => h.mp hp hp`;
`np (h.mpr np)`). This is a genuine Cantor/Lawvere fixed-point contradiction: the diagonal term is
`diag insp = fun h => ¬ insp h h`, and the contradiction is self-application at the would-be fixed
point `t`. The proof term references only `insp`, `Iff.mp/mpr`, `Exists.casesOn`. It contains **no**
`IsBisim`, **no** `IsBisimL`, **no** `BehaviorallyIdentified`, **no** `ws1_symmetric_states_bisimilar`,
**no** `SReaches`/`SHNE`. It does **not** route through bisimulation. The spine is **not Coincident**.
This is the one thing Series 09 exists to establish, and it holds. Series 08's wall is not re-hit.
(See F-2-1 on what "independent" buys once the carrier is examined, and the strip test on what the
fact *is* — neither retracts this pass, both bound its reach.)

**2. The carrier-strength check (§0.5) — SERIOUS, RE-AFFIRMED. Phase E "resolved as a relabel" does
not close it; it renames it. See F-2-1.**
The too-strong / Russell horn is genuinely closed by theorem: `dest` lands in `PkObj κ` and
`ws1_unrestricted_carrier_inconsistent` (ws1.lean 317–319) proves no surjective `insp` exists. That
side of §0.5 is clean and stays clean.

The too-weak horn is not. The question §0.5 poses is whether the carrier is **genuinely
hold-reflexive** — a hold ranging over *the space of holds* — or **merely self-looping**, too weak
to diagonalize, silently reducing to Series 08. Pass 1's F-1 asked for a positive richness witness.
Phase E's answer (charter-status §WS1; ws1.lean 328–337 NB) is to **withdraw the requirement**: the
near-surjective witness is declared "cardinality-confused," and the guard is re-stated as
"content is a predicate over holds, not a point," discharged by `ws1_holdreflexive_not_selfloop`.

Read the witness. `ws1_holdreflexive_not_selfloop` (ws1.lean 338–342) proves
`∃ insp, insp h₀ h₀ ∧ insp h₀ h₁` with the witness `insp := fun _ => (fun _ => True)` — the constant
`⊤` inspection. So the entire positive content of "hold-reflexive, not self-loop" is: *the constant-
True predicate holds two holds at once.* This is true, and it is strictly more than `inspLoop` can
say. But it is not the §0.5 property. The design's own load-bearing sentence (ws1-design.md §11;
README §2.3 third bullet) is that what separates a genuine spine from a vacuous one is a **rich**
inspection under which the self-total hold is *almost-formable* — the diagonal a real gap in a nearly-
complete enumeration. No such inspection is exhibited on the κ-bounded carrier; the spine holds
identically for *every* `insp`, including `inspLoop` (the design and ws1.lean 328–337 both admit
this). The cardinality objection is correct — you cannot surject `Hold` onto `HoldPred` minus a point
— but the correct response to "the designed witness is unrealizable" is not "so the guard is met by a
weaker witness"; it is "so the carrier-strength guard cannot be met in this form and the item is
**Partial**." Withdrawing the target and keeping the "Discharged / hold-reflexive" label is a
goalpost-move. Graded SERIOUS: the guard that stands between "impossibility *proved* on a genuinely
self-ranging carrier" and "impossibility *asserted*, holding equally on a self-loop" is not
discharged, and the label says it is.

**3. The strip test on every payoff (§0.3).**
- **Spine, strip "self-total":** survives as `¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h` — the bare Cantor
  fixed-point fact. Here surviving *as a fixed-point* is what the charter demands (§4.1); PASS, not a
  finding. (`ws7_strip_ledger` horn 1 is exactly this.)
- **Plurality, strip "residue"/"diagonal":** `ws2_residue_distinct` strips to "`fun h => ¬ insp h h`
  is not in the range of `insp`" — the spine re-read. ACCEPTABLE as a corollary; already relabelled
  (F-3, carried).
- **Forced dynamics, strip "self-total"/"re-diagonalization":** `ws3_dynamics_forced` strips to
  `¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h` **for `m'`**, with the `prec` hypothesis discarded. It survives
  stripping *completely* — indeed it survives deletion of the entire tower. See F-2-4.
- **Depth, strip "blind spot":** `ws4_depth_is_tower` strips to "`∃ x ∈ L, Q x` is monotone under
  `L ⊆ L'`" — a list-membership fact; `diag` never unfolded. Survives (carried F-5).
- **Spine/residue "moves", strip "re-inspection":** `ws4_residue_moves` strips to "if `∀h, P h → Q h`
  then `P h → ¬¬Q h`"-shaped modus ponens on the `ReDiagStep` implication. Survives. See F-2-8.
- **Bound, strip "residue":** `ws5_kill_condition` strips to "`⊤` satisfies `∀h, _ → True`, and
  `¬ diag ⊤ h₀` since `diag ⊤ = fun _ => False`." A bare fact about the constant-True successor.
  Survives (F-2-6).

Net: the spine's strip is the intended Cantor fact (good). **Every consequence still strips to a bare
fixed-point / list-subset / modus-ponens / constant-successor fact.** Pass 1 said this of a point-edit
map; the map changed shape (F-8), but the consequences did not gain self-inspection content — they
gained a different bare skeleton (implication-chasing on `∀ h, diag insp h → insp' h h`) in place of
the old one (`Function.update`). This is the heart of pass 2: see F-2-8.

**4. The freeness verdict (WS2). Free, from one position — genuinely, but a corollary. Carried as
labelled (was F-3).**
`ws2_residue_free` (ws2.lean 43–46) is a real theorem: recoverability would give a hold whose content
is `diag insp`, i.e. a self-total hold, contradicting the spine. `ws2_residue_distinct` quantifies
**one** `insp` and **one** `h`; no second position sits in the premise, so the Series 08 circularity
(`x↾(x,y) ≠ y↾(y,x)` needing `x ≠ y`) is genuinely not re-committed. This is the real repair, and it
is correctly labelled in charter-status as "Discharged **as a corollary of the independent spine**."
The tie to the Series 04/WS4 semantic import test (`ws2_residue_is_import`) is a re-statement
(recoverable ⇒ self-total), not an independent contact with `Recoverable`/`plainOf`; acceptable given
the corollary labelling. PASS on the non-circularity substance.

**5. The endogenous-order verdict (WS3). Order endogenous by construction: PASS. Forcing: see F-2-4.**
`prec := Relation.ReflTransGen (ReDiagStep dest)` (ws3.lean 39–41); `ws3_order_endogenous` is
`Iff.rfl` — the order genuinely *is* the re-diagonalization closure, no imported `ℕ`-index. The
imported-index branch is refuted by a genuine 2-cycle, `ws3_imported_index_refuted` (ws3.lean 96–102),
now a `⊤`/`⊥` 2-cycle with complementary diagonals (a 1-cycle is barred by the spine). Endogeneity of
the order-built-from-the-map: PASS. The weakness is in what `ReDiagStep` *means* (F-2-8) and in the
forcing (F-2-4), not in the endogeneity of the closure.

**6. The no-leaf verdict (WS3). (NL) relabelled honestly to face-by-type. Carried as ACCEPTABLE (was
F-7).**
Pass 1 found the old `ws3_redi_no_leaf` was `id` on its hypothesis. Phase E relabelled honestly:
`ws3_residue_is_face` (`diag insp = fun h => ¬ insp h h`, by `rfl`) establishes the residue is a
`HoldPred` — a face by *type*, never a bare relatum — and `ws3_redi_no_leaf` now proves the non-vacuous
positive `∃ insp, ∀ h, diag insp h` (witness `fun _ _ => False`, whose residue is all of `Hold`).
Inhabitation is explicitly **not** claimed for every `insp` (the docstring says so). The leaf trap
(§0.3 (NL): "a transient bare relatum anywhere is SERIOUS") is genuinely avoided — the residue is
never a point — so this is not the SERIOUS bare-relatum failure. Honest. Note the witness `fun _ _ =>
False` is the *empty* inspection; its "full residue" is the trivial dual of the spine, carrying no
carrier content — but as a face-shape witness that is all it needs to be. PASS as relabelled.

**7. Cross-workstream laundering. One SERIOUS chain persists across the F-8 fix. See F-2-8.**
The batched view is where the F-8 "fix" is exposed as a relocation. Pass 1's F-8 correction owed was
explicit: *tie `insp'` back to `dest`/`afford`/a hold of the residue face* — "`∀ h, diag insp h →
insp' (holdOf h)(holdOf h)` with `holdOf` finalised, the schematic form README §2.4 wrote and the
build dropped." Phase E strengthened the *shape* of `ReDiagStep` (from `∃ h₀` point-edit to `∀ h`
whole-residue) but **did not add the carrier tie**: `holdOf` and `Inspects` appear only in README §2.4
and in pass-1's correction text; `grep` finds neither in `ws3.lean`. The built map is
`ReDiagStep insp insp' := ∀ h, diag insp h → insp' h h` — `insp'` is still an arbitrary function,
constrained only to self-hold at the holds the prior stage left blind, and free (unconstrained)
everywhere else. Nothing ties `insp'` to `dest`, to `afford`, or to a hold *of* the residue face.
So WS4 ("depth is accumulated blind spots"), WS4 `ws4_residue_moves` ("re-inspection closes the
residue"), and WS5 (the monotonicity verdict) still consume a map that carries no re-inspection-of-
the-carrier content. The narration ("the self inspects the residue and thereby resolves it") is prose;
the theorem content is implication-chasing on an abstract `insp'`. Graded SERIOUS as a chain: the exact
correction pass 1 owed (the carrier tie) was not performed, and the label moved to "fixed at charter
strength" regardless.

**8. The coincidence rule at the spine, applied to all three "forced/definitional" pairs.**
- **WS1 no-self-total-hold vs. relational identity (flagship):** genuinely independent (check 1).
  PASS.
- **WS3 forced-dynamics vs. incompleteness:** now the theorem *does* invoke the spine
  (`ws3_dynamics_forced := ws1_no_self_total_hold dest m'`), so pass 1's F-4 "impossibility never
  used" is addressed *in citation*. But the `prec` hypothesis is discarded (`_hp`), so what is proved
  is "**every** `m'` is incomplete," not "every *reachable* `m'` is incomplete." The forcing pairs the
  spine with itself, not with the tower. Downgraded from F-4-REAL to F-2-4-REAL (differently: no
  longer "wrong lemma," now "vacuous use of the reachability hypothesis"). See F-2-4.
- **WS5 monotonicity vs. re-diagonalization:** the *Refuted* verdict unfolds to: the constant-`⊤`
  successor satisfies `ReDiagStep` for any `insp` (consequent always `True`), and `diag ⊤ = fun _ =>
  False`, so it closes every blind spot. This is honest (labelled Refuted/Partial, not assumed) and it
  is now a *whole-residue* closure rather than a point-flip — but it is still definitional: it is true
  by unfolding `ReDiagStep` at the `⊤` successor, exactly the shape the coincidence rule flags. Not
  Circular (labelled, not smuggled); thin. See F-2-6.

**9. The monotonicity verdict, stated plainly. PARTIAL — honestly labelled, not assumed. PASS.**
`ws5_monotonicity_verdict = .partialV` (ws5.lean 77), justified by `ws5_verdict_justified` (79–83),
carried into `ws6_monotonicity_retracted` by `rfl`. It is one of {Discharged, Refuted, Partial}:
**Partial** (retention Refuted-in-general via `ws5_retention_refuted`/`ws5_kill_condition`; strict
growth Discharged only on a freshness-gated chain class via `ws5_monotone_on_fresh`). It is never
assumed-and-unstated; `accResidue`/`MonotoneResidue` are measured *outside* `ReDiagStep`, so growth is
not baked into the map. This check PASSES on process and labelling — and note the finding *agrees with*
the charter's own prediction (§5.4) and with `ws4_residue_moves`: re-inspection *closes* what it
inspects, so retention *must* fail. The verdict is the honest one. Its evidential weight is low
(the refutation runs through the trivial `⊤` successor, F-2-6), but its *type* is sound and its
*direction* (Refuted) is forced by the mechanism, which is the right outcome.

**10. The axiom-check status. STILL STATIC despite a "captured run" claim. REAL. See F-2-10.**
`AxiomCheck.lean` contains `#print axioms` over every headline; `axiom-check-log.md` records
`[propext, Classical.choice, Quot.sound]` for each and an unfolded spine proof term. Phase E and the
log (axiom-check-log.md 12–17) now assert the lines were "captured from an actual `lake build
Series09.AxiomCheck` invocation … not asserted statically." But the repository still ships **no
build artifact and no captured stdout file** — `find` for `*.olean`/`*.log`/captured output returns
nothing; the log remains a hand-written transcription that now *claims* to be a capture. No `sorry`
and no `axiom` declaration appears anywhere in `formal/Series09/` (grep-confirmed; the only "sorry"
hits are the word in AxiomCheck's comment). The proofs are short and the axiom claims are entirely
plausible. But a prose file asserting "this was captured" is not a captured artifact, and pass 1's
F-10 correction ("commit the captured stdout, or annotate as asserted") is only half-done: the
annotation was changed to claim capture without committing the capture. REAL.

---

## Findings

### SERIOUS

**F-2-1 (WS1) — the carrier-strength / hold-reflexivity guard (§0.5, §4.4) is not discharged; Phase E
withdrew the target and relabelled rather than proving or reporting Partial.**
The load-bearing distinction in the design (ws1-design.md §11; README §2.3) is that a genuine spine
requires a *hold-reflexive* carrier — a hold ranging over the space of holds — witnessed by a rich
inspection on which the self-total hold is almost-formable, so the diagonal is a real gap and is *run,
not asserted*. The built witness `ws1_holdreflexive_not_selfloop` proves only that the constant-`⊤`
inspection holds two distinct holds (`insp := fun _ => fun _ => True`), i.e. "a non-point content
exists." The spine `ws1_no_self_total_hold` holds identically for **every** `insp` — including the
self-loop `inspLoop` — so nothing in the mechanized core distinguishes a hold-reflexive carrier from a
self-looping one. The cardinality objection to the *original* near-surjective witness is correct, but
it shows the *guard as designed is unmeetable*, which is a **Partial**, not a discharge by a weaker
witness.
*Correction owed (no bar-lowering):* either **prove** a cardinality-honest richness witness — an
`insp` on the κ-bounded `SHNE` carrier surjective onto a κ-bounded family of *realisable* contents
that excludes `diag insp` (near-surjective onto the realisable contents, not onto all of `HoldPred`),
so the diagonal is exhibited as the gap in a genuinely-ranging inspection — **or relabel** WS1
carrier-strength as **Partial (no rich witness; §4.4 guarded only by contrast with `inspLoop`, not by
a positive hold-reflexivity witness)** and strike "hold-reflexive carrier … DISCHARGED" from
charter-status §"What is proved" item 2 and the WS1 row. The spine's own Discharged/Independent status
does **not** depend on this (the diagonal holds for all `insp`), so this is a scope-honest re-report,
not a spine downgrade. Do not keep "the carrier is hold-reflexive, DISCHARGED" while the only witness
is "`⊤` is not a point."

**F-2-8 (WS3 owning; WS4/WS5 consuming) — the F-8 "fix" strengthened the *shape* of `ReDiagStep`
(∃→∀) but did not perform the correction owed (the carrier tie), so depth/dynamics/monotonicity still
launder self-inspection through an abstract map untied to the carrier.**
Pass 1's F-8 correction was specific: tie `insp'` to `dest`/`afford`/a hold of the residue face
(`holdOf`/`Inspects`, the schematic README §2.4 wrote). The build changed `∃ h₀, insp' h₀ = diag insp`
to `∀ h, diag insp h → insp' h h` but left `insp'` otherwise arbitrary and **added no carrier tie**
(`holdOf`, `Inspects` absent from `ws3.lean`). Consequently:
- `ws4_residue_moves` ("re-inspection closes the whole prior residue") is `fun h hd hd' => hd' (r h
  hd)` — modus ponens on the `ReDiagStep` implication. True, but it says nothing about a self
  inspecting a carrier; it says "if `insp'` self-holds every prior blind spot, then no prior blind
  spot is a blind spot of `insp'`," which is immediate from the definition.
- `ws4_residue_moves_witness`, `ws5_kill_condition`, `ws5_retention_refuted`, `ws3_serial`,
  `ws3_imported_index_refuted` all discharge their `ReDiagStep` obligations with the **constant `⊤`**
  successor (or `⊤`/`⊥`), which satisfies `ReDiagStep insp _` for *any* `insp` vacuously (consequent
  `True`). So "re-inspection" is witnessed by a constant function that inspects nothing.
- Read across workstreams: "depth is accumulated blind spots," "the residue moves to a fresh hold,"
  "the ever-deepening self is retracted" are theorems about an abstract predicate transform with no
  tie to `dest`/`afford`; the self-inspection reading is prose. This is the same laundering pass 1
  named, relocated from `Function.update` to `∀ h, … → insp' h h`.
*Correction owed:* finalise the carrier tie the design already wrote — define `holdOf`/`Inspects` so
`ReDiagStep`'s successor is a genuine inspection *of the carrier* (its content is the afforded face of
a hold whose face is the prior residue), and **re-prove** WS3/WS4/WS5 against it. If the tied map
cannot carry them (likely, since the `⊤` successor is what makes the current proofs trivial), report
WS4-layering and WS5-monotonicity as **Partial (map too weak / untied to witness re-inspection)** and
strike "DISCHARGED on the mechanized core" for WS4 and the "genuine, not a point-flip" claim for WS5.
Do not keep an untied abstract map and the re-inspection language together — that is precisely the
pass-1 SERIOUS finding, unaddressed.

### REAL

**F-2-4 (WS3) — forced dynamics now cites the spine but discards the reachability hypothesis, so it
proves "every stage is incomplete," not "every *reachable* stage is incomplete."**
`ws3_dynamics_forced (m m') (_hp : prec dest m m') : ¬ Complete m' := ws1_no_self_total_hold dest m'`.
The `_hp` is unused (underscore-bound). The charter's claim (§2 Consequence 2) is that a self-total
hold *being impossible forces successive re-inspection* — a statement about the tower having no
terminal complete stage. What is proved is the strictly weaker, tower-independent fact that *no*
inspection whatsoever is Complete, with `prec` as decoration. This is honest (it genuinely uses the
spine now, closing pass-1 F-4's "impossibility never used") but the forcing-by-reachability is still
not witnessed.
*Correction owed:* either **prove** the forcing that uses reachability — e.g. that a terminal stage
(one with no `ReDiagStep` successor carrying a fresh residue) would have to be self-total, so
non-termination follows *from* the spine *along the order* — or **relabel** `ws3_dynamics_forced` as
"no inspection is Complete (the spine, applied pointwise); seriality of `ReDiagStep` gives a successor
by construction (`ws3_serial`)," and drop "no *reachable* stage" and "forced" from the docstring and
charter-status, since the proof discards reachability.

**F-2-6 (WS5) — both horns of the Partial remain thin; the Refuted horn now fires through the
constant-`⊤` successor, which trivially closes everything.**
`ws5_retention_refuted` and `ws5_kill_condition` both use `insp' := fun _ _ => True`, which satisfies
`ReDiagStep insp insp'` for any `insp` (consequent `True`) and has `diag insp' = fun _ => False`, so
it closes *every* blind spot at once. The refutation of retention is therefore "the everything-holder
holds everything," a true but content-free witness; the Discharged horn (`ws5_monotone_on_fresh`) is
gated on a hand-supplied chain freshness hypothesis (`¬ accResidue chain h`). The verdict *type*
(Partial) and *direction* (retention Refuted) are correct and forced by the mechanism (see check 9);
the *evidence* is thin.
*Correction owed:* once F-2-8's tied map lands, re-run the kill condition against a *genuine*
re-inspection successor (not the constant `⊤`) and re-report; if only the `⊤` successor refutes
retention, state in WS5/charter-status that the refutation is witnessed only by the trivial successor
(honest thinness), not by a carrier re-inspection. No verdict change needed; evidence-strength
annotation owed.

**F-2-10 (build) — the axiom log now *claims* a captured run but still commits no artifact.**
`axiom-check-log.md` (12–17) asserts the `#print axioms` lines "were captured from an actual `lake
build Series09.AxiomCheck` invocation … not asserted statically," but no `.olean`, no stdout capture,
no build log is committed; the file remains a prose transcription. Pass-1 F-10 offered two acceptable
routes (commit the capture, *or* annotate as asserted-pending); Phase E took a third (annotate as
captured *without* committing the capture), which is weaker than either.
*Correction owed:* commit the actual captured stdout of `lake build Series09.AxiomCheck` (a file under
`spec/` or `formal/`), **or** change the log's wording back to "asserted from source reading, not
re-verified by a committed run." Do not claim capture without the captured artifact.

### COSMETIC / ACCEPTABLE

**F-2-11 (WS2) — `ws2_distributed_special_case` uses the all-false inspection, so both holds lie in
the residue vacuously (carried from pass-1 F-12).** `insp := fun _ => fun _ => False` gives
`residue insp = fun _ => True`, so "two distinct holds each in the residue" holds for *any* two
distinct holds; the witness carries no distributed-perspective content beyond distinctness of the
`labelLoop` pair. Explicitly "NOT claimed universal" (docstring; charter §9), so ACCEPTABLE. Noted so
no reader takes it as recovering Series 08's perspective as more than "two points, both trivially
un-held."

**F-2-12 (WS7) — the `Audit` certificate is sound-by-construction but its non-flagship fields inherit
F-2-4/F-2-6/F-2-8, and it has no carrier-richness field (F-2-1).** `ws7_verdict =
selfReferenceEstablished` is `rfl` on a discharged `Audit` whose every field is a real theorem, so it
genuinely cannot be hand-set — the mechanism is correct and commendable. But `dynamicsForced`,
`residueFace`, `monotonicityTested` are the thin theorems above, and no field witnesses
hold-reflexivity/carrier-richness. So the certificate vouches for "the spine is independent (true),
plus a bundle of definitional corollaries." ACCEPTABLE because the flagship field `diagonalNotBisim`
is the one that matters and it holds; noted so the certificate is not read as vouching for the
consequences at more than their proved strength.

---

## What survives cleanly

- **The spine is a genuine Cantor/Lawvere diagonal, independent of relational identity.**
  `ws1_no_self_total_hold` is a real fixed-point contradiction; its proof term contains no
  bisimulation, no behavioral identity, no symmetry lemma. Series 08's wall is **not** re-hit. This is
  the one result the series was built to obtain, and it holds without qualification *at the level of
  the fact itself* (checks 1, 8-flagship). The repair of Series 08's Partial lands in the precise sense
  the charter needed: no-self-total-hold is a separable second fact, not relational identity
  re-described. This did not change between passes and is not in doubt.
- **The too-strong / Russell guard is a theorem.** `ws1_unrestricted_carrier_inconsistent`: no
  surjective `insp` exists; κ-boundedness of `dest` (from `PkObj κ`) is real. The consistent-object
  side of §0.5 is clean.
- **Non-circularity of plurality.** No second position is smuggled into `ws2_residue_distinct`'s
  premise; the Series 08 circularity (`x ≠ y` in the premise) is genuinely not re-committed.
  Plurality-from-one-position is a true corollary of the independent spine, and is now labelled a
  corollary (checks 4; pass-1 F-3 relabel held).
- **The order is endogenous, not an imported clock.** `prec` *is* `ReflTransGen ReDiagStep`
  (`Iff.rfl`); the imported-index branch is refuted by a genuine `⊤`/`⊥` 2-cycle. (The weakness is in
  what `ReDiagStep` *means*, F-2-8, not in the endogeneity of the closure built from it.)
- **(NL) is honestly relabelled and the leaf trap is genuinely avoided.** The residue is a
  `HoldPred` — a face by type, never a bare relatum — and inhabitation is claimed only where
  witnessed, not universally (check 6; pass-1 F-7 relabel held). No transient bare relatum appears
  anywhere.
- **Monotonicity is settled to Partial by process, honestly, never assumed, and in the
  charter-predicted direction.** `accResidue` is measured outside `ReDiagStep`; the verdict is a datum
  justified by theorems; "retention Refuted" is reported as a success (the "ever-deepening self"
  retracted), exactly as §5.4 pre-registered. The discipline around the fork is what the charter
  asked for (check 9). Its evidential weight is low (F-2-6).
- **No `sorry`, no `axiom` declaration** anywhere in `formal/Series09/` (grep-confirmed). Whatever the
  axiom-run artifact status (F-2-10), the source is free of both hard prohibitions.

## Honest bottom line

**The thing the series exists to prove is still proved.** The diagonal spine is a genuine
Cantor/Lawvere fixed-point contradiction, independent of relational identity, repairing the exact gap
Series 08's series-review-3 left open. On its flagship — the only success criterion the charter says
the whole program requires (§8, closing paragraph: "the diagonal genuinely independent of relational
identity at least once") — Series 09 succeeds, and it should keep saying so. Nothing is Coincident,
nothing is Circular, nothing is assumed-in, the monotonicity fork is run and labelled Refuted-Partial
in the direction the mechanism forces.

**But the two SERIOUS findings pass 1 raised are not closed; they are relabelled.** This is the pass-2
finding and it is a discipline problem, not a soundness problem.

- *F-1 → F-2-1 (carrier-strength).* Phase E's response to "no rich witness exists" was to declare the
  requirement cardinality-confused and keep the "hold-reflexive carrier — DISCHARGED" label on a
  witness that proves only "`⊤` is not a point." The correct response to an unmeetable guard is
  **Partial**, not a discharge by a weaker witness. The spine holds for every `insp` including the
  self-loop, so *nothing mechanized distinguishes the hold-reflexive carrier from the self-looping one*
  — which is the §4.4 trap the charter names as gravest. The fact survives; the *carrier claim* is
  over-labelled.

- *F-8 → F-2-8 (the map).* The correction owed was a **carrier tie** (`holdOf`/`Inspects`, tying
  `insp'` to `afford`). Phase E delivered a **shape change** (`∃`→`∀`) and no tie. The consequences
  still strip to bare facts (implication-chasing and a constant-`⊤` successor in place of the old
  `Function.update`), and the re-inspection reading is still prose. The laundering pass 1 named was
  relocated, not removed.

The common thread — visible only batched — is that **`insp` is never connected to the carrier it
allegedly inspects.** `afford` (the hold's forced face, Series 04's semantic core) is defined and used
once, in `ws1_hold_forced`, and then never again; the entire reflexive layer (`HoldPred`, `insp`,
`diag`, `SelfTotal`, `ReDiagStep`) floats free of it. "A hold's content" is, mechanically, an
arbitrary `Hold dest → Prop`, not the face the hold affords. This is why every consequence strips to a
fact about abstract predicate transforms: there is no carrier in them to inspect. The spine does not
need the tie (Cantor bites any `f : A → (A → Prop)`), which is exactly why the spine is safe and the
consequences are thin.

**Verdict on the verdict:** `selfReferenceEstablished` is defensible **for the spine** and overstated
**for the carrier claim and the consequences**. Recommend: keep the spine's Discharged/Independent
status (criterion §8 met). Re-grade WS1 carrier-strength to **Partial (no rich hold-reflexivity
witness)**; re-grade WS4-layering and WS5-monotonicity to **Partial (map untied to the carrier;
re-inspection not witnessed)** unless the F-2-8 carrier tie is finalised and the theorems re-proved
against it; re-label `ws3_dynamics_forced` to drop "reachable"/"forced" or prove the reachability
forcing (F-2-4); commit the axiom capture or restore the "asserted" wording (F-2-10). None of these
lowers a bar: each is "prove the tied version / report Partial honestly / restore the honest label,"
and the spine already clears the one bar the program says matters.

*Two SERIOUS findings persist as relabels of pass-1 SERIOUS findings → a further D→E loop is warranted:
the corrections owed are the same ones pass 1 named (the carrier tie, the rich witness), not new goalposts.
The distinction pass 2 adds is that "addressed" in Phase E meant "relabelled," and the labels should be
brought back into line with what the code proves.*
