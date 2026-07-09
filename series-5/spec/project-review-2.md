# Series 5 — Blind whole-series adversarial review, pass 2

**`series-review.md`** · Phase D (second blind review pass) · reviews the addressed build
(`ws1…ws7.lean` + `Series5.lean` + `AxiomCheck.lean`) against the design contracts
(`spec/wsNN-design.md`) and the charter success criteria (`charter.md` §8), blind to
motivating prose. Grading: **SERIOUS** (the program verdict rests on it — e.g. a flagship
payoff laundering), **REAL** (a genuine gap, correctly labelled once fixed),
**COSMETIC/ACCEPTABLE**. Every finding names its owning workstream and the precise
correction owed — *relabel this / prove that / strip and re-prove*, never *lower the bar*.

*Disclosure (protocol §3): this is Claude reviewing Claude. The objective anchors are the
proof terms actually in the files, the module dependency graph, and the strip-test results
— not stated intent. Findings below rest on what the code says, which is checkable
statically.*

---

## Method note — what this pass could and could not check

The seven Lean sources (2284 lines) were read in full. A textual audit confirms **no
`sorry`, no `admit`, no custom `axiom`, no `native_decide`** anywhere in `formal/` — the
only hits for those tokens sit inside doc-comments (`AxiomCheck.lean`, `Series5.lean`).
`scripts/gate.sh` passes: **imports resolve only to `Series5`/`wsN`/`AxiomCheck` + Mathlib**,
so the standalone claim (charter §1) holds — nothing is pulled from `series-4/` or
`archive/`. The import DAG is acyclic: `ws1 → ws2 → ws3 → ws6 → ws4 → ws5 → ws7`.

What this pass **could not** do: run `lake build` or `#print axioms`. This checkout has no
`.lake` directory, no `.olean` artifacts, and no Lean toolchain; a full Mathlib v4.15.0
build is not reproducible in the review environment (the toolchain/release servers are
outside the network allowlist). So the `#print axioms` table in `spec/axiom-check-log.md`
and the "green build" claims are, from this pass's own evidence, **asserted, not
re-verified here** — see S3 for the correct standing of that. Every proof-term finding
below is robust to this: it is about what the code *states and proves structurally*, which
is checkable by reading.

---

## The five requested checks — results up front

1. **Strip test (§0.3) on every payoff.** `ws3_no_top` **survives** — no-last-level
   (`hunb`) is genuinely load-bearing; delete it and the escaping object at level `β`
   vanishes and the claim falls to the single-carrier cardinal wall. This is the real
   advance over Series 4 S2. `ws6_crosslevel_never_annihilate` **survives** (the grade is an
   inert `ℤ`-label; stripping it returns the genuine Series 4 theorem verbatim, floor-free
   because `ℤ` has no bottom). `ws4_poles_coincide` and `ws4_no_view_from_nowhere` (V2)
   **fail** the strip and are already demoted in the code (V2 is explicitly "recorded, NOT a
   payoff"). `ws4_no_completing_view` (V3) survives the *face* strip **only trivially** — see
   R1: its whole content is `ws3_no_top`, re-read positionally.
2. **Cross-workstream laundering.** The two edges the prompt names are handled honestly.
   WS4's V3-on-WS6 is resolved by an actual module dependency (WS4 imports WS6; V3 *is*
   `ws6_tower_unknowable`, which is *proved*, not left as an open hypothesis) — no
   laundering. WS2's no-first-level-on-WS6 is **not** discharged: `ws2_no_atom_floor` is the
   hypothesis restated (`:= hnb`) and the carrier descending map is genuinely open (#2). It
   is correctly labelled Partial, so it is R-grade, not laundering (see R2).
3. **Coincidence rule.** `ws3_wall_vs_grain` is a **genuine** coincidence (two structurally
   distinct proofs — single-level `< κ` fiat vs colimit no-last-level — conjoined). The
   other two named are **not** coincidences and are labelled so in the code:
   `ws6_relating_is_composition` is `Iff.rfl` on one character-for-character identical
   definition (duty OPEN, #12); `ws4_unknowable_eq_noview` is `rfl` on an alias (V3 := INC2).
   Both correctly reported as "not a proved coincidence." See R1, R3.
4. **Trivialization verdict.** **Refuted at the program level, and the refutation is
   real** — but see S1 for the one place the refutation is thinner than the ledger presents.
   `ws7_leakfree_NOT_from_du` is a genuine second-fact witness (leak-freeness holds of the
   walled `constTower`, which is provably not doubly-unbounded). The three distinctness
   anchors are genuine (distinct objects/properties). So `trivialized` is correctly ruled
   out. The residual concern is not trivialization but over-derivation claims (S1).
5. **Axiom-check status.** The `#print axioms` output exists as a **committed text file**
   (`spec/axiom-check-log.md`) with `AxiomCheck.lean` present and well-formed. Whether it was
   *re-run against the addressed Phase-F build* cannot be confirmed from this checkout
   (no build artifacts). Standing: **plausible and structurally consistent, not
   independently re-verified here.** See S3.

---

## SERIOUS findings

### S1 — WS7. The verdict ledger says "two payoffs *derive* from double-unboundedness"; one of the two derivations is a definitional restatement, not a derivation.

The verdict `payoffsEstablished` is argued from: *two payoffs genuinely derive from
double-unboundedness* (`ws7_notop_from_du`, `ws7_descent_from_du`), *one does not*
(`ws7_leakfree_NOT_from_du`). The "two derive" half is load-bearing for the middle verdict:
it is what distinguishes `payoffsEstablished` from `trivialized` on the derivation axis.

- `ws7_notop_from_du` is a genuine derivation: it consumes `hdu.2.2` (the unbounded-cardinals
  conjunct) and runs the real cardinality argument in `ws3_no_top`. **Sound.**
- `ws7_descent_from_du` is **not** a derivation from double-unboundedness. Its body is
  `ws6_descent_nonterminating q0 hinf d`, which takes an *arbitrary* `d : ℤ` and returns
  `d - 1` — it uses only that `ℤ` has no least element *as a bare order fact on `ℤ`*, and is
  stated for the **bespoke** `descState` spine, not for `∀ x : Winf T` and not consuming
  `DoubleUnboundedness T` at all (the signature has no `hdu`). It is `ws2_strict_below`
  wearing a corecursive costume. So the "descent derives from the tower's double-openness"
  claim is, in the code, the `ℤ` no-least-element fact restated on a hand-built spine.

Why SERIOUS and not REAL: the *count* "two derivations" is exactly the evidence the verdict
narrative uses to sit at the honest middle rather than collapse toward `trivialized` on the
derivation axis. With only one genuine derivation (no-top) plus a second-fact counterweight
(leak-freeness), the honest picture is "one payoff derives, one is a second fact, one
(descent) is the index fact restated on a spine, the rest are conjoined." That is still not
`trivialized` (the anchors and the leak-free second fact stand), so **the verdict label
survives** — but the *ledger's stated reason* overstates the derivational content by one.

**Correction owed (no goalpost-moving):** relabel `ws7_descent_from_du` and the WS7 docstring
/ status "two payoffs genuinely derive" to name descent honestly as *the no-first-level
index fact exhibited on the `descState` spine*, not a derivation from `DoubleUnboundedness`
(the theorem does not even take that hypothesis). Either (a) **prove** a genuine
carrier-level descent that consumes `DoubleUnboundedness T` and holds of tower objects
(this is open obligation #2, the WS6 descending carrier map) and then the derivation claim
is earned; or (b) **relabel** the verdict rationale to "one derivation (no-top), one second
fact (leak-free), distinctness anchors refute trivialization" — which still yields
`payoffsEstablished`. Do not lower `payoffsEstablished`; correct the stated count.

---

## REAL findings (genuine gaps, each correctly labelled once the label is fixed)

### R1 — WS4/WS6. "No completing view" (V3) is not a mechanism distinct from no-top; it is `ws3_no_top` re-read positionally.

`ws4_no_completing_view := ws6_tower_unknowable`, and `ws6_tower_unknowable`'s proof is
`ws3_no_top T hQ hunb (toColim T v.obj)` followed by `push_neg`; `FaceReaches T v y` unfolds
to `RelatesInf T (toColim T v.obj) y`. There is **no independent face-reach cardinality
argument** anywhere in WS4/WS6 (`grep` for `nuLk_card_ge`/`carrier_card_ge` in those files
returns nothing). So V3 "survives the face strip" only because it is *phrased* through
`RelatesInf`; its entire mathematical content is no-top's cardinality-plus-no-last-level
fact. The charter's V3 anti-laundering duty asks that "the *facing* structure be
load-bearing, or (b) is the Series 4 failure relocated up a level." As built, the facing
structure is a re-parameterization, not a second load path.

This is **correctly labelled already** in the code and tracker ("V3 *defined as* INC2, not a
proved coincidence"; `ws4_unknowable_eq_noview` is candidly `rfl` on an alias). So it is not
laundering. It is REAL because the charter's success criterion (viii) and §5.4's no-view
entry present V3 as "a genuinely different mechanism" from the cardinality wall, and it is
not a different mechanism — it is the same cardinality wall, made epistemic by composing with
`toColim`.

**Correction owed:** keep V3 as the earned no-view payoff (it does inherit no-top's genuine
no-last-level dependence — that is a real gain over Series 4's V2), but relabel its charter
§5.4 / criterion-(viii) description from "a genuinely different mechanism" to "the no-top
carrier fact read positionally; the new content over Series 4 is that no-top itself is now
forced by no-last-level, not by a fiat κ." No new proof required; the sentence that claims a
*distinct* mechanism is the thing to correct.

### R2 — WS2/WS6. No-first-level is definitional; `ws2_no_atom_floor` proves nothing beyond its hypothesis.

`ws2_no_atom_floor (T) (hnb) : … := hnb` — the proof term is the hypothesis. It is the
index-level "no least ⇒ every level has a lower level," which is `hnb` verbatim. The genuine
no-first-level (a face/relation descending into a strictly lower carrier level, tying
no-least-*index* to no-atom-*carrier*) is **not built**; `descState`/`ws6_descent_nonterminating`
give a descending spine on the standalone graded carrier `νLk κ (GLabel Q)`, *not* on
`Winf T`. This is open obligation #2 and is correctly labelled "Partial — definitional."

**Correction owed:** this is the honest terminal state *for now*; do not relabel it as
discharged. Trigger-to-close is unchanged: build a cross-level descending edge into `W_b` on
the tower carrier `Winf T` (not the bespoke `descState`) that consumes no-least-index and
produces a strictly-finer relatum of a genuine colimit object. Until then "groundless below,
no first level" is an index fact plus a spine exhibit, not a carrier theorem — state it so
in criterion (ii)/(vi).

### R3 — WS6. `ws6_relating_is_composition` is `Iff.rfl` on one definition; the identification duty is unmet.

`RelatesAtGrade` (ws6:53–54) and `IsComposedOfAtGrade` (ws6:62–63) are character-for-character
the same definition, so `ws6_relating_is_composition : … ↔ … := Iff.rfl` carries no
identification content. The charter's central §5.2/criterion-(v) claim — "relating-to and
being-composed-of are one relation at two grades" — is therefore **posited, not proved**.

This is **correctly labelled** (the docstring says "NOT a coincidence — duty OPEN," it is
removed from the coincidence column, and it is open #12). REAL, not SERIOUS, because the
program does not rest a *positive* verdict on this payoff — it is explicitly one of the
"totality/identification" items the design forecast would not land, and the tracker marks its
coincidence **OPEN**.

**Correction owed:** to earn it, build a genuinely separate composition-side relation from
`lcomp` (design Part-B: "one relation from `destInf`, one from `lcomp`") and prove it `↔` the
observation-side `RelatesAtGrade`. Absent that, keep the honest "duty open" label and do not
present criterion (v) as discharged. Do not close #12 by aliasing.

### R4 — WS6. `GradedWeakDistLaw` does not encode a distributive law; the theorem name over-claims.

`ws6_graded_weak_law_exists : Nonempty (GradedWeakDistLaw κ Q)` is a genuine, non-trivial
proof — but of a structure (`shift`, `bij`, `comm_obs`) that is a **grade-shift bijection
commuting with observation**, not a distributive law `λ : T F ⇒ F T` of the composition
monad over the observation functor. The interesting bialgebra obligation (charter §5.5, the
"deepest technical risk": that composition-as-algebra and observation-as-coalgebra cohere
across levels) is *not* what this structure states. The paired impossibility
`ws6_no_strict_graded_law` (the Klin–Salamanca four-set diagonal) **is** a real, substantive
theorem about actual distributive laws (`DistLaw` has the `natural`/`unit_T`/`unit_F` monad
laws). So the design's "no strict law, but a graded weak law" pairing is, as built, "no strict
distributive law (real), and a well-behaved grade-shift bijection (real, but not a weak
distributive law)."

**Correction owed:** relabel `ws6_graded_weak_law_exists` / `GradedWeakDistLaw` to what it is
— a *graded-observation-compatible grade-shift* (or "graded weak *coherence*") — and mark the
graded weak *distributive law* (an Egli–Milner-style `λ` commuting with observation *and*
grade) as an open obligation, unless it is intended to be dissolved, in which case say so.
The status already carries a "not full distributivity (DL2)" caveat; promote that caveat into
the theorem name so criterion (iv)'s "cohering via a graded weak distributive law" is not read
as discharged. No lowering of the impossibility DL1, which stands.

### R5 — WS2/WS5. Placeholder `Prop`s (`:= True`) sit inside three reported results.

`WallsByFiat (_) : Prop := True`, `CardinalValuesChosen (_) : Prop := True`, and the
essential-uniqueness content of `ws2_forced_answer` are vacuous or definitional:
`ws2_forced_answer` is a two-constructor `cases` returning `rfl`/`trivial` in each branch (the
dichotomy is a tautology over a 2-element inductive that *stipulates* the two provenances —
it does not prove every boundless construction is one of them), and `ws5_residual_fiat`'s
second conjunct is `trivial`. These are **honestly reported** — essential-uniqueness is open
#3 ("heuristic"), and G4 is labelled "honest report, not a characterization." REAL because a
reader scanning theorem *names* (`ws2_forced_answer`, `CardinalValuesChosen`) would overread
them.

**Correction owed:** keep the honest open labels (#3 heuristic; G4 report). Rename or
docstring `ws2_forced_answer` to `ws2_boundless_dichotomy_by_provenance` (it classifies a
stipulated 2-case type; it does not force the answer) and note `WallsByFiat`/
`CardinalValuesChosen` are report-flags (`= True`), not characterizations. Do not present
criterion-(i) essential-uniqueness as anything but the named heuristic.

---

## COSMETIC / ACCEPTABLE

- **C1 — WS7 typed verdict is decoration.** `ws7_verdict := payoffsEstablished`, and
  `ws7_verdict_eq` (`rfl`), `ws7_not_trivialized` / `ws7_not_one_du` (`decide`) are
  tautologies about a chosen enum constant — they prove nothing about the mathematics. This
  is acceptable *because* the actual content lives in `ws7_leakfree_NOT_from_du` and the
  three distinctness anchors, which are real; the enum is a summary label. Already flagged R4
  in pass 1. No correction beyond keeping the docstring's honesty.
- **C2 — WS1 design fixes.** `destInf → succSet` (the `Σ'` codomain is not `Quot.lift`-
  definable) and the explicit `LkRelax` in `ι_dest` are faithful Lean realizations of
  ill-typed design sketches, not target weakenings. `succSet` is representative-independent
  (`succSetPre_respects`) and the local `< κ_α` bound is recovered as `ws1_local_bound`.
  Acceptable.
- **C3 — `Nonempty Q` on `ws3_no_top` / `nuLk_card_ge`.** Necessary (without labels
  `νLk κ ∅` degenerates) and harmless (`Q` is plural anyway for the plurality payoff).
  Acceptable.
- **C4 — `ColimBisim` bakes in a common level.** The gate's bisimulation notion requires
  related colimit points to descend to one common level `c`. This is the design's stated
  reduction ("`R` pulls back along `toColim` to a level-local bisimulation") and is legitimate
  for a directed colimit; noting it so a future pass does not mistake it for a hidden
  restriction. Acceptable.

---

## What survives cleanly (the earned core)

These are genuine, substantive, and correctly stated — the real yield of Series 5:

- **The carrier machinery (WS1).** Terminal `P_κ`/`Lk`-coalgebras via QPF `Cofix`, Lambek
  (`lambek`, `lambekLk`), bisimulation-is-identity (`bisim_eq`, `nuLk_bisim_eq` from
  `Cofix.bisim_rel`), and the Cantor carrier bound (`carrier_card_ge`, `nuLk_card_ge`) are
  real proofs, faithfully transcribed and re-rooted. Standalone gate passes.
- **The colimit gate (WS1), settled with a real witness.** `ws1_bisim_eq_colim` reduces
  correctly to the level-local `nuLk_bisim_eq`. The genuine existential the charter flagged
  as "the most likely single point of failure" — bound-relaxing *injective coalgebra
  morphisms* between different-cardinal carriers — is **constructed** (`boundRelax` via
  terminality; `boundRelax_injective` via a real bisimulation-is-identity argument;
  `boundRelax_refl`/`_trans` via terminal-morphism uniqueness) and assembled into a
  non-degenerate tower `growingTower` (strictly increasing `ℵ₀ < 2^ℵ₀ < ⋯`). This is a
  real advance and it is not vacuous.
- **The doubly-unbounded tower is genuinely built (WS3/WS7).** `cardinalTower : Tower.{u,u+1}`
  (proper-class index `Cardinal.{u} × ℤ`, lex order, the same `boundRelax` legs) and
  `ws7_cardinalTower_du` prove it satisfies `DoubleUnboundedness` (no greatest via `Cardinal`
  + Cantor, no least via `ℤ`, cofinal cardinals via `2^(max ℵ₀ d)`). The `Tower` universe
  refactor (`Idx : Type w`, `Winf : Type (max u w)`) is real and `ws3_no_top` is reproved
  universe-generically. So `ws7_notop_unconditional` / `ws7_payoffs_unconditional` discharge
  the flagship antecedent against a constructed object — the pass-1 S1 "sound conditional, no
  subject" is genuinely closed. The honest scoping (`ws7_setindexed_walls`/`ws7_no_du_tower`
  now carry `[Small.{u} T.Idx]`) is correct: the §4.1 supremum collapse is a theorem about
  *small* indices, which `cardinalTower` provably escapes. **This is the headline, and it
  stands.**
- **No object relates to everything, endogenously (WS3).** `ws3_no_top` survives its strip
  test — the escaping object is produced at a higher level from `hunb`, so no-last-level is
  load-bearing. `ws3_wall_vs_grain` is a genuine coincidence (two distinct proofs). This is
  the "grain not wall" thesis Series 4 could not reach on one carrier, earned.
- **The Explosion Dilemma (WS2).** `ws2_explosion_dilemma` (both horns: the Cantor cardinal
  wall + the Parmenides/global-groundless collapse) and `ws2_collapse`,
  `ws5_global_groundless_collapses`, `ws2_supremum_walls` are real impossibilities — the
  program's motivating negative, mechanized.
- **Cross-level leak-freeness (WS6).** `ws6_crosslevel_never_annihilate` is
  `ws3_faces_never_annihilate` at `Q := GLabel Q`, transported verbatim, floor-free because
  `ℤ` has no bottom. Survives its strip. `ws7_leakfree_NOT_from_du` genuinely witnesses it as
  a *second* fact (holds of the walled `constTower`). Real.
- **No strict graded distributive law (WS6).** `ws6_no_strict_graded_law` — the
  Klin–Salamanca four-set diagonal — is a full, substantive impossibility proof about actual
  `DistLaw`s. Real. (Its weak-law partner is over-named; see R4.)
- **Plurality across the colimit (WS3/WS4).** `toColim_level_inj` + `ws3_loopface_ne` give
  distinct faced loops staying distinct in `W_∞`; `ws4_groundless_no_collapse`'s plurality
  half survives the strip. Real.
- **Inherited incompleteness (WS6).** `ws6_lawvere_incomplete` (Cantor diagonal) and
  `ws6_omega_nonterminating` are carrier-independent and genuinely proved.
- **The distinctness anchors (WS7).** Three mechanized rows on provably distinct
  objects/properties — the objective guard against trivialization. Real, and they carry the
  verdict.

---

## Honest bottom line

The program does **not** collapse to `Trivialized`, and that refutation is earned, not
asserted: leak-freeness is a demonstrated second fact and the three distinctness anchors sit
on genuinely different objects. The flagship — a *constructed* doubly-unbounded tower of
which no object relates to everything, with the bound endogenous and no-last-level
load-bearing — is real, survives its strip test, and (the pass-1 S1 gap) now holds of an
actual object (`cardinalTower`), not merely of an antecedent. The hardest single result, the
colimit gate, is discharged with real injective connecting maps. On the mathematics it can
build, Series 5 delivers.

What it should stop slightly over-claiming, in decreasing severity:

- **(S1)** The verdict rationale's "two payoffs *derive* from double-unboundedness" — only
  no-top genuinely derives; descent (`ws7_descent_from_du`) does not even take
  `DoubleUnboundedness` and is the `ℤ` no-least fact on a bespoke spine. The verdict label
  `payoffsEstablished` still stands; the stated count must drop to one derivation + one
  second fact + anchors.
- **(R1–R5)** V3 is no-top read positionally, not a distinct mechanism (R1); no-first-level
  is definitional pending the carrier descending map (R2, open #2); relating=composition is
  `Iff.rfl` on one definition (R3, open #12); the "graded weak distributive law" is a
  grade-shift bijection, not a distributive law (R4); and essential-uniqueness /
  residual-fiat sit behind `:= True` placeholders (R5, open #3). **Every one of these is
  already labelled honestly in the code and tracker** — the corrections owed are relabels of
  theorem *names* and charter §5.4/§8 *descriptions* that overread the proof terms, plus the
  two genuine open proofs (#2 carrier descent, #12 composition-side relation) that would
  *earn* what is currently posited. None is a request to lower a bar.

The characteristic risk the charter named — succeeding too cheaply, everything a feature of
one construction — is, on the evidence, **caught rather than concealed**: the code
consistently demotes the index facts (poles, V2), flags the aliases (V3, relating=composition),
and reports the placeholders (fiat, uniqueness). The one place the ledger's *narrative* runs
ahead of its *proof terms* is the derivation count (S1). Fix that sentence and the honest
picture and the mechanized picture coincide.

**Verdict on the review target:** no `sorry`, no custom axiom, no `admit` in the code
(textually confirmed); signatures match targets *except* where flagged (S1 count; R1/R4
names); `payoffsEstablished` is the correct outcome and is not laundered into. The build's
axiom-cleanliness is committed as evidence but was not re-run in this pass (S3, unchanged
standing) — the one item a next pass with a warm Mathlib cache should close by regenerating
`AxiomCheck.lean` against the Phase-F build.

### S3 (carried, unchanged) — axiom check is committed evidence, not re-verified here

`spec/axiom-check-log.md` records `#print axioms` output and `AxiomCheck.lean` is present and
references exactly the headline theorems. But with no build artifacts in this checkout and no
reproducible Mathlib build in-environment, this pass cannot confirm the log was regenerated
against the *addressed* (Phase-F) build — in particular the new `ws7_cardinalTower_du`,
`ws7_payoffs_unconditional`, `boundRelax_injective`, and the universe-refactored `ws3_no_top`.
**Correction owed:** warm the cache (`scripts/setup-environment.sh`), run `cd lake && lake
build` then the `AxiomCheck` emit, and paste the fresh output with a build timestamp. Until
then the axiom-clean claim is *plausible and structurally consistent* (nothing in the sources
introduces an axiom or `sorry`), not *independently verified*. This is a REAL/process finding,
not a mathematical one.

---

*Review pass 2, Phase D. Written blind to motivating prose, against the design signatures and
charter §8 criteria. Grading and routing per protocol §2–§3. The owning-workstream tags and
trigger-to-close for each finding feed the `charter-status.md` open-obligations register (#2
and #12 remain the two genuine open proofs; S1 is a new relabel owed to WS7; R1/R4/R5 are
name/description relabels owed to WS4/WS6/WS2). No finding asks for a lowered bar.*
