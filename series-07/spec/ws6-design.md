# WS6 — The heuristic ceiling

**Design doc. Series 07, the honest boundary. Owns: the line between what the Import Theorem *proves* and what it *defends* — the provable core (the general lemma over every plain coalgebra, the transcribed process instance, and the trichotomy) assembled as one theorem, versus the fully universal "*any* construction faithful to relating collapses", attempted and reported HEURISTIC when "construction" resists a formalizable quantifier, exactly as Series 04 (essential-uniqueness of restriction-quality) and Series 05 (essential-uniqueness of the tower) reported their forced answers.**

*Series 07 is standalone; names transcribed into `series-07/formal/Series07/ws6.lean`, re-namespaced `Series07.WS6` (see `spec/README.md` §6). WS6 builds almost no new Lean: the core is `ws1_atomless_bisim` (WS1), `ws2_import_theorem` (WS2), `ws1_productive_unique` (transcribed), and `ws3_trichotomy` (WS3), assembled; the universal is an attempted definition and its honest failure note. The shared `Construction` ceiling flagged by ws1 C3 and ws2 C4 is defined and adjudicated here, once.*

## The object at stake

The charter (§5.3) names two boundaries as load-bearing; WS6 owns the second: **the provable core versus the universal thesis.** The provable core is a finite conjunction of machine-checked facts — the lemma covers *every* plain `P_κ`-coalgebra (a genuine ∀ over `X` and `dest`), the process instance is transcribed Series 06, the trichotomy is WS3. Each is a real quantifier Lean can range over. The universal — "any construction *whatsoever* faithful to relating is either an import or collapses" — is not, because "construction" cannot be exhaustively ranged over: to quantify it one must first *define* the type of all constructions, and any such definition is either so general it has no content (every type with an endomap qualifies, and the claim becomes vacuous or false) or it is a *disjunction of the known shapes* (coalgebra ⊔ process ⊔ …), which is precisely not "all constructions". WS6's job is to draw that line honestly, mechanize everything on the provable side of it, attempt the universal, and — following the program's fixed discipline — report it a **defended thesis** if it resists, with the core as the floor beneath the defense.

**Ambient theory.** `spec/README.md` §2: the four ingredients; `ws1_atomless_bisim` (WS1); `ws2_import_theorem` (WS2); the transcribed `Proc`, `ws1_productive_unique`; `ws3_trichotomy` (WS3); the `Construction` abstraction flagged (README §2, "The construction abstraction") as the WS6 ceiling, not a WS2 obligation. §3's `ProgramVerdict` is WS7's, cited here only to place the heuristic outcome.

## Candidates (framings of the universal)

### C1 — The provable core as an explicit disjunction over known construction-shapes (the lead; the honest floor)

```lean
/-- The core: the impossibility, over the two shapes Series 07 actually mechanizes. -/
theorem ws6_provable_core (hinf : ℵ₀ ≤ κ) :
    -- static: every plain behaviorally-identified atomless coalgebra is a subsingleton
    (∀ {X} (dest : X → PkObj κ X), BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X)
  ∧ -- dynamic: the unique productive thread of the process is Ω
    (∀ (t : Proc κ), Productive t → t = omegaProc hinf)
  ∧ -- exhaustive: every distinction is a leaf, an import, or a collapsing history
    ws3_trichotomy
```
The core states exactly what is proved: the lemma-driven static collapse (WS1+WS2), the transcribed dynamic collapse (Series 06), and the trichotomy (WS3), conjoined — an *explicit disjunction* over the construction-shapes Series 07 built, no more.

- **Ambient `F`:** `P_κ` throughout; each conjunct is a standing theorem.
- **Success condition:** the term typechecks by assembling `ws2_import_theorem_static`, `ws1_productive_unique`, `ws3_trichotomy`. A genuine ∀ inside each conjunct (over `X`/`dest`, over `t`); no ∀ over "constructions".
- **Failure mode:** **disjunction-not-universal.** This is honest but *modest*: it covers coalgebras and the process, and names them; it does not cover "anything else faithful to relating". That gap is not a defect of C1 — it is the ceiling C1 exists to make explicit. C1 is the floor, correctly labelled.

**Paper triage.** Decidable-on-paper and near-transcribed: every conjunct is a proved theorem (WS1/WS2/WS3, Series 06). C1 is the assembly. **Winner (the core).** Its honesty is that it says "these shapes" and not "all shapes".

### C2 — A `Construction` typeclass abstracting "faithful to relating" (the aspirational universal)

```lean
class Construction (C : Type u) where
  carrier   : Type u
  step      : carrier → PkObj κ carrier         -- "relating" — but a process is not one step
  faithful  : BehaviorallyIdentified step       -- "an object is its relating"
theorem ws6_universal [Construction C] (hatom : ∀ x, SHNE (Construction.step) x) :
    Subsingleton (Construction.carrier)          -- ANY construction faithful to relating collapses
```
Abstract every construction as a single class carrying a `step` into the plain functor plus faithfulness, and prove the collapse once, for the class.

- **Success condition:** the class ranges over static coalgebras *and* processes *and* anything else faithful to relating, and the collapse is one theorem.
- **Failure mode:** **contentless or disjunction, and here contentless-then-false.** If `step : carrier → PkObj κ carrier` is the whole content, the class is *just a plain coalgebra* — it does not cover the process (`Proc` is the thread space of the final ω-chain, *not* a single `carrier → PkObj κ carrier`; ws1 D3 records this: the dynamic collapse is proved on its own carrier by `allNonempty_unique`, not derived from the lemma). To also cover `Proc` one must widen `step` to "a coalgebra *or* a process *or* …", which is C1's disjunction wearing a class's clothes; to widen it to genuinely *anything* (drop the `PkObj` codomain) is to lose the `P_κ` structure the lemma needs, and the theorem is then false (a labelled coalgebra is a "construction" that does not collapse). **Either contentless (= a coalgebra, missing the process), or a disjunction (= C1), or so general the collapse is false.** This trilemma *is* the un-formalizability.

**Paper triage.** The aspirational universal, and the one the charter predicts resists. It cannot simultaneously (a) cover the process, (b) stay a single quantifier, and (c) keep the theorem true — the three fail as a group. **Report heuristic:** `ws6_universal` is stated as the *thesis* the class gestures at, defended by the core, not proved for the class. Retained as the target the ceiling is drawn beneath.

### C3 — Category-theoretic form: final coalgebras in any suitable category

```lean
-- "any construction faithful to relating" = a final F-coalgebra in a category with
-- enough structure; atomlessness = the hne subobject; collapse = subterminality there
theorem ws6_universal_cat (𝒞 : Category) (F : 𝒞 ⥤ 𝒞) [HasFinalCoalgebra F] (…) : …
```
Phrase the universal as: in any suitable category, the hereditarily-non-empty part of the final `F`-coalgebra is subterminal — one theorem covering every "world" as an object of some `𝒞`.

- **Failure mode:** **needs machinery Series 07 does not build.** A genuine category-theoretic universal wants `CategoryTheory` final-coalgebra / behavioral-subobject infrastructure not transcribed into `Series07/`, and it *still* does not range over "anything faithful to relating" — it ranges over "final `F`-coalgebras in categories with the assumed structure", which is a more abstract *disjunction*, not the universal. It relocates the un-formalizability up a level; it does not dissolve it.

**Paper triage.** More general-*looking* than C2, same defect underneath (a parametrized disjunction, over categories now), and it costs unbuilt Mathlib `CategoryTheory` scaffolding. **Reject as a WS6 obligation; retain as the interpretive gloss** — the universal, *were* the category fixed and its machinery built, would be this; naming it marks the shape of the thesis without pretending to prove it. (Positioning, charter §10: universal coalgebra à la Rutten/Jacobs is exactly this register.)

### C4 — Declare the universal a defended thesis with the core mechanized (the pre-registered honest fallback)

```lean
/-- The universal, stated as prose-backed thesis, NOT a mechanized quantifier.
    Its evidence is `ws6_provable_core`; its scope beyond the core is defended, not proved. -/
def ws6_universal : ProgramClaim :=
  { core      := ws6_provable_core            -- machine-checked floor
  , thesis    := "any construction faithful to relating is an import or collapses"
  , status    := ClaimStatus.heuristic        -- defended, not a Lean ∀ over constructions
  , precedent := [Series04.forcedAnswer, Series05.forcedAnswer] }
```
Do not fake a quantifier. Package the universal as a claim whose *core* is the mechanized `ws6_provable_core` and whose *reach* beyond it is a defended thesis, explicitly `heuristic`, in the exact register Series 04/05 used for their forced answers.

- **Success condition:** the core member typechecks (it is C1); the thesis is honestly typed as heuristic, with the two prior forced answers cited as the precedent that makes this a *pattern*, not an evasion.
- **Failure mode:** **un-formalizable, and owned as such.** The thesis is not a theorem; C4 does not pretend it is. The only way C4 "fails" is dishonesty — stating the thesis as if mechanized — which the `ClaimStatus.heuristic` tag exists to forbid.

**Paper triage.** The pre-registered honest fallback, and the charter's predicted landing (§5.3, §9). **Winner (the universal's disposition):** `ws6_provable_core` is Discharged; `ws6_universal` is Partial — heuristic, with the core as its floor. This is the same shape every prior forced-answer claim took.

## Paper-decidable triage

| Cand | Framing of the universal | Lean status | Failure mode | Disposition |
|---|---|---|---|---|
| C1 | core as explicit disjunction over known shapes | typechecks (assembled) | disjunction-not-universal (by design) | **the mechanized core** |
| C2 | `Construction` typeclass over "faithful to relating" | does not close | contentless / disjunction / false-if-general | thesis target; **heuristic** |
| C3 | final coalgebras in any suitable category | needs unbuilt `CategoryTheory` | parametrized disjunction, machinery-heavy | gloss only |
| C4 | universal as defended thesis, core mechanized | core typechecks; thesis tagged | un-formalizable, owned | **the universal's home** |

## Winning candidates: C1 (the core, mechanized) + C4 (the universal, heuristic), with C3 as gloss

### Definitions and obligations

```lean
namespace Series07.WS6
-- ws1_atomless_bisim (WS1), ws2_import_theorem_static (WS2), Proc/Productive/omegaProc/
-- ws1_productive_unique (S6, transcribed), ws3_trichotomy (WS3), ProgramClaim/ClaimStatus — cited.

/-- **The provable core.** Static collapse (lemma-driven) ∧ dynamic collapse (transcribed)
    ∧ trichotomy (WS3). An explicit disjunction over the shapes Series 07 mechanizes — the
    honest floor, a genuine ∀ inside each conjunct, no ∀ over "constructions". -/
theorem ws6_provable_core (hinf : ℵ₀ ≤ κ) :
    (∀ {X} (dest : X → PkObj κ X), BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X)
  ∧ (∀ (t : Proc κ), Productive t → t = omegaProc hinf)
  ∧ ws3_trichotomy :=
  ⟨fun dest hb ha => ws2_import_theorem_static dest hb ha,
   fun t ht => ws1_productive_unique hinf t ht,
   ws3_trichotomy⟩

/-- **The universal.** Attempted as a quantifier (C2) — it does not close: any `Construction`
    general enough to cover coalgebras AND the process is either contentless, a disjunction of
    the known shapes, or so general the collapse is false. Reported HEURISTIC: a defended
    thesis floored by `ws6_provable_core`, in the register of Series 04/05's forced answers. -/
def ws6_universal (hinf : ℵ₀ ≤ κ) : ProgramClaim :=
  { core      := ws6_provable_core hinf
  , thesis    := "any construction faithful to relating is an import or collapses"
  , status    := ClaimStatus.heuristic
  , precedent := [Series04.forcedAnswer, Series05.forcedAnswer] }
```

**D1 — the provable core.** `ws6_provable_core`. *Strategy:* assemble the three standing theorems; each conjunct is a genuine quantifier Lean checks. *Paper-decidable:* yes — every member is proved upstream (WS1/WS2/WS3, Series 06); WS6 conjoins. **Discharged.**

**D2 — the universal, attempted then reported.** `ws6_universal`. *Strategy:* first *attempt* C2's `Construction` class and record the obstruction as a comment-level proof-sketch (the trilemma: to cover `Proc` the `step` field must widen to a disjunction, which is C1, or drop `PkObj`, which makes the collapse false — so no single honest `step` both covers the process and keeps the theorem). Then package the claim as C4 with `status := heuristic`, core `= ws6_provable_core`. *Paper-decidable:* the *impossibility of the quantifier* is decidable-on-paper (the trilemma has no fourth horn — cover the process ⇒ disjunction or contentless; keep truth ⇒ retain `PkObj` ⇒ not "anything"); the *thesis itself* is, by construction, not a Lean proposition. **Partial — heuristic.**

**D3 — the ceiling is drawn where the charter placed it.** *Strategy:* record, as the deliverable's standing note, that the line between D1 and D2 is *exactly* charter §5.3's provable-core/universal boundary and README §2's "`Construction` unifying both is the WS6 heuristic ceiling, not a WS2 obligation" — WS6 does not move the line, it mechanizes one side and defends the other. *Paper-decidable:* yes — it is a boundary-placement, cross-checked against the anchor.

### The strip test (charter §7)

Delete "heuristic" from `ws6_universal` — assert the thesis as a mechanized ∀ — and the claim becomes false-or-vacuous: there is no honest type of "all constructions" to quantify (C2's trilemma), so a stripped `ws6_universal` either ranges over a disjunction (and is C1 mislabelled as universal) or over everything-with-an-endomap (and a labelled coalgebra refutes it). The tag is load-bearing: it is the difference between a defended thesis and a false theorem. Delete "core" and the thesis floats free of any machine-checked floor — precisely the dishonesty the program forbids. Both deletions expose that the honest content lives in the *pairing* (mechanized core + tagged thesis), not in a phantom universal quantifier.

## Outcome classes (per charter §7)

- **Discharged:** `ws6_provable_core` (D1) — the static collapse, the transcribed dynamic collapse, and the trichotomy, assembled. The floor is machine-checked.
- **Partial — heuristic (pre-registered, exactly as Series 04/05):** `ws6_universal` (D2) — the fully universal form is a **defended thesis, not a theorem**, because "construction" admits no honest formalizable quantifier (C2's trilemma: contentless, or disjunction, or false-if-general). Reported heuristic with `ws6_provable_core` as its floor and Series 04/05's forced answers as precedent. This is not a shortfall relabelled as the goal; it is the goal's honest ceiling, named in advance by the charter (§5.3, §9) and README (§2).
- **Ceiling placed, not moved (D3):** the provable-core/universal line is charter §5.3's, mechanized on one side, defended on the other.

## Deliverable

`series-07/formal/Series07/ws6.lean`: cited `ws1_atomless_bisim`, `ws2_import_theorem_static`, `ws1_productive_unique`, `ws3_trichotomy`, `ProgramClaim`/`ClaimStatus` (transcribed from the Series 04/05 forced-answer packaging); `ws6_provable_core` (D1, Discharged); the attempted `Construction` class with its obstruction sketch and `ws6_universal` (D2, Partial — heuristic). Axiom check: `#print axioms ws6_provable_core` on the standard three (it is `ws2_import_theorem_static` + `ws1_productive_unique` + `ws3_trichotomy`, each already axiom-clean upstream). `ws6_universal` is a `def` returning a `ProgramClaim`, carrying no proof obligation beyond its `core` field — the honest mark that the universal is claimed, not proved.

---

*Design doc for Series 07 WS6. The provable core (coalgebras via the general lemma ⊔ the transcribed process ⊔ the trichotomy) is mechanized; the fully universal "any construction faithful to relating collapses" is attempted and reported heuristic — a defended thesis floored by the core, in the exact register Series 04 and Series 05 reported their forced answers. No em dashes in final academic paper copy; this working design doc is not final copy.*
