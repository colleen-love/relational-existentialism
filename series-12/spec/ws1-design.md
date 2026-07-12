# WS1 — The opening and the coincidence

**Design doc. Series 12, the blocking workstream. Owns: (a) THE TWO HALVES — the transcribed Series 07 import necessity (a genuine atomless distinction is non-recoverable) and the transcribed diagonal (self-inspection cannot totalize; the residue is free for every inspection, independent of relational identity); and (b) THE COINCIDENCE — that both halves characterize the SAME shape, `¬ Recoverable`, from opposite quantifier directions, with the residue the FORCED-FOR-ALL instance and the imports the EXISTS-SATISFYING class, proved as shape-identity and NEVER as object-identity. WS1 is blocking: WS2–WS4 build over the opening it draws.**

*Series 12 is standalone; the Series 07 import theorem (`ws2_import_theorem`, `ws3_atomless_distinct_is_import`, `ImportDiff`), the diagonal spine (`ws1_no_self_total_hold`, `ws1_diagonal_not_bisim`, `residue`, `ResidueRecoverable`, `ws2_residue_free`), and the import test (`Recoverable`, `plainOf`, `labelLoop`, `ws4_labelLoop_not_recoverable`) are transcribed into `series-12/formal/Series12/ws1.lean`, re-namespaced `Series12.WS1` (see `spec/README.md` §6). WS1 DEFINES the opening shape `Opening` (README §2.7) and is the only genuinely-new Lean here (the two halves are transcription; the coincidence is a statement about the transcribed facts). The one signature risk is the shared-negation fallacy (discipline 1): asserting the import IS the residue from their shared non-recoverability.*

## The object at stake

The charter's spine (§2, §5.1): the opening the diagonal GENERATES and the import Series 07 REQUIRES have the same shape, `¬ Recoverable`. Series 07 proved a differentiator cannot be recovered from the relating — any two atomless states are bisimilar (`ws1_atomless_bisim`), so a genuine atomless distinction is an IMPORT (`ws3_atomless_distinct_is_import`): non-recoverable, but by being adjoined, an inhabitant of the shape. The diagonal proved the structure generates non-recoverability from within — no inspection totalizes itself (`ws1_no_self_total_hold`), so the residue it leaves is FREE (`ws2_residue_free`): non-recoverable, but FORCED, for every inspection. The design's whole burden is to state the coincidence at exactly the right strength: **the required and the generated coincide in the shape `¬ Recoverable`, the residue is the forced instance, the imports are the class of inhabitants, and the two quantifier structures — forced-for-all vs exists-satisfying — are kept distinct, never collapsed into "the import IS the residue."** The pre-registered sin (discipline 1, charter §4.c): two things both failing `Recoverable` are not thereby identical — a junk label also fails it — so the coincidence is of shape, and the theorem must say exactly that much and no more.

**Ambient theory.** `spec/README.md` §2.2 (import theorem), §2.3 (diagonal + residue), §2.4 (import test), §2.7 (the `Opening` shape).

## Candidates

### C1 — The two halves, transcribed (the near-certain baseline)

```lean
/-- **THE TWO HALVES.** (Required) a genuine atomless distinction is an import — bisimilar yet unequal,
    non-recoverable from `dest`. (Generated) the residue is free for every inspection, and the diagonal is
    independent of relational identity. -/
theorem ws1_two_halves {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ x y : X, x ≠ y → ¬ LeafDiff dest x y → ImportDiff dest x y)          -- REQUIRED (Series 07)
  ∧ (¬ ResidueRecoverable insp)                                            -- GENERATED (the free residue)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t) :=  -- independent
  ⟨fun x y h hnl => ws3_atomless_distinct_is_import dest x y h hnl,
   ws2_residue_free dest insp, (ws1_diagonal_not_bisim dest insp).2⟩
```
The two halves, each transcribed: Series 07's `ws3_atomless_distinct_is_import` (required) and the diagonal's `ws2_residue_free` + `ws1_diagonal_not_bisim` (generated, independent of relational identity).

- **Ambient:** `ws3_atomless_distinct_is_import`, `ws2_residue_free`, `ws1_diagonal_not_bisim`.
- **Success condition (Discharged, transcribed):** the term typechecks — both halves are proved Series 07 / diagonal facts.
- **Failure mode:** *none — transcription.* **Winner (the baseline).**

### C2 — The shape-coincidence, quantifiers explicit (the lead)

```lean
/-- **THE COINCIDENCE.** Both the residue and the imports inhabit the opening shape `¬ Recoverable`, from
    OPPOSITE quantifier directions: the residue FORCED-FOR-ALL (non-recoverable for EVERY inspection), the
    imports EXISTS-SATISFYING (there EXISTS a non-recoverable labelled distinction). Shape-identity, stated
    with the quantifiers distinct; NEVER object-identity. -/
theorem ws1_shape_coincidence (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
        Opening (ResidueRecoverable) insp)                                 -- FORCED-FOR-ALL: the residue
  ∧ (Opening (Recoverable) (labelLoop hinf)) :=                            -- EXISTS-SATISFYING: an import
  ⟨fun {X} dest insp => ws2_residue_free dest insp,
   ws4_labelLoop_not_recoverable hinf⟩
```
where `Opening realizable c := ¬ realizable c` (README §2.7). The first conjunct is `ws2_residue_free` under the FORCED-FOR-ALL quantifier (`∀ insp`, the residue inhabits the shape); the second is `ws4_labelLoop_not_recoverable`, one EXISTS-SATISFYING inhabitant (an import inhabits the shape). The shape `Opening (¬ realizable)` is shared; the quantifiers are visibly different (`∀` vs the witnessed instance).

- **Ambient:** `Opening`, `ws2_residue_free`, `ws4_labelLoop_not_recoverable`.
- **Success condition (Shape-drawn):** the conjunction typechecks with the two quantifier structures manifestly distinct, and neither conjunct mentions the other's object.
- **Failure mode:** *object-identity (discipline 1).* If the theorem instead asserted `residue insp = (the import)` or a bijection making them one object, it would commit the shared-negation fallacy. C2 forecloses it: the two conjuncts live in DIFFERENT TYPES (`insp : Hold dest → HoldPred dest` vs a labelled coalgebra), share only the predicate SHAPE `Opening (¬ realizable)`, and are quantified differently. **Winner (the coincidence).**

**Paper triage.** Decidable and immediate: `ws2_residue_free` is universally quantified over `insp` (forced-for-all); `ws4_labelLoop_not_recoverable` is a single witnessed import (exists-satisfying). The shape `Opening` is the shared `¬ realizable`. **Winner.**

### C3 — The anti-identity theorem (the discipline-1 guard, first-class)

```lean
/-- **SHAPE, NOT IDENTITY.** Shared non-recoverability under-determines identity: the opening shape has MANY
    distinct inhabitants on the residue side alone (distinct inspections give distinct free residues), so
    "both fail `Recoverable`" cannot entail "same object." The coincidence is of shape; a junk label also
    fails it. -/
theorem ws1_coincidence_not_identity {X : Type u} (dest : X → PkObj κ X)
    (insp₁ insp₂ : Hold dest → HoldPred dest) (hne : residue insp₁ ≠ residue insp₂) :
    Opening (ResidueRecoverable) insp₁                                     -- inhabits the shape …
  ∧ Opening (ResidueRecoverable) insp₂                                     -- … and so does this one …
  ∧ residue insp₁ ≠ residue insp₂ :=                                       -- … yet they are DISTINCT
  ⟨ws2_residue_free dest insp₁, ws2_residue_free dest insp₂, hne⟩
```
The guard the review demands: two inspections both inhabit the opening shape (both free residues) yet are DISTINCT objects. So inhabiting `Opening (¬ Recoverable)` does not make two things one — the coincidence is necessarily of shape, and object-identity would be a category error (the residue and an import do not even share a type).

- **Ambient:** `Opening`, `ws2_residue_free`, the residue's dependence on `insp`.
- **Success condition (Shape-drawn):** two distinct inhabitants of the shape exhibited — shared negation under-determines identity, as a theorem.
- **Failure mode:** *asserting identity anyway.* Foreclosed: C3 IS the refutation of the fallacy. **Winner (the anti-identity guard).**

**Paper triage.** Decidable: distinct inspections yield distinct residues (`residue = diag insp`, and `diag insp₁ ≠ diag insp₂` when `insp₁`, `insp₂` differ at a self-hold), both free by `ws2_residue_free`. **Winner.**

### C4 — Object-identity form (the sin, stated to be rejected)

```lean
theorem ws1_import_is_residue (hinf : ℵ₀ ≤ κ) : (labelLoop hinf) ≃ residue (…) := …
```
Assert a canonical correspondence making the import and the residue ONE object.

- **Failure mode:** *the shared-negation fallacy, SERIOUS (discipline 1).* This is exactly the sin: from "both fail `Recoverable`" to "same object." Type-incorrect (they do not share a type) and false in content (many distinct things fail `Recoverable`). **Reject.** WS1 asserts shape-coincidence (C2) with the anti-identity guard (C3); never object-identity.

### C5 — A single fused predicate (the over-unification trap)

```lean
def NonRecoverable (thing) : Prop := ¬ Recoverable thing ∨ ¬ ResidueRecoverable thing   -- one predicate over both
```
Fuse the two recoverability notions into one predicate quantified over a sum type.

- **Failure mode:** *hiding the quantifier distinction.* A single predicate over `residue ⊕ import` would let the forced-for-all and exists-satisfying quantifiers blur into one existential/universal, exactly what discipline 1 forbids. **Reject:** the `Opening realizable c` abstraction (README §2.7) keeps `realizable` a PARAMETER, so the residue instance (`realizable := ResidueRecoverable`, `∀`-quantified) and the import instance (`realizable := Recoverable`, witnessed) stay visibly separate. Parametricity in `realizable`, not fusion.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the two halves, transcribed | `ws3_atomless_distinct_is_import`, `ws2_residue_free`, `ws1_diagonal_not_bisim` | yes — transcribed | **win (baseline)** |
| C2 | shape-coincidence, quantifiers explicit | `Opening`, `ws2_residue_free`, `ws4_labelLoop_not_recoverable` | yes — `∀` vs witnessed | **win (coincidence)** |
| C3 | shape ≠ identity (distinct inhabitants) | `Opening`, `ws2_residue_free` | yes — distinct residues | **win (anti-identity guard)** |
| C4 | the import IS the residue | — | yes — type-incorrect, false | **reject (the sin)** |
| C5 | one fused predicate | — | yes — hides the quantifiers | **reject (over-unification)** |

## Winning candidates: C1 (two halves) + C2 (coincidence) + C3 (anti-identity guard)

### Definitions and obligations (cite `spec/README.md` §2.2–§2.4, §2.7)

```lean
namespace Series12.WS1
-- ws2_import_theorem, ImportDiff, LeafDiff, ws3_atomless_distinct_is_import, ws1_no_self_total_hold,
-- ws1_diagonal_not_bisim, residue, ResidueRecoverable, ws2_residue_free, Recoverable, plainOf, labelLoop,
-- ws4_labelLoop_not_recoverable — transcribed (README §6).

/-- **The opening (shape), defined once (README §2.7).** Parametric in the candidate type and the
    recoverability notion, so the residue and the imports inhabit ONE shape by SEPARATE quantifiers. -/
def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c

/-- **D1 — the two halves (C1).** -/
theorem ws1_two_halves {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ x y : X, x ≠ y → ¬ LeafDiff dest x y → ImportDiff dest x y)
  ∧ (¬ ResidueRecoverable insp)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (i : Hold d → HoldPred d), ¬ ∃ t, SelfTotal i t) :=
  ⟨fun x y h hnl => ws3_atomless_distinct_is_import dest x y h hnl,
   ws2_residue_free dest insp, (ws1_diagonal_not_bisim dest insp).2⟩

/-- **D2 — the shape-coincidence (C2).** Forced-for-all (residue) ∧ exists-satisfying (import). -/
theorem ws1_shape_coincidence (hinf : ℵ₀ ≤ κ) :
    (∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
        Opening (ResidueRecoverable) insp)
  ∧ (Opening (Recoverable) (labelLoop hinf)) :=
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws4_labelLoop_not_recoverable hinf⟩

/-- **D3 — the anti-identity guard (C3).** Shared negation under-determines identity. -/
theorem ws1_coincidence_not_identity {X : Type u} (dest : X → PkObj κ X)
    (insp₁ insp₂ : Hold dest → HoldPred dest) (hne : residue insp₁ ≠ residue insp₂) :
    Opening (ResidueRecoverable) insp₁ ∧ Opening (ResidueRecoverable) insp₂
  ∧ residue insp₁ ≠ residue insp₂ :=
  ⟨ws2_residue_free dest insp₁, ws2_residue_free dest insp₂, hne⟩
```

**Proof architecture.** D1 threads the two transcribed halves (Series 07 required, the diagonal generated). D2 is the coincidence: the FIRST conjunct is `ws2_residue_free` under `∀ insp` (the residue inhabits the shape for EVERY inspection — forced-for-all); the SECOND is `ws4_labelLoop_not_recoverable`, one witnessed import inhabiting the shape (exists-satisfying). The shape `Opening (¬ realizable)` is shared, the quantifiers distinct, the objects never equated. D3 forecloses the fallacy by exhibiting two DISTINCT inhabitants of the shape (distinct free residues), so shared negation cannot entail identity. **Dependencies:** all three transcribe Series 07 / diagonal facts (README §6); no new mathematics, only the honest statement of the coincidence.

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D2 (`ws1_shape_coincidence`) with the quantifiers honest, D3 (`ws1_coincidence_not_identity`) the anti-identity guard. The required and the generated coincide in the shape `¬ Recoverable`, the residue the forced instance, the imports the class, never object-identity.
- **Discharged (transcribed):** D1 (the two halves).
- **Refuted / SERIOUS (pre-registered, discipline 1):** if the coincidence were ever stated as object-identity (C4) or the quantifiers fused (C5), the payoff is the shared-negation fallacy, SERIOUS — reported, not shipped. Foreclosed by D2's parametric-in-`realizable` shape and D3's distinct inhabitants.
- **Strip test.** Delete **"opening / coincidence / undefinable"** from `ws1_shape_coincidence` and it is the bare fact **"for every inspection the residue is not `ResidueRecoverable` (`ws2_residue_free`), and `labelLoop` is not `Recoverable` (`ws4_labelLoop_not_recoverable`), the two under distinct quantifiers"** — a forced-non-recoverable-residue-and-a-non-recoverable-inhabitant fact with the quantifiers distinct, which is EXACTLY what the charter demands (protocol §0.3: the coincidence should strip to "the forced-non-recoverable residue and the class of non-recoverable inhabitants share the shape `¬ Recoverable`, quantifiers distinct"). The interpretive layer ("the opening," "the coincidence") is earned; the mathematical content is two transcribed non-recoverability facts under honest quantifiers, and no name is a term.

## Deliverable

`series-12/formal/Series12/ws1.lean`: the transcribed carrier + import theorem + diagonal + import test (README §6); `Opening` (README §2.7); `ws1_two_halves` (D1), `ws1_shape_coincidence` (D2), `ws1_coincidence_not_identity` (D3). **WS1 is blocking; the opening it draws is ambient for WS2–WS4.** Axiom check: `#print axioms ws1_shape_coincidence` reduces through `ws2_residue_free` and `ws4_labelLoop_not_recoverable` to the standard three. **The coincidence is shape-identity with forced-for-all kept distinct from exists-satisfying, the anti-identity guard a theorem, and object-identity foreclosed — the guard against the shared-negation fallacy.**
