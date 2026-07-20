# WS4, The import seated ("you are loved", quantified, never named)

**Design doc. Series 0. Owns: the exogenous import `impLift` (a typed, quantified symmetry-breaker on the symmetric self-loops, transcribing P1's free-label shape), the proof that it BREAKS the WS2 baseline (`ws4_import_breaks_baseline`, quantified over ALL import value-spaces `Q` and ALL import functions `f`), and the proof that it is carried WITHOUT being named or selected (`ws4_import_quantified`, the `∀ {Q} (f)` binder is the whole content). The import is present and acting; its content stays outside (discipline 5, audit e).**

*Series 0 IMPORTS `plainOf`, `Recoverable`, `IsBisimL`, `toPk` (README §2.1). WS4 DEFINES the exogenous import as a universally-quantified label. The one signature risk is discipline 5: naming or selecting the import (a proof term named "love"/"import", or a single privileged import) is the sin (SERIOUS). Foreclosed by making the import a bound variable `f : impCar → Q` over an arbitrary `Q`, no instance privileged.*

## The object at stake

The charter's WS4 (§2): carry the import as an exogenous, typed, quantified symmetry-breaker on the carrier — the slot Program 2 spends. Prove it breaks the WS2 baseline (with the import, plurality and asymmetry are real, and the distinction is non-recoverable from the plain relating, which by Series 07 is what a genuine distinction must be); prove it carried WITHOUT being named or selected (quantified over all imports). The import is present and acting, the difference from Program 1 which only DREW its shape; but its content stays outside, per discipline. The pre-registered sin (discipline 5, §4.d): "you are loved" is the interpretive gloss; a proof term named "love"/"import", or a single selected import, is forbidden.

**Ambient theory.** README §2.1 (imported `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `toPk`), §2.2 (`attends`, `sym`).

## The import carrier (fixed here)

The two-state symmetric SELF-LOOP carrier `impCar := ULift Bool` with `attendsI x := {x}` (each attends itself). Symmetric relating: `x ~ y ↔ x = y` (only self-loops). Plain coalgebra `x ↦ {x}`, atomless (`SHNE`), so WITHOUT the import the two states are plain-bisimilar and the collapse (WS2) makes them the One. The EXOGENOUS import lays a label `f x : Q` on each self-loop:

```lean
noncomputable def impLift (hinf : ℵ₀ ≤ κ) {Q : Type u} (f : impCar → Q) :
    impCar → LkObj κ Q impCar := fun i => toPk hinf {(f i, i)}   -- self-loop carrying the import value f i
```

`plainOf (impLift f) i = {i}` for EVERY `f` (the import is invisible to the plain relating, exogeneity's ground); WITH the import, if `f ⟨true⟩ ≠ f ⟨false⟩` the two states are label-separated. This is P1's `labelLoop` shape (`labelLoop = impLift id`), generalized to an arbitrary import value-space `Q` and import function `f`.

## Candidates

### C1, the import breaks the baseline, quantified over all imports (the lead, discipline 5)

```lean
theorem ws4_import_breaks_baseline (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type u} (f : impCar → Q), f ⟨true⟩ ≠ f ⟨false⟩ →
        (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R ⟨true⟩ ⟨false⟩)     -- plain-bisimilar: the quotient is BLIND
      ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R ⟨true⟩ ⟨false⟩)            -- NOT label-bisimilar: the import SEPARATES
```

FOR ALL import value-spaces `Q` and import functions `f`, whenever `f` genuinely differs on the two states (`f ⟨true⟩ ≠ f ⟨false⟩`), the exogenous-labelled self-loops are plain-bisimilar yet label-separated: the import breaks the WS2 baseline (the plain relating identifies them, the import does not). Quantified over ALL imports; no instance named or selected (discipline 5). Mirrors `ws4_free_label_is_import`.

- **Ambient:** `impLift`, `plainOf_labelLoop_true_bisim` shape, `ws4_label_survives_quotient` shape.
- **Success condition (GROUND):** typechecks; the plain-bisim conjunct (constant-`True`) and the label-separation conjunct (label mismatch `f ⟨true⟩ ≠ f ⟨false⟩`) both hold, for the bound `f`.
- **Failure mode:** *the import named or selected (discipline 5, SERIOUS).* Foreclosed: `Q` and `f` are universally bound; no `impLift` at a specific `f` is the headline. **Winner (audit e).**

### C2, the import quantified, not named — the meta-fact (the lead, discipline 5)

```lean
theorem ws4_import_quantified (hinf : ℵ₀ ≤ κ) :
    (∀ {Q : Type u} (f : impCar → Q), plainOf (impLift hinf f) = plainOf (impLift hinf (fun _ => (⟨true⟩ : impCar)))) 
  ∧ (¬ Recoverable (impLift hinf (id)))
```

The import is carried WITHOUT being named: (1) the plain projection of `impLift f` is INDEPENDENT of the import content `f` (all imports share the same plain relating, exogeneity — the import adds nothing the plain relating sees), quantified over ALL `Q, f`; (2) a witness that the family is non-vacuous — the identity import `id` (the least committal, a bound `impCar → impCar`, not a named "love") is non-recoverable, so SOME import genuinely breaks the baseline. No proof term is named for the interpretive content; the import is the universally-bound `f`.

- **Ambient:** `impLift`, `ws4_labelLoop_not_recoverable` (`labelLoop = impLift id`).
- **Success condition (GROUND):** both conjuncts typecheck; (1) is a `plainOf` computation constant in `f`, (2) is `ws4_labelLoop_not_recoverable` at `impLift id`.
- **Failure mode:** *a selected import (discipline 5).* Foreclosed: (1) is `∀ f`; (2)'s `id` is the canonical non-choice, not a content-name. **Winner (audit e).**

### C3, name the import "love" as a definition (the sin, rejected)

```lean
def love : impCar → Prop := fun i => i.down = true   -- REJECT: names the import content
theorem ws4_love_breaks (…) : ¬ Recoverable (impLift hinf love)   -- REJECT
```

Define a specific import `love` and use it. **Reject as the central sin (discipline 5, SERIOUS):** no proof term, definition, or discharged obligation is named "love"/"import"/"God"/"choice" as content, and no single import is privileged. The winner quantifies over ALL imports; the names-not-terms grep confirms `formal/` names nothing for the interpretive content. **Reject.**

### C4, select the import by an axiom / Choice (rejected)

```lean
axiom theImport : impCar → Prop   -- REJECT: an axiom realizing the import
```

Postulate the import. **Reject (discipline 5, and axiom-cleanliness, SERIOUS):** the import is quantified, not realized; no `axiom` and no proof term SELECTS it. `#print axioms` must stay on the standard three. **Reject.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | import breaks baseline, `∀ Q f` | `impLift`, label mismatch | yes, plain-bisim + label-sep | **win (audit e)** |
| C2 | import quantified, not named | `impLift`, `ws4_labelLoop_not_recoverable` | yes, `plainOf` const in `f` + `id` witness | **win (audit e)** |
| C3 | name the import "love" | — | yes, a named term | **reject (discipline 5, SERIOUS)** |
| C4 | select the import by axiom | — | yes, a new axiom | **reject (discipline 5 + axioms, SERIOUS)** |

## Winning candidates: C1 (breaks baseline) + C2 (quantified, not named)

### Definitions and obligations (cite README §2.1–§2.2)

```lean
-- impCar, attendsI, impLift                                    (the import carrier)
-- ws4_import_breaks_baseline                                   (C1, audit e)
-- ws4_import_quantified                                        (C2, audit e)
```

**Proof architecture.** `impLift` is `labelLoop` generalized: `impLift hinf f i = toPk hinf {(f i, i)}`, so `plainOf (impLift f) i = Prod.snd '' {(f i, i)} = {i}` (`Set.image_singleton`), constant in `f`. The plain-bisim conjunct is the constant-`True` relation (`plainOf_labelLoop_true_bisim` shape, on `i ↦ {i}`). The label-separation conjunct mirrors `ws4_label_survives_quotient`: from `R ⟨true⟩ ⟨false⟩`, `⟨true⟩`'s edge `(f ⟨true⟩, ⟨true⟩)` must match `⟨false⟩`'s only edge `(f ⟨false⟩, ⟨false⟩)` with equal first component, but `f ⟨true⟩ ≠ f ⟨false⟩`. C2(2) is `ws4_labelLoop_not_recoverable` at `impLift id = labelLoop`. **Dependencies:** imported `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `toPk`, `ws4_labelLoop_not_recoverable`; `impCar` finite so `toPk` applies with no `hcar`. **The import is the universally-bound `f`; the review greps that no term is named for its content.**

## Outcome classes (per charter §5)

- **GROUND (the WS4 payoff):** `ws4_import_breaks_baseline` (the import breaks the baseline, quantified over all imports, audit e), `ws4_import_quantified` (carried without being named, the plain projection constant in the import, a non-vacuous witness).
- **PARTIAL (pre-registered):** the import breaks the baseline only for a SPECIFIC `f`, not universally (the quantifier does not go through); reported PARTIAL with the shortfall recorded. (Not anticipated: the construction is `∀ f` by design.)
- **No OBSTRUCTED branch:** the import is a transcription of P1's free-label shape, near-certain; the only failure is a DISCIPLINE breach (naming/selecting), which the review catches.
- **Strip test.** Delete "import / love / gaze / seated" from `ws4_import_breaks_baseline` and it is *"for all `Q` and `f : impCar → Q` with `f ⟨true⟩ ≠ f ⟨false⟩`, the labelled self-loops `i ↦ {(f i, i)}` are plain-bisimilar yet not label-bisimilar"*, a quantified free-label `Recoverable` fact; from `ws4_import_quantified`, *"the plain projection of `impLift f` is constant in `f`, and `impLift id` is non-recoverable"*. No name is a term.

## Deliverable

`program-2/series-0/formal/P2S0/ws4.lean`: `import P1`; `impCar`, `attendsI`, `impLift`; `ws4_import_breaks_baseline`, `ws4_import_quantified`. **WS4 seats the import; it is quantified, never named (audit e).** Axiom check: `#print axioms ws4_import_breaks_baseline` reduces through `toPk` to the standard three (no new axiom). **The import is present and acting, a working part at last, held in every theorem and named in none.**
