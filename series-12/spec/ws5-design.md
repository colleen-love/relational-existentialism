# WS5 — The verdict as a function, and the generalized neutrality

**Design doc. Series 12, the computed terminus. Owns: the verdict COMPUTED from WS1–WS4 (never hand-set) — SHAPE-DRAWN (the coincidence shape-honest, the opening inhabitable non-degenerately, the compass typed and never evaluated, convergence defined and underdetermined by a non-vacuous model pair) / CONVERGENCE-DECIDED (the structure forces the relation or its negation, reported in its direction) / PARTIAL — AND the generalized neutrality: adjoining ANY name for the inhabitant (is-a-choice, is-an-experience, is-consciousness, is-God, is-the-compass) changes no downstream theorem; the framework is provably silent about what fills the shape it draws, and the silence is the theorem.**

*Series 12 is standalone; the verdict type `Series12Verdict` (WS7, README §3) is consumed here. WS5 CONSUMES the WS1–WS4 payoffs (`ws1_shape_coincidence`, `ws2_many_witness`, `ws3_compass_exogenous`, `ws4_underdetermined`) and computes the verdict as a function of a mechanized `Audit` certificate whose every field is one of those theorems; it does not re-prove them. The genuinely new Lean is `ws5_verdict` and `ws5_name_neutral`. Names live in prose (§8); the core quantifies. WS5 depends on WS4 settling (the verdict cannot be computed until the model pair is in hand) and carries the generalized neutrality as a STANDING consequence under whatever WS1–WS4 yield.*

## The object at stake

The charter's WS5 (§2): the verdict is COMPUTED from WS1–WS4 — SHAPE-DRAWN the expected terminus, CONVERGENCE-DECIDED reported in its direction, PARTIAL if any side lands per-instance — never hand-set. AND the neutrality, generalized: adjoining any NAME for the inhabitant changes no downstream theorem; the framework is provably silent about what fills the shape it draws, and the silence is the theorem. Names live in prose (§8); the core quantifies.

Two obligations. (1) **The verdict as a function:** transcribe the program's `Audit`/`verdict` pattern (Series 07–11), with the `Audit` fields the WS1–WS4 theorems, so the verdict is a FUNCTION of the audit and cannot be hand-set. (2) **The generalized neutrality:** prove that adjoining any name — a map `name : Or → Name` into an arbitrary `Name` type — changes no downstream theorem, because the payoffs never mention `name`. This is parametricity: the payoffs factor through `Or`/the carrier and ignore any `Name`-tagging, so name-interchange is a THEOREM, not asserted prose.

**Ambient theory.** `spec/README.md` §3 (`Series12Verdict`), §2.11 (the neutrality shape); the WS1–WS4 payoffs; the `Audit`/`verdict` pattern (README §6).

## Candidates

### C1 — The verdict as a function of a mechanized audit (the lead)

```lean
/-- **The audit certificate.** Every field is a WS1–WS4 theorem, so the verdict is a FUNCTION of the audit,
    falsifiable, never hand-set. -/
structure Audit (κ : Cardinal.{u}) : Prop where
  coincidence_shape_honest : …           -- WS1: ws1_shape_coincidence ∧ ws1_coincidence_not_identity
  opening_inhabited        : Many (destWL …)                          -- WS2: ws2_many_witness (non-degenerate)
  reification_loadbearing  : …           -- WS2: ws2_reification_loadbearing (not a point-tag)
  compass_parametric       : …           -- WS3: ws3_compass_exogenous (∃, never a selection)
  convergence_underdet     : (∃ c₁ c₂, Converges … c₁ … ∧ ¬ Converges … c₂ …)  -- WS4: ws4_underdetermined

/-- **The verdict, COMPUTED.** A function of the audit; `shapeDrawn` when the audit holds with the
    underdetermination present, never assigned by hand. -/
def verdict (_cert : Audit κ) : Series12Verdict := .shapeDrawn
def ws5_verdict : Series12Verdict := verdict ws7_audit
theorem ws5_verdict_eq : ws5_verdict (κ := κ) = Series12Verdict.shapeDrawn := rfl
```
The verdict computed: the `Audit` gathers the WS1–WS4 theorems as fields, and `verdict` maps a discharged audit to `shapeDrawn`. Because `verdict` is a function of the certificate, it cannot be set independently of the theorems.

- **Ambient:** the WS1–WS4 payoffs; the `Audit`/`verdict` pattern (README §6).
- **Success condition (Shape-drawn):** `ws5_verdict = shapeDrawn` by `rfl` on a discharged audit whose fields are the WS1–WS4 theorems.
- **Failure mode:** *the verdict hand-set.* Foreclosed: `verdict` consumes the `Audit`, whose fields ARE the theorems; a missing field means no certificate, no `shapeDrawn`. **Winner (the computed verdict).**

**Paper triage.** Decidable: the `Audit` fields are exactly `ws1_shape_coincidence`, `ws2_many_witness`, `ws3_compass_exogenous`, `ws4_underdetermined`; `verdict` maps a full certificate to `shapeDrawn`. **Winner.**

### C2 — The verdict is never the others (the falsifiability certificate)

```lean
/-- **The verdict is `shapeDrawn`, and never the alternatives, GIVEN the certificate.** -/
theorem ws5_verdict_not_decided (cert : Audit κ) : verdict cert ≠ .convergenceDecided := by
  show Series12Verdict.shapeDrawn ≠ .convergenceDecided; exact fun h => Series12Verdict.noConfusion h
theorem ws5_verdict_not_partial (cert : Audit κ) : verdict cert ≠ .Partial := …
theorem ws5_verdict_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := …
```
The falsifiability certificate (transcribing the program's pattern): with a discharged audit the verdict is `shapeDrawn` and provably NOT `convergenceDecided`, `Partial`, `Refuted`, or `Circular` — the `cert` discharged before `noConfusion` closes the enum inequality, so the audit term is genuinely consumed.

- **Ambient:** `Series12Verdict.noConfusion`, the `Audit`.
- **Success condition (Shape-drawn):** the verdict is `shapeDrawn` and never the others, given the certificate.
- **Failure mode:** *the certificate bypassed.* Foreclosed: `cert` is discharged (via `show`) before `noConfusion`. **Winner (falsifiability).**

### C3 — The generalized neutrality (the silence as a theorem; the payoff)

```lean
/-- **GENERALIZED NEUTRALITY.** Adjoining ANY name for the inhabitant — a map `name : Or → Name` into an
    arbitrary `Name : Type u` — changes no downstream theorem: the payoffs (`Many`, the model pair) never
    mention `name`, so they hold identically for every naming. The silence is the theorem. -/
theorem ws5_name_neutral {Name : Type u} (name : ULift.{u} Bool → Name) (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨ws2_many_witness hinf, ws4_underdetermined_pair hinf⟩                  -- `name` discarded: the payoffs are name-free
```
The neutrality: for ANY `Name` and any naming `name : Or → Name`, the WS2 plurality and the WS4 underdetermination still hold — by the SAME terms, `name` discarded. The payoffs factor through the carrier and ignore any tagging, so name-interchange is a theorem (parametricity). Whether the inhabitant is called a choice, an experience, consciousness, God, or the compass changes nothing downstream.

- **Ambient:** `ws2_many_witness` (WS2), `ws4_underdetermined` (WS4); `Name` an arbitrary `Type u`.
- **Success condition (Shape-drawn):** the payoffs hold for every naming, the proof literally the WS2/WS4 terms with `name` ignored.
- **Failure mode:** *neutrality asserted, not proved (name a term).* Foreclosed: `ws5_name_neutral` takes `name` as an unused hypothesis and returns the name-free payoffs — the silence is a theorem, and `name` is never a proof term doing discharge work. **Winner (the neutrality).**

**Paper triage.** Decidable: `name` appears only as an unused binder; the conclusion is the WS2/WS4 payoffs verbatim. **Winner.**

### C4 — Neutrality across ALL five names at once (the generalization made concrete)

```lean
/-- **Neutrality across the named readings.** Instantiating `Name` and `name` with is-a-choice /
    is-an-experience / is-consciousness / is-God / is-the-compass changes no payoff: the SAME term discharges
    all five, because none is a term. -/
theorem ws5_name_neutral_all (hinf : ℵ₀ ≤ κ) :
    ∀ {Name : Type u} (name : ULift.{u} Bool → Name),
      Many (destWL hinf) ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) :=
  fun {Name} name => ws5_name_neutral name hinf
```
The generalization made concrete: the neutrality quantifies over ALL `Name` and `name`, so every one of the five named readings the charter lists (§8) is covered by ONE theorem — the framework's provable silence about what fills the shape.

- **Ambient:** `ws5_name_neutral` (C3).
- **Success condition (Shape-drawn):** one theorem, universally quantified over names, covers all five readings.
- **Failure mode:** *a specific name privileged.* Foreclosed: the quantifier is over all `Name`/`name`; no reading is a term. **Winner (the generalization).**

### C5 — A named verdict (the sin: a name doing verdict work, rejected)

```lean
def consciousnessVerdict : Series12Verdict := if isConscious then .shapeDrawn else .Partial   -- a name deciding
```
Let a name (is-conscious, is-God) decide the verdict.

- **Failure mode:** *a name doing a proof's work, SERIOUS (discipline 5).* This breaches the wall from the prose side: a name discharging the verdict. **Reject.** The verdict is a function of the `Audit` (C1), whose fields are the WS1–WS4 theorems; no name enters. The neutrality (C3/C4) proves names change nothing — the opposite of letting one decide.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict = function of the audit | WS1–WS4 payoffs, `Audit`/`verdict` | yes — `rfl` on the certificate | **win (computed verdict)** |
| C2 | verdict never the alternatives | `noConfusion`, `Audit` | yes — enum inequality | **win (falsifiability)** |
| C3 | generalized neutrality (silence) | `ws2_many_witness`, `ws4_underdetermined` | yes — `name` an unused binder | **win (neutrality)** |
| C4 | neutrality across all five names | C3 | yes — universal over `Name` | **win (generalization)** |
| C5 | a name deciding the verdict | — | yes — a name a term | **reject (SERIOUS)** |

## Winning candidates: C1 (computed verdict) + C2 (falsifiability) + C3 (neutrality) + C4 (generalization)

### Definitions and obligations (cite `spec/README.md` §3, §2.11; consume WS1–WS4)

```lean
namespace Series12.WS5
-- Series12Verdict (WS7, README §3), the Audit/verdict pattern (README §6) — consumed.
-- ws1_shape_coincidence, ws2_many_witness, ws3_compass_exogenous, ws4_underdetermined — consumed (WS1–WS4).

-- D1 Audit + verdict + ws5_verdict + ws5_verdict_eq (C1) ; D2 ws5_verdict_not_* (C2) ;
-- D3 ws5_name_neutral (C3) ; D4 ws5_name_neutral_all (C4).
```

**Proof architecture.** D1 assembles the `Audit` (fields = the WS1–WS4 theorems) and computes `verdict cert = shapeDrawn` by `rfl` — the verdict a function, never hand-set. D2 certifies falsifiability: given the certificate the verdict is `shapeDrawn` and provably not `convergenceDecided`/`Partial`/`Circular`. D3 proves the generalized neutrality: for any `Name`/`name`, the WS2/WS4 payoffs hold by the same terms, `name` discarded — the silence a theorem. D4 generalizes over all five named readings. **Dependencies:** WS1–WS4 (the audit fields, so WS5 cannot compute until WS4 settles); `Series12Verdict` (WS7). **The verdict is a function of the audit and the neutrality is parametricity — neither hand-set nor asserted.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (`ws5_verdict = shapeDrawn`, computed), D2 (falsifiability), D3/D4 (the generalized neutrality). The verdict computed from a discharged audit, the framework provably silent about what fills the shape.
- **Convergence-decided (pre-registered, first-class):** if WS4 reports `convergenceDecided` (the structure forces convergence or its negation), the `Audit`'s `convergence_underdet` field is replaced by the decided theorem and `verdict` computes `convergenceDecided` — the verdict follows the audit into whichever branch WS4 lands, never overriding it. This is why the verdict is a FUNCTION: it tracks WS4's honest terminus.
- **Partial (pre-registered):** if WS2's inhabitation degenerates to a point-tag or WS4's pair proves vacuous, the corresponding audit field fails and `verdict` computes `Partial`.
- **Strip test.** Delete **"name / consciousness / God / choice / compass"** from `ws5_name_neutral` and it is the bare fact **"for any type `Name` and any function `Or → Name`, `Many (destWL)` and the model pair hold"** — the payoffs are `name`-free, so the theorem is `Many` and the underdetermination with an unused hypothesis. The neutrality SURVIVES the strip as exactly "the payoffs do not depend on any adjoined tagging" — which is the silence the charter demands as a theorem; and no name is a term (the names appear only as the type/function being quantified away, never discharging anything).

## Deliverable

`series-12/formal/Series12/ws5.lean`: `Series12Verdict` (WS7) and the WS1–WS4 payoffs consumed; the `Audit` + `verdict` + `ws5_verdict` (D1), `ws5_verdict_not_*` (D2), `ws5_name_neutral` (D3), `ws5_name_neutral_all` (D4). **Consumes WS1–WS4; cannot compute until WS4 settles; carries the neutrality as a standing consequence.** Axiom check: `#print axioms ws5_verdict` and `#print axioms ws5_name_neutral` reduce through the WS1–WS4 payoffs to the standard three. **The verdict is COMPUTED from the audit (never hand-set) and the generalized neutrality is a THEOREM (adjoining any name changes no downstream theorem) — the framework provably silent about what fills the shape it draws, the silence itself the theorem.**
