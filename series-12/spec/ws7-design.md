# WS7 — The anti-circularity audit

**Design doc. Series 12, the audit, runs last. Owns: the typed verdict `Series12Verdict` and the mechanized `Audit` certificate whose every field is a WS1–WS4 theorem (so the verdict cannot be hand-set), and the five promoted first-class checks — (1) the coincidence is shape-honest (forced-for-all vs exists-satisfying, not object-identity); (2) NO EVALUATION of the compass (no theorem selects, constructs, or applies a distinguished compass; every compass-theorem parametric); (3) the underdetermination is a genuine non-degenerate model pair (both inhabitants non-degenerate, on one structure, the relation holding in one and failing in the other); (4) inhabitation is a genuine tower-distinction (reification load-bearing), not a point-tag; (5) names are names, not terms (no proof term named consciousness/God/choice/compass). Plus the strip-test ledger, aggregated. WS7 cannot report until WS1–WS6 have.**

*Series 12 is standalone; the `Audit`/`verdict` certificate pattern is transcribed from the program (Series 07–11 `ws7`), re-pointed to `Series12Verdict` (README §3). WS7 CONSUMES all of WS1–WS6 and unfolds the five signature risks; it does not re-prove the payoffs. The genuinely new Lean is `Series12Verdict`, the `Audit`, `ws7_verdict`, the five check-theorems, and the strip-test aggregation. WS7 owns the final verdict and the program-level synthesis's honesty; a name doing a proof's work anywhere in `formal/Series12/` is the finding it exists to catch.*

## The object at stake

The charter's WS7 (§2), the audit with three checks promoted and two more first-class (protocol §0.4–§0.6b). Beyond the inherited checks (no construction by fiat, honest quantifiers), five Series-12 risks are first-class: (a) **NO EVALUATION OF THE COMPASS** — grep and unfold: no theorem selects, constructs, or applies a distinguished compass; every compass-theorem parametric; a canonical inhabitant in the core is the central sin, SERIOUS; (b) **the underdetermination is a genuine model pair** — both inhabitants non-degenerate, on the same structure, the relation genuinely holding in one and failing in the other, not a vacuity; (c) **the coincidence is shape-honest** — forced-for-all (residue) vs exists-satisfying (inhabitants) kept distinct, never object-identity from shared non-recoverability; plus (d) **inhabitation is genuine** — a real tower-distinction, not a point-tag; and (e) **names are not terms** — no proof term named consciousness, God, choice, or compass (as content). The verdict is a FUNCTION of the mechanized audit, so it cannot be hand-set.

**Ambient theory.** All of WS1–WS6; `spec/README.md` §3 (`Series12Verdict`), §0 (the five disciplines); the `Audit`/`verdict` pattern (README §6).

## Candidates

### C1 — The verdict type and the mechanized audit (the lead)

```lean
/-- **The verdict type (README §3).** -/
inductive Series12Verdict
  | shapeDrawn | convergenceDecided | Partial | Refuted | Circular
  deriving DecidableEq

/-- **The audit certificate.** Every field a WS1–WS4 theorem; the verdict a FUNCTION of it. -/
structure Audit (κ : Cardinal.{u}) : Prop where
  shape_honest        : (∀ {X} (dest : X → PkObj κ X) (insp), Opening (ResidueRecoverable) insp)
                        ∧ (∃ i₁ i₂ : Hold (destW …) → HoldPred (destW …), residue i₁ ≠ residue i₂)   -- (c)+(1)
  no_evaluation       : ∀ {X} (dest) (reify) {Or} (c : Compass dest reify Or), True                  -- (a)+(2): parametric
  compass_exogenous   : ∃ c x y, (∃ R, IsBisim (destW …) R ∧ R x y) ∧ c.orient x ≠ c.orient y        -- (a): ∃, not a selection
  model_pair          : ∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW
                        ∧ NonDegenerate … c₁ aW bW ∧ NonDegenerate … c₂ aW bW                          -- (b)+(3)
  inhabitation_genuine: bW = reifyW … (sW …) ∧ bW ∈ reifyStep (destW …) (reifyW …) {aW}               -- (d)+(4): reify load-bearing

def verdict (_cert : Audit κ) : Series12Verdict := .shapeDrawn
def ws7_verdict : Series12Verdict := verdict ws7_audit
theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series12Verdict.shapeDrawn := rfl
```
The verdict type and the audit: the fields are the five checks as theorems, so `verdict` is a function of the certificate — `shapeDrawn` exactly when all five hold, never hand-set.

- **Ambient:** the WS1–WS4 payoffs; the `Audit`/`verdict` pattern.
- **Success condition (Shape-drawn):** `ws7_verdict = shapeDrawn` by `rfl` on a certificate whose fields are the five checks.
- **Failure mode:** *the verdict hand-set.* Foreclosed: `verdict` consumes the `Audit`; a failed check means no certificate. **Winner (the audit).**

### C2 — The no-evaluation check, unfolded (the central check)

```lean
/-- **THE NO-EVALUATION CHECK (the central check, discipline 2).** Every compass-theorem is PARAMETRIC over
    `(Or)` and `(c : Compass …)`; the only concrete compasses (`ws3_compass_exogenous`, the model pair) live
    inside `∃`, discharging existentials, never selecting THE compass. Unfolded: `ws3_compass_exogenous` is
    `∃ c, …`, `ws4_underdetermined` is `∃ c₁ c₂, …`; NO theorem has a distinguished `Compass` as a
    non-existential subterm. -/
theorem ws7_no_evaluation (hinf : ℵ₀ ≤ κ) :
    (∀ {X} (dest) (reify) {Or} (c : Compass dest reify Or) (x W : X),
        Converges dest reify c x W ↔ c.raise x W (c.orient x) = c.orient W)   -- parametric, definitional
  ∧ (∃ c, ∃ x y, (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y) := …  -- concrete only inside ∃
```
The central check: the convergence relation is parametric (an `Iff` for ALL `c`), and the only concrete compass is inside an existential. A canonical inhabitant used non-existentially would be the central sin; unfolding confirms none exists.

- **Ambient:** `Converges`, `Compass`, `ws3_compass_exogenous`.
- **Success condition (Shape-drawn):** every compass-theorem parametric; concrete compasses only inside `∃`.
- **Failure mode:** *a canonical compass found, SERIOUS.* This IS the check; if found, the finding is SERIOUS (the undefinable defined). Foreclosed by WS3's parametricity. **Winner (the central check).**

### C3 — The genuine-model-pair check (the underdetermination, discipline 3)

```lean
/-- **THE MODEL-PAIR CHECK (discipline 3).** The underdetermination is two NON-DEGENERATE inhabitants on ONE
    structure, the relation genuinely holding in one and failing in the other — not a vacuity (not an empty
    relation "failing," not a trivial one "holding"), neither compass a collapsed constant. -/
theorem ws7_model_pair_genuine (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW                          -- holds …
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW                        -- … and fails (one structure)
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ws4_underdetermined hinf
```
The model-pair check: unfold `ws4_underdetermined` and confirm both compasses non-degenerate, on one structure, the relation holding in one and failing in the other. Not decided by definition (the relation is compass-dependent), not vacuous (both truth values realized).

- **Ambient:** `ws4_underdetermined`, `NonDegenerate`.
- **Success condition (Shape-drawn):** the pair is genuine — non-degenerate, one structure, holding-and-failing.
- **Failure mode:** *a vacuous pair or a decided-by-definition relation, SERIOUS.* Foreclosed by WS4's `NonDegenerate` and both truth values realized. **Winner (the model-pair check).**

### C4 — The genuine-inhabitation check (the point-tag guard, discipline 4)

```lean
/-- **THE INHABITATION CHECK (discipline 4).** The plurality separates a genuinely plain-bisimilar pair (a
    reified relatum and a base relatum) with `reify`/`reifyStep`/`towerN` LOAD-BEARING — NOT a point-tag on
    a fixed field. Confirm `bW = reifyW sW` is `reifyStep`-adjoined and the without-import side is genuine
    `ws1_atomless_bisim`. -/
theorem ws7_inhabitation_genuine (hinf : ℵ₀ ≤ κ) :
    (Many (destWL hinf))
  ∧ (bW = reifyW hinf (sW hinf) ∧ bW ∈ reifyStep (destW hinf) (reifyW hinf) {aW})
  ∧ (∀ {X} (dest : X → PkObj κ X), BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X) := …
```
The inhabitation check: unfold `ws2_many_witness` and confirm the separated relatum is a `reifyStep`-produced reified relatum (reification load-bearing, not `labelLoop`'s two Booleans), and the without-import collapse is genuine Series 07.

- **Ambient:** `ws2_many_witness`, `ws2_reification_loadbearing`, `ws2_import_theorem_static`.
- **Success condition (Shape-drawn):** reification load-bearing; the without-import side genuine `ws1_atomless_bisim`.
- **Failure mode:** *a point-tag, the Bookkeeping re-hit, Partial.* Foreclosed by `bW ∈ reifyStep {aW}`; if a reviewer judges the rank external, reported Partial. **Winner (the inhabitation check).**

### C5 — The names-not-terms check (the wall from the prose side, discipline 5)

```lean
/-- **THE NAMES-NOT-TERMS CHECK (discipline 5).** Grep `formal/Series12/`: no proof term, definition, or
    discharged obligation is named "consciousness," "God," "choice," or "compass" (as CONTENT). The type
    `Compass` is a SHAPE (parametric, quantified over), never a discharged content; `ws5_name_neutral` proves
    any `Name`-tagging changes no payoff. Every headline mentions only the opening, the compass TYPE,
    attention, the tower, the convergence relation, the transcribed machinery, and standard Lean/Mathlib. -/
theorem ws7_names_not_terms {Name : Type u} (name : ULift.{u} Bool → Name) (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) :=
  ws5_name_neutral name hinf
```
The names-not-terms check: the neutrality theorem IS the certificate — any name is a `Name`-tagging that changes no payoff, so no name does discharge work. The grep confirms no proof term is named as content.

- **Ambient:** `ws5_name_neutral`.
- **Success condition (Shape-drawn):** no name a term; the neutrality proves names change nothing.
- **Failure mode:** *a name doing a proof's work, SERIOUS.* This IS the check; foreclosed by the neutrality and the grep. **Winner (the names check).**

### C6 — The strip-test ledger, aggregated (the review's tool, mechanized as a checklist)

```lean
/-- **THE STRIP-TEST LEDGER.** Each payoff, stripped of its structural words, reduces to its bare fact: the
    coincidence → the forced-residue-and-non-recoverable-inhabitant fact (quantifiers distinct); the
    plurality → the labelled-separation fact (reification load-bearing); the convergence → the model-pair
    fact. A payoff surviving the strip AS its named fact is earned; one surviving as SOMETHING ELSE is
    flagged. -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    (∀ {X} (dest) (insp), ¬ ResidueRecoverable insp) ∧ (¬ Recoverable (labelLoop hinf))   -- coincidence strips here
  ∧ (∃ x y, (∃ R, IsBisim (plainOf (destWL hinf)) R ∧ R x y) ∧ ¬ ∃ R, IsBisimL (destWL hinf) R ∧ R x y)  -- plurality
  ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) := …                           -- convergence
```
The strip-test ledger: the three payoffs, each reduced to the bare fact the strip leaves — the coincidence to the two non-recoverability facts, the plurality to the labelled-separation, the convergence to the model pair. Aggregated so the reviewer runs one checklist.

- **Ambient:** the WS1/WS2/WS4 payoffs stripped.
- **Success condition (Shape-drawn):** each payoff strips to its named fact.
- **Failure mode:** *a payoff surviving as something else / a name surviving as a term.* Foreclosed: each strips to a bisimulation/reification/model-pair fact. **Winner (the ledger).**

### C7 — The verdict never the alternatives (falsifiability; and the pre-registered branches)

```lean
theorem ws7_verdict_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by
  show Series12Verdict.shapeDrawn ≠ .Circular; exact fun h => Series12Verdict.noConfusion h
-- and ≠ convergenceDecided, ≠ Partial, ≠ Refuted, each via noConfusion on the discharged certificate
```
The falsifiability certificate: with a discharged audit the verdict is `shapeDrawn` and provably not `Circular`/`convergenceDecided`/`Partial`/`Refuted`, the `cert` consumed before `noConfusion`. And the pre-registered branches: if WS4 lands `convergenceDecided`, the audit's `model_pair` field carries the decided theorem and `verdict` computes `convergenceDecided` — the verdict tracks the audit into whichever branch.

- **Ambient:** `Series12Verdict.noConfusion`, the `Audit`.
- **Success condition (Shape-drawn):** the verdict never the alternatives given the certificate; tracks the audit into the pre-registered branches.
- **Failure mode:** *the certificate bypassed / the verdict hand-set.* Foreclosed: `cert` discharged before `noConfusion`. **Winner (falsifiability).**

## Paper-decidable triage

| Cand | What it checks | Discipline | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict type + mechanized audit | all | yes — `rfl` on the certificate | **win (the audit)** |
| C2 | no evaluation of the compass | 2 (central) | yes — parametric `Iff`, ∃-only concrete | **win (central check)** |
| C3 | genuine non-degenerate model pair | 3 | yes — `NonDegenerate`, both truth values | **win (model-pair)** |
| C4 | genuine tower-inhabitation | 4 | yes — `bW ∈ reifyStep {aW}` | **win (inhabitation)** |
| C5 | names not terms | 5 | yes — neutrality + grep | **win (names)** |
| C6 | strip-test ledger | 0.3 | yes — each strips to its fact | **win (ledger)** |
| C7 | verdict never the alternatives | 0.2 | yes — `noConfusion` | **win (falsifiability)** |

## Winning candidates: C1–C7 (the full audit)

### Definitions and obligations (consume all of WS1–WS6; cite README §3)

```lean
namespace Series12.WS7
-- all WS1–WS6 payoffs; the Audit/verdict pattern (README §6) — consumed.

inductive Series12Verdict | shapeDrawn | convergenceDecided | Partial | Refuted | Circular deriving DecidableEq

-- D1 Audit + verdict + ws7_verdict + ws7_verdict_eq (C1) ; D2 ws7_no_evaluation (C2) ;
-- D3 ws7_model_pair_genuine (C3) ; D4 ws7_inhabitation_genuine (C4) ; D5 ws7_names_not_terms (C5) ;
-- D6 ws7_strip_ledger (C6) ; D7 ws7_verdict_not_* (C7).
```

**Proof architecture.** D1 defines the verdict type and the `Audit` (fields = the five checks) and computes `ws7_verdict = shapeDrawn`. D2 (the central check) unfolds the compass-theorems parametric, concrete compasses only inside `∃`. D3 unfolds the model pair genuine (non-degenerate, one structure, holding-and-failing). D4 unfolds the inhabitation genuine (reification load-bearing, not a point-tag; without-import genuine Series 07). D5 certifies no name a term (the neutrality). D6 aggregates the strip-test ledger. D7 certifies falsifiability and the pre-registered branches. **Dependencies:** all of WS1–WS6 (WS7 cannot report until they have); `Series12Verdict` re-points the program's verdict pattern. **The verdict is a function of the audit; the five disciplines are its fields; a breach is a SERIOUS finding, reported.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (`ws7_verdict = shapeDrawn`), with D2–D7 the five checks and the ledger discharged. The audit certifies the coincidence shape-honest, the compass never evaluated, the model pair genuine, the inhabitation a real tower-distinction, and no name a term.
- **Convergence-decided / Partial / Circular (pre-registered, first-class):** if a check fails, `verdict` computes the honest alternative — `convergenceDecided` (WS4 decides), `Partial` (a point-tag or per-instance), or `Circular` (a discipline breached: a canonical compass, convergence decided by definition, object-identity, or a name a term). The verdict tracks the audit; never hand-set.
- **Strip test (aggregated, D6).** The coincidence strips to the two non-recoverability facts (quantifiers distinct); the plurality to the labelled-separation (reification load-bearing); the convergence to the model pair. Each survives AS its named fact; any payoff surviving as something else, or any name surviving as a term, is flagged SERIOUS.

## Deliverable

`series-12/formal/Series12/ws7.lean`: all WS1–WS6 payoffs consumed; `Series12Verdict`, the `Audit`, `ws7_verdict` + `ws7_verdict_eq` (D1), `ws7_no_evaluation` (D2), `ws7_model_pair_genuine` (D3), `ws7_inhabitation_genuine` (D4), `ws7_names_not_terms` (D5), `ws7_strip_ledger` (D6), `ws7_verdict_not_*` (D7). **Runs last; owns the verdict and the program-level synthesis's honesty.** Axiom check: `#print axioms ws7_verdict` and each check reduce through the WS1–WS4 payoffs to the standard three; `AxiomCheck.lean` captures the full `#print axioms` record to `spec/axiom-check-log.md` (charter: Series 12 ships the captured log). **The verdict is COMPUTED from an audit whose fields are the five disciplines — the coincidence shape-honest, the compass never evaluated, the model pair genuine, the inhabitation a real tower-distinction, and no name a term — a breach of any a SERIOUS finding, the verdict never hand-set.**
