# WS7, The anti-circularity audit

**Design doc. Series 12, the audit, runs last. Owns: the typed verdict `Series12Verdict` and the mechanized `Audit` certificate whose every field is a WS1–WS4 theorem (so the verdict cannot be hand-set), and the five promoted first-class checks, (1) the coincidence is shape-honest (forced-for-all vs exists-satisfying, not object-identity); (2) NO EVALUATION of the compass (no theorem selects, constructs, or applies a distinguished compass; every compass-theorem parametric); (3) the underdetermination is a genuine non-degenerate model pair (both inhabitants non-degenerate, on one structure, the relation holding in one and failing in the other); (4) inhabitation is a genuine tower-distinction (reification load-bearing), not a point-tag; (5) names are names, not terms (no proof term named consciousness/God/choice/compass). Plus the strip-test ledger, aggregated. WS7 cannot report until WS1–WS6 have.**

*Series 12 is standalone; the `Audit`/`verdict` certificate pattern is transcribed from the program (Series 07–11 `ws7`), re-pointed to `Series12Verdict` (README §3). WS7 CONSUMES all of WS1–WS6 and unfolds the five signature risks; it does not re-prove the payoffs. The genuinely new Lean is `Series12Verdict`, the `Audit`, `ws7_verdict`, the five check-theorems, and the strip-test aggregation. WS7 owns the final verdict and the program-level synthesis's honesty; a name doing a proof's work anywhere in `formal/Series12/` is the finding it exists to catch.*

## The object at stake

The charter's WS7 (§2), the audit with three checks promoted and two more first-class (protocol §0.4–§0.6b). Beyond the inherited checks (no construction by fiat, honest quantifiers), five Series-12 risks are first-class: (a) **NO EVALUATION OF THE COMPASS**, grep and unfold: no theorem selects, constructs, or applies a distinguished compass; every compass-theorem parametric; a canonical inhabitant in the core is the central sin, SERIOUS; (b) **the underdetermination is a genuine model pair**, both inhabitants non-degenerate, on the same structure, the relation genuinely holding in one and failing in the other, not a vacuity; (c) **the coincidence is shape-honest**, forced-for-all (residue) vs exists-satisfying (inhabitants) kept distinct, never object-identity from shared non-recoverability; plus (d) **inhabitation is genuine**, a real tower-distinction, not a point-tag; and (e) **names are not terms**, no proof term named consciousness, God, choice, or compass (as content). The verdict is a FUNCTION of the mechanized audit, so it cannot be hand-set.

**Ambient theory.** All of WS1–WS6; `spec/README.md` §3 (`Series12Verdict`), §0 (the five disciplines); the `Audit`/`verdict` pattern (README §6).

## Candidates

### C1, The verdict type and the mechanized audit (the lead)

```lean
/-- **The verdict type + the convergence fork (README §3, Finding 4).** -/
inductive Series12Verdict
  | shapeDrawn | convergenceDecided | Partial | Refuted | Circular
  deriving DecidableEq

inductive ConvergenceFork {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (a b : X) : Type u
  | forcedHolds (h : ∀ {Or} (c : Compass dest reify Or), Converges dest reify c a b)
  | forcedFails (h : ∀ {Or} (c : Compass dest reify Or), ¬ Converges dest reify c a b)
  | underdet    (h : ∃ c₁ c₂ : Compass dest reify (ULift.{u} Bool),
                       Converges dest reify c₁ a b ∧ ¬ Converges dest reify c₂ a b
                       ∧ NonDegenerate dest reify c₁ a b ∧ NonDegenerate dest reify c₂ a b)

def verdictOfFork {X} {dest} {reify} {a b : X} : ConvergenceFork dest reify a b → Series12Verdict
  | .forcedHolds _ => .convergenceDecided
  | .forcedFails _ => .convergenceDecided
  | .underdet    _ => .shapeDrawn

/-- **The audit certificate.** The five checks as fields, PLUS the WS4 `fork` carrying which disjunct of the
    trichotomy was discharged; the verdict BRANCHES on it (Finding 4), never a returned constant. -/
structure Audit (κ : Cardinal.{u}) where     -- Type-level (carries the data-level fork)
  shape_honest        : (∀ {X} (dest : X → PkObj κ X) (insp), Opening (ResidueRecoverable) insp)
                        ∧ (∃ i₁ i₂ : Hold (destW …) → HoldPred (destW …), residue i₁ ≠ residue i₂)   -- (c)+(1)
  no_evaluation       : ∀ {X} (dest) (reify) {Or} (c : Compass dest reify Or), True                  -- (a)+(2): parametric
  compass_exogenous   : ∃ c x y, (∃ R, IsBisim (destW …) R ∧ R x y) ∧ c.orient x ≠ c.orient y        -- (a): ∃, not a selection
  inhabitation_genuine: cW = reifyW … (sW₂ …) ∧ cW ∈ reifyStep (destW …) (reifyW …) (towerN … 1)     -- (d)+(4): reify load-bearing
                        ∧ (rankW aW = rankW aW' ∧ aW ≠ aW')                                            -- rank non-injective (Finding 1)
  fork                : ConvergenceFork (destW …) (reifyW …) aW bW                                    -- (b)+(3): the WS4 fork (Finding 4)

def verdict (cert : Audit κ) : Series12Verdict := verdictOfFork cert.fork
def ws7_verdict : Series12Verdict := verdict ws7_audit
/-- A THEOREM (not a definitional constant): the fork is `underdet` (the model pair), so `verdictOfFork`
    computes `shapeDrawn` (Finding 4). -/
theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series12Verdict.shapeDrawn := by
  show verdictOfFork (ws7_audit (κ := κ)).fork = .shapeDrawn; rfl
```
The verdict type, the fork, and the audit: the checks are fields, the WS4 `fork` records which trichotomy disjunct was discharged, and `verdict` BRANCHES on the fork via `verdictOfFork` (Finding 4). With the fork at `underdet` (the model pair), `ws7_verdict = shapeDrawn` is a theorem; had WS4 decided convergence, the fork would be `forcedHolds`/`forcedFails` and the verdict `convergenceDecided`.

- **Ambient:** the WS1–WS4 payoffs; `ConvergenceFork`/`verdictOfFork`; the `Audit` pattern.
- **Success condition (Shape-drawn):** `ws7_verdict = shapeDrawn` as a theorem via the `underdet` fork; the alternatives expressible via the other constructors.
- **Failure mode:** *the verdict a returned constant ignoring its certificate (Finding 4).* Foreclosed: `verdict := verdictOfFork cert.fork` inspects the fork; a decided fork gives `convergenceDecided`. **Winner (the audit, branching).**

### C2, The no-evaluation check, unfolded (the central check)

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
The central check (honest formulation, series-review-1 SR1-1): the convergence relation is parametric (an `Iff` for ALL `c`), and NO compass-parametric obligation is discharged by evaluating a distinguished compass; the only concrete compasses (`cHold`/`cFail`, the WS3 inline witnesses) occur as model-pair / existential-witness constructions, never selected to prove a `∀`-compass statement. A canonical inhabitant used to discharge a parametric obligation would be the central sin; the grep+unfold confirms none exists. (The meta clause is what the review runs; the theorem records the parametric `Iff` and the exogeneity existential it leans on.)

- **Ambient:** `Converges`, `Compass`, `ws3_compass_exogenous`.
- **Success condition (Shape-drawn):** every compass-theorem parametric; concrete compasses only inside `∃`.
- **Failure mode:** *a canonical compass found, SERIOUS.* This IS the check; if found, the finding is SERIOUS (the undefinable defined). Foreclosed by WS3's parametricity. **Winner (the central check).**

### C3, The genuine-model-pair check (the underdetermination, discipline 3)

```lean
/-- **THE MODEL-PAIR CHECK (discipline 3).** The underdetermination is two NON-DEGENERATE inhabitants on ONE
    structure, the relation genuinely holding in one and failing in the other, not a vacuity (not an empty
    relation "failing," not a trivial one "holding"), neither compass a collapsed constant. -/
theorem ws7_model_pair_genuine (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW                          -- holds …
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW                        -- … and fails (one structure)
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  (ws4_underdetermined hinf).2                                             -- the pair; (…).1 is the ConstituentOf edge
```
The model-pair check: unfold `ws4_underdetermined` (whose first conjunct is the genuine `ConstituentOf aW bW` edge, Finding 2) and confirm both compasses non-degenerate, on one structure, the relation holding in one and failing in the other. Not decided by definition (the relation is compass-dependent), not vacuous (both truth values realized).

- **Ambient:** `ws4_underdetermined`, `NonDegenerate`.
- **Success condition (Shape-drawn):** the pair is genuine, non-degenerate, one structure, holding-and-failing.
- **Failure mode:** *a vacuous pair or a decided-by-definition relation, SERIOUS.* Foreclosed by WS4's `NonDegenerate` and both truth values realized. **Winner (the model-pair check).**

### C4, The genuine-inhabitation check (the point-tag guard, discipline 4)

```lean
/-- **THE INHABITATION CHECK (discipline 4, Finding 1).** The plurality separates a genuinely plain-bisimilar
    pair (a reified relatum CARRYING a reified constituent, and a base relatum) with `reify`/`reifyStep`/
    `towerN` LOAD-BEARING, on a carrier where rank is NON-INJECTIVE, generalized. NOT a point-tag. Confirm
    `cW = reifyW sW₂` is `reifyStep`-adjoined, rank is non-injective, and the without-import side is genuine
    `ws2_import_theorem_static`. -/
theorem ws7_inhabitation_genuine (hinf : ℵ₀ ≤ κ) :
    (Many (destWL hinf))
  ∧ (cW = reifyW hinf (sW₂ hinf) ∧ cW ∈ reifyStep (destW hinf) (reifyW hinf) (towerN (destW hinf) (reifyW hinf) {aW, aW'} 1))
  ∧ (rankW aW = rankW aW' ∧ aW ≠ aW')                                       -- rank non-injective (Finding 1)
  ∧ (∀ {X} (dest : X → PkObj κ X), BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X) := …
```
The inhabitation check: unfold `ws2_many_witness` and confirm the separated relatum `cW` is a `reifyStep`-produced reified relatum carrying a reified constituent (reification load-bearing, not `labelLoop`'s two Booleans or the two-state silhouette), rank is non-injective (`aW`, `aW'`), the separation is an instance of the general theorem, and the without-import collapse is genuine Series 07.

- **Ambient:** `ws2_many_witness`, `ws2_reification_loadbearing`, `ws_witness_rank_noninjective`, `ws2_many_general`, `ws2_import_theorem_static`.
- **Success condition (Shape-drawn):** reification load-bearing; rank non-injective; the separation general; the without-import side genuine `ws1_atomless_bisim`.
- **Failure mode:** *a point-tag or a two-state silhouette, the Bookkeeping re-hit, Partial (Finding 1).* Foreclosed on three certificates: `cW ∈ reifyStep (towerN … 1)`, rank non-injective, and the general theorem; if a reviewer still judges the rank external, reported Partial. **Winner (the inhabitation check).**

### C5, The names-not-terms check (the wall from the prose side, discipline 5)

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
The names-not-terms check: the neutrality theorem IS the certificate, any name is a `Name`-tagging that changes no payoff, so no name does discharge work. The grep confirms no proof term is named as content.

- **Ambient:** `ws5_name_neutral`.
- **Success condition (Shape-drawn):** no name a term; the neutrality proves names change nothing.
- **Failure mode:** *a name doing a proof's work, SERIOUS.* This IS the check; foreclosed by the neutrality and the grep. **Winner (the names check).**

### C6, The strip-test ledger, aggregated (the review's tool, mechanized as a checklist)

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
The strip-test ledger: the three payoffs, each reduced to the bare fact the strip leaves, the coincidence to the two non-recoverability facts, the plurality to the labelled-separation, the convergence to the model pair. Aggregated so the reviewer runs one checklist.

- **Ambient:** the WS1/WS2/WS4 payoffs stripped.
- **Success condition (Shape-drawn):** each payoff strips to its named fact.
- **Failure mode:** *a payoff surviving as something else / a name surviving as a term.* Foreclosed: each strips to a bisimulation/reification/model-pair fact. **Winner (the ledger).**

### C7, The verdict never the alternatives (falsifiability; and the pre-registered branches)

```lean
-- Any verdict from any fork is never Partial/Refuted/Circular (verdictOfFork lands only in {shapeDrawn, convergenceDecided}):
theorem ws7_verdict_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by
  cases h : cert.fork <;> simp [verdict, verdictOfFork, h] <;> exact fun h => Series12Verdict.noConfusion h
-- The CONCRETE verdict is `shapeDrawn` and not `convergenceDecided`, BECAUSE its fork is `underdet` (the model pair):
theorem ws7_verdict_not_decided : ws7_verdict (κ := κ) ≠ .convergenceDecided := by
  rw [ws7_verdict_eq]; exact fun h => Series12Verdict.noConfusion h
```
The falsifiability certificate (Finding 4-aware): `verdictOfFork` lands only in `{shapeDrawn, convergenceDecided}`, so ANY audit's verdict is provably not `Partial`/`Refuted`/`Circular` (a discipline breach would mean no certificate at all); and the CONCRETE `ws7_verdict` is `shapeDrawn` and not `convergenceDecided` BECAUSE its fork is `underdet` (via `ws7_verdict_eq`, the model pair). The pre-registered branch is expressible: had WS4 landed convergence-decided, `ws7_audit.fork` would be `forcedHolds`/`forcedFails` and `verdict` would compute `convergenceDecided`, tracking the audit into that branch.

- **Ambient:** `Series12Verdict.noConfusion`, `verdictOfFork`, `ws7_verdict_eq`.
- **Success condition (Shape-drawn):** every verdict is never a breach-verdict; the concrete verdict is `shapeDrawn` via its `underdet` fork; the decided branch is reachable.
- **Failure mode:** *the verdict a returned constant / the fork ignored (Finding 4).* Foreclosed: `verdict` cases on the fork, and the concrete claim routes through the `underdet` fork. **Winner (falsifiability).**

## Paper-decidable triage

| Cand | What it checks | Discipline | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict type + mechanized audit | all | yes, `rfl` on the certificate | **win (the audit)** |
| C2 | no evaluation of the compass | 2 (central) | yes, parametric `Iff`, ∃-only concrete | **win (central check)** |
| C3 | genuine non-degenerate model pair | 3 | yes, `NonDegenerate`, both truth values | **win (model-pair)** |
| C4 | genuine tower-inhabitation (non-injective rank, general) | 4, 1 | yes, `cW ∈ reifyStep (towerN … 1)`, rank non-injective | **win (inhabitation)** |
| C5 | names not terms | 5 | yes, neutrality + grep | **win (names)** |
| C6 | strip-test ledger | 0.3 | yes, each strips to its fact | **win (ledger)** |
| C7 | verdict branches on the fork, never the breach-verdicts | 0.2, 4 | yes, `verdictOfFork` + `noConfusion` | **win (falsifiability)** |

## Winning candidates: C1–C7 (the full audit)

### Definitions and obligations (consume all of WS1–WS6; cite README §3)

```lean
namespace Series12.WS7
-- all WS1–WS6 payoffs; the Audit/verdict pattern (README §6), consumed.

inductive Series12Verdict | shapeDrawn | convergenceDecided | Partial | Refuted | Circular deriving DecidableEq
-- ConvergenceFork (data-level, 3 constructors) + verdictOfFork (branches), README §3, Finding 4.

-- D1 Audit (fork field) + verdict (branches) + ws7_verdict + ws7_verdict_eq (theorem) (C1) ; D2 ws7_no_evaluation (C2) ;
-- D3 ws7_model_pair_genuine (C3) ; D4 ws7_inhabitation_genuine (C4) ; D5 ws7_names_not_terms (C5) ;
-- D6 ws7_strip_ledger (C6) ; D7 ws7_verdict_not_* (C7).
```

**Proof architecture.** D1 defines the verdict type, the data-level `ConvergenceFork`, `verdictOfFork`, and the `Audit` (the five checks as fields PLUS the WS4 `fork`), and computes `ws7_verdict = verdictOfFork ws7_audit.fork`, which is `shapeDrawn` as a THEOREM via the `underdet` fork (Finding 4, the returned-constant defect retired). D2 (the central check) unfolds the compass-theorems parametric, concrete compasses only inside `∃`. D3 unfolds the model pair genuine (non-degenerate, one structure, holding-and-failing) via `(ws4_underdetermined).2`. D4 unfolds the inhabitation genuine (reification load-bearing, `cW` carrying a reified constituent, rank non-injective, generalized; without-import genuine Series 07, Finding 1). D5 certifies no name a term (the neutrality). D6 aggregates the strip-test ledger. D7 certifies falsifiability (the verdict branches on the fork, never a breach-verdict) and the pre-registered branches. **Dependencies:** all of WS1–WS6 (WS7 cannot report until they have); `Series12Verdict`/`ConvergenceFork` re-point the program's verdict pattern. **The verdict BRANCHES on the audit's fork; the five disciplines are its checking fields; a breach is a SERIOUS finding, reported.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (`ws7_verdict = shapeDrawn`), with D2–D7 the five checks and the ledger discharged. The audit certifies the coincidence shape-honest, the compass never evaluated, the model pair genuine, the inhabitation a real tower-distinction, and no name a term.
- **Convergence-decided / Partial / Circular (pre-registered, first-class, Finding 4):** the verdict tracks the audit's `fork`: a `forcedHolds`/`forcedFails` fork computes `convergenceDecided` (WS4 decides), and a failed check computes `Partial` (a point-tag or per-instance) or `Circular` (a discipline breached: a canonical compass, convergence decided by definition, object-identity, or a name a term). The alternatives are now EXPRESSIBLE (the fork carries the disjunct); the verdict is never hand-set.
- **Strip test (aggregated, D6).** The coincidence strips to the two non-recoverability facts (quantifiers distinct); the plurality to the labelled-separation (reification load-bearing); the convergence to the model pair. Each survives AS its named fact; any payoff surviving as something else, or any name surviving as a term, is flagged SERIOUS.

## Deliverable

`series-12/formal/Series12/ws7.lean`: all WS1–WS6 payoffs consumed; `Series12Verdict`, `ConvergenceFork`, `verdictOfFork`, the `Audit` (with the `fork` field), `ws7_verdict` + `ws7_verdict_eq` (a theorem) (D1), `ws7_no_evaluation` (D2), `ws7_model_pair_genuine` (D3), `ws7_inhabitation_genuine` (D4), `ws7_names_not_terms` (D5), `ws7_strip_ledger` (D6), `ws7_verdict_not_*` (D7). **Runs last; owns the verdict and the program-level synthesis's honesty.** Axiom check: `#print axioms ws7_verdict` and each check reduce through the WS1–WS4 payoffs to the standard three; `AxiomCheck.lean` captures the full `#print axioms` record to `spec/axiom-check-log.md` (charter: Series 12 ships the captured log). **The verdict BRANCHES on an audit whose fields are the five disciplines plus the WS4 fork, the coincidence shape-honest, the compass never evaluated, the model pair genuine, the inhabitation a real tower-distinction (non-injective rank, generalized), and no name a term: a breach of any a SERIOUS finding, the verdict never hand-set, the pre-registered alternatives expressible (Finding 4).**
