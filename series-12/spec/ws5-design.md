# WS5, The verdict as a function, and the generalized neutrality

**Design doc. Series 12, the computed verdict. Owns: the verdict COMPUTED from WS1–WS4 (never hand-set), SHAPE-DRAWN (the coincidence shape-honest, the opening inhabitable non-degenerately, the compass typed and never evaluated, convergence defined and underdetermined by a non-vacuous model pair) / CONVERGENCE-DECIDED (the structure forces the relation or its negation, reported in its direction) / PARTIAL, AND the generalized neutrality: adjoining ANY name for the inhabitant (is-a-choice, is-an-experience, is-consciousness, is-God, is-the-compass) changes no downstream theorem; the framework is provably silent about what fills the shape it draws, and the silence is the theorem.**

*Series 12 is standalone; the verdict type `Series12Verdict` (WS7, README §3) is consumed here. WS5 CONSUMES the WS1–WS4 payoffs (`ws1_shape_coincidence`, `ws2_many_witness`, `ws3_compass_exogenous`, `ws4_underdetermined`) and computes the verdict as a function of a mechanized `Audit` certificate whose every field is one of those theorems; it does not re-prove them. The genuinely new Lean is `ws5_verdict` and `ws5_name_neutral`. Names live in prose (§8); the core quantifies. WS5 depends on WS4 settling (the verdict cannot be computed until the model pair is in hand) and carries the generalized neutrality as a STANDING consequence under whatever WS1–WS4 yield.*

## The object at stake

The charter's WS5 (§2): the verdict is COMPUTED from WS1–WS4, SHAPE-DRAWN the expected verdict, CONVERGENCE-DECIDED reported in its direction, PARTIAL if any side lands per-instance, never hand-set. AND the neutrality, generalized: adjoining any NAME for the inhabitant changes no downstream theorem; the framework is provably silent about what fills the shape it draws, and the silence is the theorem. Names live in prose (§8); the core quantifies.

Two obligations. (1) **The verdict as a function:** transcribe the program's `Audit`/`verdict` pattern (Series 07–11), with the `Audit` fields the WS1–WS4 theorems, so the verdict is a FUNCTION of the audit and cannot be hand-set. (2) **The generalized neutrality:** prove that adjoining any name, a map `name : Or → Name` into an arbitrary `Name` type, changes no downstream theorem, because the payoffs never mention `name`. This is parametricity: the payoffs factor through `Or`/the carrier and ignore any `Name`-tagging, so name-interchange is a THEOREM, not asserted prose.

**Ambient theory.** `spec/README.md` §3 (`Series12Verdict`), §2.11 (the neutrality shape); the WS1–WS4 payoffs; the `Audit`/`verdict` pattern (README §6).

## Candidates

### C1, The verdict as a function of a mechanized audit (the lead)

```lean
/-- **The audit certificate.** Every field is a WS1–WS4 theorem, so the verdict is a FUNCTION of the audit,
    falsifiable, never hand-set. -/
structure Audit (κ : Cardinal.{u}) where     -- Type-level (carries the data-level fork, Finding 4)
  coincidence_shape_honest : …           -- WS1: ws1_shape_coincidence ∧ ws1_coincidence_not_identity
  opening_inhabited        : Many (destWL …)                          -- WS2: ws2_many_witness (non-degenerate)
  reification_loadbearing  : …           -- WS2: ws2_reification_loadbearing (not a point-tag)
  compass_parametric       : …           -- WS3: ws3_compass_exogenous (∃, never a selection)
  fork                     : ConvergenceFork (destW …) (reifyW …) aW bW  -- WS4: WHICH disjunct (Finding 4)

/-- **The verdict BRANCHES on the certified fork (Finding 4), not a returned constant.** `verdictOfFork`
    cases on the audit's fork: `underdet ↦ shapeDrawn`, `forcedHolds`/`forcedFails ↦ convergenceDecided`. The
    fork is inspected, so had WS4 decided convergence the verdict would say so. -/
def verdict (cert : Audit κ) : Series12Verdict := verdictOfFork cert.fork
def ws5_verdict : Series12Verdict := verdict ws7_audit
/-- `ws5_verdict = shapeDrawn` is now a THEOREM, following from the audit's fork being `underdet` (discharged
    by the model pair `ws4_underdetermined`), NOT a definitional constant (Finding 4). -/
theorem ws5_verdict_eq : ws5_verdict (κ := κ) = Series12Verdict.shapeDrawn := by
  show verdictOfFork (ws7_audit (κ := κ)).fork = .shapeDrawn
  rfl   -- ws7_audit.fork := .underdet (ws4_underdetermined …), and verdictOfFork (.underdet _) = .shapeDrawn
```
The verdict branches: `verdict` cases on the audit's `fork` field via `verdictOfFork` (README §3). Because the fork carries WHICH disjunct of the trichotomy WS4 discharged, `verdict` reads the certificate rather than returning a constant, and `ws5_verdict_eq` holds BECAUSE the fork is `underdet` (the model pair), as a theorem. Had WS4 landed convergence-decided, `ws7_audit.fork` would be `forcedHolds`/`forcedFails` and `verdict` would compute `convergenceDecided` (Finding 4, the fork is now expressible).

- **Ambient:** the WS1–WS4 payoffs; `ConvergenceFork`/`verdictOfFork` (README §3); the `Audit` pattern (README §6).
- **Success condition (Shape-drawn):** `verdict` cases on the fork; `ws5_verdict = shapeDrawn` is a theorem via the `underdet` fork, and `convergenceDecided` is expressible via the other constructors.
- **Failure mode:** *the verdict a returned constant ignoring its certificate (Finding 4).* Foreclosed: `verdict := verdictOfFork cert.fork` inspects the fork; the pre-registered alternatives are reachable. **Winner (the computed verdict, branching).**

**Paper triage.** Decidable: `verdictOfFork (.underdet _) = .shapeDrawn` by `rfl`; `verdictOfFork (.forcedHolds _)`/`(.forcedFails _) = .convergenceDecided`; the audit supplies the fork from WS4. **Winner.**

### C2, The verdict is never the others (the falsifiability certificate)

```lean
/-- **The concrete verdict is `shapeDrawn`, and never the alternatives, BECAUSE its fork is `underdet`.**
    Stated of `ws5_verdict` (whose fork WS4 discharged at `underdet`), NOT of an arbitrary audit: a
    `forcedHolds`/`forcedFails` fork would legitimately give `convergenceDecided`, so the falsifiability is
    that THIS audit's fork forces `shapeDrawn`, tied to the model pair. -/
theorem ws5_verdict_not_decided : ws5_verdict (κ := κ) ≠ .convergenceDecided := by
  rw [ws5_verdict_eq]; exact fun h => Series12Verdict.noConfusion h
theorem ws5_verdict_not_partial : ws5_verdict (κ := κ) ≠ .Partial := by
  rw [ws5_verdict_eq]; exact fun h => Series12Verdict.noConfusion h
theorem ws5_verdict_not_circular : ws5_verdict (κ := κ) ≠ .Circular := by
  rw [ws5_verdict_eq]; exact fun h => Series12Verdict.noConfusion h
```
The falsifiability certificate (transcribing the program's pattern, Finding 4-aware): the CONCRETE verdict, whose fork WS4 discharged at `underdet`, is `shapeDrawn` and provably NOT `convergenceDecided`, `Partial`, `Refuted`, or `Circular`. This is falsifiable because it routes through `ws5_verdict_eq` (the fork is `underdet`, the model pair): had WS4 landed convergence-decided, the fork would be `forcedHolds`/`forcedFails`, `ws5_verdict_eq` would not hold, and the verdict would be `convergenceDecided` instead, honestly.

- **Ambient:** `Series12Verdict.noConfusion`, `ws5_verdict_eq`, the `underdet` fork.
- **Success condition (Shape-drawn):** the concrete verdict is `shapeDrawn` and never the others, via its `underdet` fork.
- **Failure mode:** *the falsifiability made vacuous by ignoring the fork.* Foreclosed: it routes through `ws5_verdict_eq`, which depends on the fork being `underdet` (the model pair); a decided fork would flip it. **Winner (falsifiability).**

### C3, The generalized neutrality (the silence as a theorem; the payoff)

```lean
/-- **GENERALIZED NEUTRALITY.** Adjoining ANY name for the inhabitant, a map `name : Or → Name` into an
    arbitrary `Name : Type u`, changes no downstream theorem: the payoffs (`Many`, the model pair) never
    mention `name`, so they hold identically for every naming. The silence is the theorem. -/
theorem ws5_name_neutral {Name : Type u} (name : ULift.{u} Bool → Name) (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨ws2_many_witness hinf, ws4_underdetermined_pair hinf⟩                  -- `name` discarded: the payoffs are name-free
```
The neutrality: for ANY `Name` and any naming `name : Or → Name`, the WS2 plurality and the WS4 underdetermination still hold, by the SAME terms, `name` discarded. The payoffs factor through the carrier and ignore any tagging, so name-interchange is a theorem (parametricity). Whether the inhabitant is called a choice, an experience, consciousness, God, or the compass changes nothing downstream.

- **Ambient:** `ws2_many_witness` (WS2), `ws4_underdetermined` (WS4); `Name` an arbitrary `Type u`.
- **Success condition (Shape-drawn):** the payoffs hold for every naming, the proof literally the WS2/WS4 terms with `name` ignored.
- **Failure mode:** *neutrality asserted, not proved (name a term).* Foreclosed: `ws5_name_neutral` takes `name` as an unused hypothesis and returns the name-free payoffs, the silence is a theorem, and `name` is never a proof term doing discharge work. **Winner (the neutrality).**

**Paper triage.** Decidable: `name` appears only as an unused binder; the conclusion is the WS2/WS4 payoffs verbatim. **Winner.**

### C4, Neutrality across ALL five names at once (the generalization made concrete)

```lean
/-- **Neutrality across the named readings.** Instantiating `Name` and `name` with is-a-choice /
    is-an-experience / is-consciousness / is-God / is-the-compass changes no payoff: the SAME term discharges
    all five, because none is a term. -/
theorem ws5_name_neutral_all (hinf : ℵ₀ ≤ κ) :
    ∀ {Name : Type u} (name : ULift.{u} Bool → Name),
      Many (destWL hinf) ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) :=
  fun {Name} name => ws5_name_neutral name hinf
```
The generalization made concrete: the neutrality quantifies over ALL `Name` and `name`, so every one of the five named readings the charter lists (§8) is covered by ONE theorem, the framework's provable silence about what fills the shape.

- **Ambient:** `ws5_name_neutral` (C3).
- **Success condition (Shape-drawn):** one theorem, universally quantified over names, covers all five readings.
- **Failure mode:** *a specific name privileged.* Foreclosed: the quantifier is over all `Name`/`name`; no reading is a term. **Winner (the generalization).**

### C5, A named verdict (the sin: a name doing verdict work, rejected)

```lean
def consciousnessVerdict : Series12Verdict := if isConscious then .shapeDrawn else .Partial   -- a name deciding
```
Let a name (is-conscious, is-God) decide the verdict.

- **Failure mode:** *a name doing a proof's work, SERIOUS (discipline 5).* This breaches the wall from the prose side: a name discharging the verdict. **Reject.** The verdict is a function of the `Audit` (C1), whose fields are the WS1–WS4 theorems; no name enters. The neutrality (C3/C4) proves names change nothing, the opposite of letting one decide.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict BRANCHES on the certified fork | `ConvergenceFork`/`verdictOfFork`, WS4 fork | yes, cases on the fork, `underdet ↦ shapeDrawn` | **win (computed verdict)** |
| C2 | concrete verdict never the alternatives | `noConfusion`, `ws5_verdict_eq` (fork `underdet`) | yes, via the fork | **win (falsifiability)** |
| C3 | generalized neutrality (silence) | `ws2_many_witness`, `ws4_underdetermined` | yes, `name` an unused binder | **win (neutrality)** |
| C4 | neutrality across all five names | C3 | yes, universal over `Name` | **win (generalization)** |
| C5 | a name deciding the verdict |, | yes, a name a term | **reject (SERIOUS)** |

## Winning candidates: C1 (computed verdict) + C2 (falsifiability) + C3 (neutrality) + C4 (generalization)

### Definitions and obligations (cite `spec/README.md` §3, §2.11; consume WS1–WS4)

```lean
namespace Series12.WS5
-- Series12Verdict, ConvergenceFork, verdictOfFork (WS7, README §3), the Audit pattern (README §6), consumed.
-- ws1_shape_coincidence, ws2_many_witness, ws3_compass_exogenous, ws4_underdetermined, consumed (WS1–WS4).

-- D1 Audit (fork field) + verdict + ws5_verdict + ws5_verdict_eq (C1) ; D2 ws5_verdict_not_* (C2) ;
-- D3 ws5_name_neutral (C3) ; D4 ws5_name_neutral_all (C4).
```

**Proof architecture.** D1 assembles the `Audit` (fields = the WS1–WS3 theorems plus the WS4 `fork`) and computes `verdict cert = verdictOfFork cert.fork`, which cases on the certified disjunct (Finding 4); with the fork discharged at `underdet` (the model pair), `ws5_verdict_eq : ws5_verdict = shapeDrawn` is a THEOREM, not a definitional constant. D2 certifies falsifiability of the concrete verdict via its `underdet` fork (a decided fork would flip it). D3 proves the generalized neutrality: for any `Name`/`name`, the WS2/WS4 payoffs hold by the same terms, `name` discarded, the silence a theorem. D4 generalizes over all five named readings. **Dependencies:** WS1–WS4 (the audit fields, so WS5 cannot compute until WS4 settles and supplies the fork); `Series12Verdict`/`ConvergenceFork`/`verdictOfFork` (WS7). **The verdict branches on the audit's fork and the neutrality is parametricity, neither hand-set nor asserted.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (`ws5_verdict = shapeDrawn`, computed by casing on the `underdet` fork, a theorem), D2 (falsifiability), D3/D4 (the generalized neutrality). The verdict computed from a discharged audit, the framework provably silent about what fills the shape.
- **Convergence-decided (pre-registered, first-class, Finding 4):** if WS4 reports `convergenceDecided` (the structure forces convergence or its negation), the `Audit`'s `fork` field is `forcedHolds`/`forcedFails` and `verdictOfFork` computes `convergenceDecided`. The verdict follows the audit's fork into whichever branch WS4 lands, never overriding it. This is why the verdict BRANCHES: it tracks WS4's honest verdict, and the fork makes the alternative EXPRESSIBLE (the returned-constant defect is gone).
- **Partial (pre-registered):** if WS2's inhabitation degenerates to a point-tag or WS4's pair proves vacuous, the corresponding audit field fails (no certificate, or a fork that is neither the three), and the verdict is reported `Partial`.
- **Strip test.** Delete **"name / consciousness / God / choice / compass"** from `ws5_name_neutral` and it is the bare fact **"for any type `Name` and any function `Or → Name`, `Many (destWL)` and the model pair hold"**, the payoffs are `name`-free, so the theorem is `Many` and the underdetermination with an unused hypothesis. The neutrality SURVIVES the strip as exactly "the payoffs do not depend on any adjoined tagging", which is the silence the charter demands as a theorem; and no name is a term (the names appear only as the type/function being quantified away, never discharging anything).

## Deliverable

`series-12/formal/Series12/ws5.lean`: `Series12Verdict`/`ConvergenceFork`/`verdictOfFork` (WS7) and the WS1–WS4 payoffs consumed; the `Audit` (with the `fork` field) + `verdict` (branching on the fork) + `ws5_verdict` + `ws5_verdict_eq` as a theorem (D1), `ws5_verdict_not_*` (D2), `ws5_name_neutral` (D3), `ws5_name_neutral_all` (D4). **Consumes WS1–WS4; cannot compute until WS4 settles and supplies the fork; carries the neutrality as a standing consequence.** Axiom check: `#print axioms ws5_verdict` and `#print axioms ws5_name_neutral` reduce through the WS1–WS4 payoffs to the standard three. **The verdict BRANCHES on the certified fork (never a returned constant, Finding 4) and the generalized neutrality is a THEOREM (adjoining any name changes no downstream theorem): the framework provably silent about what fills the shape it draws, the silence itself the theorem.**
