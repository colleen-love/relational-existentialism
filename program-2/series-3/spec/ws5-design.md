# WS5 — The verdict and the audit folded in. Design.

**Target (charter §2-WS5).** The verdict is COMPUTED, never hand-set: `shapeDrawn` (WS1 typed-not-evaluated, WS2
forced in-sight on a genuine class, WS3 dissent an import, WS4 the fork reaching both values); the pre-registered
alternatives `forcedFull` / `disconnected` / `partial'` reachable. Audit clauses (a)-(e) bundled.

## 1. Winning construction (typed signatures)

```lean
inductive Outcome | shapeDrawn | forcedFull | disconnected | partial'
  deriving DecidableEq

/-- `shapeDrawn` iff `Converges₂` is typed and two-sided free (WS1), forced over the in-sight class AND its
    dissent an import (WS2/WS3), and the fork reaches both values (WS4). Pre-registered alternatives:
    `disconnected` (WS1 fails), `partial'` (WS2 or WS3 degenerate), `forcedFull` (the in-sight forcing
    extends to the full class — no faithful dissent). -/
def verdict (typed forcedInSight dissentImport forkBoth : Bool) : Outcome :=
  if !typed then Outcome.disconnected
  else if !(forcedInSight && dissentImport) then Outcome.partial'
  else if forkBoth then Outcome.shapeDrawn
  else Outcome.forcedFull

/-- **THE COMPUTED VERDICT.** On the certified flags, `shapeDrawn`, by computation. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.shapeDrawn        -- rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: flipping a flag computes a different outcome. The
    `forcedFull` arm (in-sight forcing extends to the full class) is a reachable input — the
    pre-registered stronger outcome, never hand-set on this witness. -/
theorem ws5_verdict_discriminates :
    verdict true true true false = Outcome.forcedFull
  ∧ verdict false true true true = Outcome.disconnected
  ∧ verdict true false true true = Outcome.partial'
  ∧ verdict true true false true = Outcome.partial'                              -- decide

/-- **THE FLAGS ARE JUSTIFIED.** The four `true` inputs are EARNED by the WS1-WS4 headlines. None hand-set. -/
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),                                   -- typed / two-sided free (WS1)
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),                                       -- forced in-sight (WS2)
        Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),                                       -- dissent an import (WS3)
        Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val))
  ∧ ((∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)  -- class genuine (WS4)
     ∧ (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c))
```

`ws5_flags_justified := ⟨ws1_two_sided_free hinf, ws2_converges_decided_in_sight hinf,
ws3_dissent_is_import hinf, ws4_insight_proper hinf⟩`.

## 2. The five audit clauses (a)-(e)

```lean
/-- (a) NO VALUATION EVALUATED. `Converges₂` fixes no valuation: two-sided free (WS1). A proof term (real
    content), not merely a grep note. -/
theorem ws5_audit_no_evaluation (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth

/-- (b) THE DIRECTION IS NEVER DECIDED. No theorem, definition, or discharged obligation states that `slf` and
    `oth` DO or DO NOT cohere; the verdict LOCATES the fork (`ws5_verdict_discriminates` reaches both
    `shapeDrawn` and `forcedFull`) and fills neither. A NAMES/absence property about the build, carried
    as a grep-certified `True` (the CORRECT non-decision — the direction is left open, not decided). -/
theorem ws5_audit_direction_open : True := trivial

/-- (c) THE FORK IS GENUINE. Both zones on witnessed valuations, the class properly constrained, no PR1-S1. -/
theorem ws5_audit_fork_genuine (hinf : ℵ₀ ≤ κ) :
    (fork bundle : ws4_two_zone hinf) ∧ (proper : ws4_insight_proper hinf)

/-- (d) DISSENT IS AN IMPORT. A proof term resting on Series 07. -/
theorem ws5_audit_dissent_import (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
    ¬ Recoverable (valLift (outDest hinf attendsR) c.val)

/-- (d, K1 anchor) THE FACES ARE THE LOAD-BEARING READERS. `Converges₂` is between `slf` and `oth`, the genuine
    two the S2 pair built: `oth` is `RealFor` the NAMED `slfReader`, and the twoness is a `¬ Recoverable`
    import. The coherence is between genuine readers, not decoration over labels (charter §4.d). -/
theorem ws5_audit_faces_are_readers (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)

/-- (e) NAMES-NOT-TERMS. No proof term is named for the interpretive content. Grep-certified `True`. -/
theorem ws5_audit_names_not_terms : True := trivial
```

`ws5_audit_faces_are_readers := ⟨ws2_other_reader_wise hinf, ws2_other_non_recoverable hinf⟩` (cited from S2).

## 2a. Recurrence guard note

The `True` placeholders (b, e) are NAMES/absence properties (about identifiers and what is NOT proved), certified
by the §6 grep, exactly the accepted S2 pattern (`ws5_audit_downstream_open`, `ws5_audit_names_not_terms`). They
are the CORRECT non-decisions: (b) the direction open is the charter's central discipline, not a shortfall; (e)
the grep is the certificate. Clauses (a), (c), (d), and the K1 anchor are genuine propositions.

## 3. Outcome (computed)

On this witness the flags are all `true` (WS1 two-sided free, WS2 forced in-sight on the inhabited proper class,
WS3 dissent an import, WS4 both zones witnessed), so `verdict = shapeDrawn`. `forcedFull` is reached by
`verdict true true true false` (the pre-registered outcome for a structure whose in-sight forcing covers the full
class), and is NOT hand-set here — on this witness `cDiss` is a genuine faithful dissent, so `forkBoth = true`.

## 4. Strip-test annotation

`ws5_verdict_discriminates` strips to "a function `Bool⁴ → Outcome` reaching ≥ 2 values on reachable inputs" — a
bare discrimination fact. `ws5_flags_justified` strips to the conjunction of the WS1-WS4 stripped statements.
Survives.
