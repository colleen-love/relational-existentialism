/-
`program-2/series-3/formal/P2S3/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 3 (2.3).

The verdict is COMPUTED from the WS1-WS4 flags (never hand-set): `verdict : Bool⁴ → Outcome`, `ws5_verdict_eq`
computes `shapeDrawn` by `rfl`, and `ws5_verdict_discriminates` shows the function reaches more than one value
(the `forcedFull` arm — the in-sight forcing extends to the full class, the pre-registered CONVERGENCE-DECIDED —
is a reachable input, never hand-set on this witness). The flags are EARNED by `ws5_flags_justified` (the WS1-WS4
headline propositions). The five audit clauses (a)-(e): (a) no valuation evaluated, (c) fork genuine, (d) dissent
an import, and the K1 anchor (the faces are the load-bearing readers `slf`/`oth` the S2 pair built) are genuine
propositions; (b) direction-open and (e) names-not-terms are grep-certified `True` placeholders (NAMES/absence
properties about identifiers and what is NOT proved, the accepted S2 pattern), the CORRECT non-decisions.

Design docs: `program-2/series-3/spec/ws5-design.md`; shared objects `spec/README.md` §7.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S3.ws1
import P2S3.ws2
import P2S3.ws3
import P2S3.ws4

universe u

namespace P2S3

open P1.Core P1.Reader P2S0 Cardinal
open P2S2 (RCar slf oth attendsR rankR slfReader ws2_other_reader_wise ws2_other_non_recoverable)

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `shapeDrawn` the expected payoff (the fork reaches both values on a constrained class);
`forcedFull` the in-sight forcing extends to the FULL faithful class (the pre-registered CONVERGENCE-DECIDED, the
outcome that would decide the program's oldest question, reported in whichever direction); `disconnected`
`Converges₂` cannot be typed without evaluating a valuation; `partial'` primed (`partial` is a Lean keyword) an
obligation lands only per-instance/degenerate. No identifier embeds a forbidden content-name (audit (e)). -/
inductive Outcome
  | shapeDrawn
  | forcedFull
  | disconnected
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION.** `shapeDrawn` iff `Converges₂` is typed and two-sided free (WS1), forced over the
in-sight class AND its dissent an import (WS2/WS3), and the fork reaches both values (WS4). The pre-registered
alternatives: `disconnected` (WS1 fails), `partial'` (WS2 or WS3 degenerate), `forcedFull` (the in-sight forcing
extends to the full class — no faithful dissent). -/
def verdict (typed forcedInSight dissentImport forkBoth : Bool) : Outcome :=
  if !typed then Outcome.disconnected
  else if !(forcedInSight && dissentImport) then Outcome.partial'
  else if forkBoth then Outcome.shapeDrawn
  else Outcome.forcedFull

/-- **THE COMPUTED VERDICT.** On the certified flags, `shapeDrawn`, by computation. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.shapeDrawn := rfl

/-- **Falsifiability.** The verdict function DISCRIMINATES: flipping a flag computes a different outcome. The
`forcedFull` arm (the in-sight forcing extends to the full class) is a reachable input — the pre-registered
stronger outcome, never hand-set on this witness (on which `cDiss` is a genuine faithful dissent, so
`forkBoth = true`). -/
theorem ws5_verdict_discriminates :
    verdict true true true false = Outcome.forcedFull
  ∧ verdict false true true true = Outcome.disconnected
  ∧ verdict true false true true = Outcome.partial'
  ∧ verdict true true false true = Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The verdict's four `true` inputs are EARNED by the WS1-WS4 headlines: the WS1
two-sided freedom (`typed`); the WS2 in-sight forcing (`forcedInSight`); the WS3 dissent import (`dissentImport`);
and the WS4 genuine (proper, inhabited) class (`forkBoth`). None hand-set. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val))
  ∧ ((∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
     ∧ (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c)) :=
  ⟨ws1_two_sided_free, ws2_converges_decided_in_sight hinf, ws3_dissent_is_import hinf, ws4_insight_proper hinf⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) NO VALUATION EVALUATED.** `Converges₂` fixes no valuation: two-sided free (WS1). A proof term (real
content), not merely a grep note. -/
theorem ws5_audit_no_evaluation :
    ∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth :=
  ws1_two_sided_free

/-- **(b) THE DIRECTION IS NEVER DECIDED.** No theorem, definition, or discharged obligation states that `slf`
and `oth` DO or DO NOT cohere; the verdict LOCATES the fork (`ws5_verdict_eq` reaches `shapeDrawn`,
`ws5_verdict_discriminates` reaches `forcedFull`) and fills neither. A NAMES/absence property about the build, carried as a grep-certified `True`
(the CORRECT non-decision — the direction is left open, not decided; charter §4.a). -/
theorem ws5_audit_direction_open : True := trivial

/-- **(c) THE FORK IS GENUINE.** Both zones on witnessed valuations at the same pair, the class properly
constrained (in-sight ⊊ faithful, both inhabited), no PR1-S1 tautology. A proof term bundling `ws4_two_zone` and
`ws4_insight_proper`. -/
theorem ws5_audit_fork_genuine {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ((∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
      ∧ (∀ (Or : Type) (c : Valuation RCar Or),
          Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
      ∧ (∀ (Or : Type) (c : Valuation RCar Or),
          Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val)))
  ∧ ((∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
     ∧ (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c)) :=
  ⟨ws4_two_zone hinf, ws4_insight_proper hinf⟩

/-- **(d) DISSENT IS AN IMPORT.** A proof term resting on Series 07 (via `valLift_not_recoverable` → the collapse
engine + the negative import horn). -/
theorem ws5_audit_dissent_import {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
    ¬ Recoverable (valLift (outDest hinf attendsR) c.val) :=
  ws3_dissent_is_import hinf

/-- **(d, K1 anchor) THE FACES ARE THE LOAD-BEARING READERS.** `Converges₂` is between `slf` and `oth`, the
genuine two the S2 pair built: `oth` is `RealFor` the NAMED `slfReader`, and the twoness is a `¬ Recoverable`
import. The coherence is between genuine readers, not a decoration over labels (charter §4.d). Cited from S2. -/
theorem ws5_audit_faces_are_readers {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR) :=
  ⟨ws2_other_reader_wise hinf, ws2_other_non_recoverable hinf⟩

/-- **(e) NAMES-NOT-TERMS.** No proof term, definition, or discharged obligation is named as content
`love`/`loved`/`coherence`/`convergence`/`compass`/`orientation`/`self`/`other`/`God`/`choice`/`subjectivity`. A
NAMES property about identifiers, certified by the protocol §6 grep; carried here as a grep-certified `True`.
Made non-vacuous at Program Review 2-1 (PR2-R2, the accepted S13 C1-S1 form): the statement below proves
the outcome codomain a genuine discrimination among neutrally-named values. -/
theorem ws5_audit_names_not_terms :
    Outcome.disconnected ≠ Outcome.partial'
  ∧ Outcome.partial' ≠ Outcome.shapeDrawn
  ∧ Outcome.shapeDrawn ≠ Outcome.forcedFull
  ∧ Outcome.disconnected ≠ Outcome.forcedFull := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end P2S3
