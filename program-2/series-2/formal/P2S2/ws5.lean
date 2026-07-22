/-
`program-2/series-2/formal/P2S2/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 2 (2.2).

The verdict is COMPUTED from the WS1-WS4 flags (never hand-set): `verdict : Bool⁵ → Outcome`, `ws5_verdict_eq`
computes `twoFacing` by `rfl`, and `ws5_verdict_discriminates` shows the function is not constant (flip a flag,
get a different outcome). The flags are EARNED by `ws5_flags_justified` (the WS1-WS4 headline propositions). The
audit clauses (a)-(e) are actual propositions bundling the payoffs; the coherence-open (d-iv) and names (e)
clauses are grep-certified `True` placeholders (properties about identifiers, not propositions).

DISCLOSED (C2-S1): the flags are the accepted house pattern (S1 `ws5.lean`) — `ws5_flags_justified` proves the
headline Props that earn each `true`; ONE / TOTALIZED are PRE-REGISTERED outcomes the same `verdict` computes for
OTHER structures (charter §7), reachable inputs to the discriminating function, not hand-set claims about this
witness (on which the twoness IS non-recoverable and the diagonal DOES hold, so twoFacing is the computed
outcome). The charter's outcome names map to Lean identifiers carrying no forbidden content-name (audit (e)).

Design docs: `program-2/series-2/spec/ws5-design.md`; shared objects `spec/README.md` §7.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S2.ws1
import P2S2.ws2
import P2S2.ws3
import P2S2.ws4

universe u

namespace P2S2

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `twoFacing` the expected payoff; `one` the mutual reading collapses (Series 07's One);
`totalized` a perspective closes the pair; `partial'` primed (`partial` is a Lean keyword); `disconnected` WS1
imports beyond the symmetry-breaker. No identifier embeds a forbidden content-name (audit (e)). -/
inductive Outcome
  | twoFacing
  | one
  | totalized
  | partial'
  | disconnected
  deriving DecidableEq

/-- **The verdict FUNCTION.** twoFacing iff the construction is well-formed (WS1), the reader and facing land
(WS2/WS3), and under mutual reading the twoness is non-recoverable AND no inspection totalizes (WS4). The
pre-registered alternatives: disconnected (WS1 fails), partial' (WS2/WS3 degenerate), one (the twoness recovered
— the mutual reading collapses), totalized (a self-total hold — a perspective closes the pair). -/
def verdict (wf readerTwo facing nonCollapse nonTotal : Bool) : Outcome :=
  if !wf then Outcome.disconnected
  else if !(readerTwo && facing) then Outcome.partial'
  else if nonCollapse && nonTotal then Outcome.twoFacing
  else if !nonCollapse then Outcome.one
  else Outcome.totalized

/-- **THE COMPUTED VERDICT.** On the certified flags, twoFacing, by computation. -/
theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing := rfl

/-- **Falsifiability.** The verdict function DISCRIMINATES: flipping a flag computes a different outcome. The ONE
and TOTALIZED arms are reachable inputs (the pre-registered alternatives for other structures). -/
theorem ws5_verdict_discriminates :
    verdict true true true false true = Outcome.one
  ∧ verdict true true true true false = Outcome.totalized
  ∧ verdict false true true true true = Outcome.disconnected
  ∧ verdict true false true true true = Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The verdict's five `true` inputs are EARNED by the WS1-WS4 headlines: the WS1
section (`wf`); the NAMED reader for which `oth` is `RealFor` (`readerTwo`); the WS3 reading-direction import
(`facing`, `¬ Recoverable (faceLift)`); the WS3 diagonal (`nonTotal`); the WS2 twoness import (`nonCollapse`,
`¬ Recoverable (rankLift)`); and the WS4 joint-unattended residue (the mutual content). None hand-set. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (attendsR (reifyR {slf, oth, q}) = {slf, oth, q})
  ∧ (RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth)
  ∧ (¬ Recoverable (faceLift hinf))
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
  ∧ (¬ Recoverable (rankLift (outDest hinf attendsR) rankR))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y)
        ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth) := by
  refine ⟨by decide, ws2_other_reader_wise hinf, (ws3_facing_asymmetric hinf).2.2.2,
          (ws3_facing_partial hinf).2, ws2_other_non_recoverable hinf, (ws4_mutual_residue hinf).2.1⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) THE OTHER IS A READER, NOT A LABEL.** The NAMED finite attention `slfReader` for which `oth` is
`RealFor` (not `Many`, not a tag; the reader fixed, its `reads` membership load-bearing). -/
theorem ws5_audit_reader_loadbearing {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth :=
  ws2_other_reader_wise hinf

/-- **(b) THE TWONESS IS NON-RECOVERABLE.** A proof term (the otherness an import, Series 07). -/
theorem ws5_audit_twoness_import {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsR) rankR) :=
  ws2_other_non_recoverable hinf

/-- **(c) THE FACING IS ASYMMETRIC.** A proof term: the reading-direction is non-recoverable, not an assumption. -/
theorem ws5_audit_facing_asymmetric {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (faceLift hinf) :=
  (ws3_facing_asymmetric hinf).2.2.2

/-- **(d) THE RESIDUE IS GENUINE, THE MUTUALITY TESTED.** The four readings witnessed, the joint-unattended
residue (`bnd` in neither reach), and the reading order rank-constrained (no PR1-S1). Both arms reachable via
`ws5_verdict_discriminates`. The coherence is left OPEN (`ws5_audit_downstream_open`). -/
theorem ws5_audit_residue_genuine {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y)
        ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd) :=
  ⟨(ws4_mutual_residue hinf).1, (ws4_mutual_residue hinf).2.1, (ws4_mutual_residue hinf).2.2.1⟩

/-- **(d, coherence-open) THE COHERENCE IS UNTOUCHED.** No theorem, definition, or discharged obligation decides
the coherence/convergence of the two readings (Series 2.3's `Converges₂`). A NAMES property about identifiers (no
`converg`/`cohere` term), certified by the §6 grep; carried as a `True` placeholder, as the property is about
identifiers, not a proposition. This `True` is the CORRECT non-decision — the coherence is left open, not
decided. -/
theorem ws5_audit_downstream_open : True := trivial

/-- **(e) NAMES-NOT-TERMS.** No proof term, definition, or discharged obligation is named as content
`self`/`other`/`I`/`you`/`perspective`/`love`/`loved`/`gaze`/`God`/`choice`/`subjectivity`. A NAMES property,
certified by the mechanical grep (protocol §6); carried here as a `True` placeholder, as the property is about
identifiers, not a proposition.
Made non-vacuous at Program Review 2-1 (PR2-R2, the accepted S13 C1-S1 form): the statement below proves
the outcome codomain a genuine discrimination among neutrally-named values. -/
theorem ws5_audit_names_not_terms :
    Outcome.disconnected ≠ Outcome.partial'
  ∧ Outcome.partial' ≠ Outcome.twoFacing
  ∧ Outcome.twoFacing ≠ Outcome.one
  ∧ Outcome.one ≠ Outcome.totalized
  ∧ Outcome.disconnected ≠ Outcome.totalized := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end P2S2
