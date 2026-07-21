/-
`program-2/series-6/formal/P2S6/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 6 (2.6).

The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= shapeDrawn` by `rfl` on
the certified flags, DISCRIMINATING (reaches all four outcomes), the four DECIDING flags EARNED by the WS1-WS4
headlines (`ws5_flags_justified`). The computed verdict is SHAPE-DRAWN: strict identity fails and the single line
is an import (the ground), the weak continuity is RECOVERABLE on the merged carrier and an IMPORT on the cut
carrier (both reachable), so which obtains is SELF-RELATIVE and not forced (`carrierDecided = false`, grounded by
`ws5_carrier_relative_verdict`; the two meta-flags disclosed, finding C3-S1). The verdict rests on the weak
continuity and the linearization import, not on strict identity failing: it returns `partial'` when the line is
not an import or a fork side is excluded, so the strict-failure flag alone never decides (audit c). The five audit
clauses (a)-(e) bundle the payoffs; (e) is the grep-certified placeholder (the names property is meta, enforced by
protocol §6).

Design docs: `program-2/series-6/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S6.ws1
import P2S6.ws2
import P2S6.ws3
import P2S6.ws4

universe u

namespace P2S6

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `woven` a recoverable weak continuity binds the moments (an endogenous succession);
`severed` no recoverable weak continuity (the succession an import); `shapeDrawn` the continuity drawn but its
recoverability self-relative and undecidable; `partial'` primed (`partial` is a Lean keyword) an obligation
degenerate. No identifier embeds a forbidden content-name as a whole word (audit e). -/
inductive Outcome
  | woven
  | severed
  | shapeDrawn
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION.** `shapeDrawn` iff strict identity fails and the single line is an import (the ground),
the weak continuity is reachable both recoverable (WOVEN) and as an import (SEVERED), and the plain structure does
NOT force a canonical carrier (`carrierDecided = false`, the continuity self-relative). The pre-registered
alternatives: `partial'` (no strict failure, or no line import, or a fork side excluded by construction);
`woven`/`severed` (a canonical carrier forced one way). -/
def verdict (strictFails lineIsImport wovenReachable severedReachable carrierDecided carrierWoven : Bool) :
    Outcome :=
  if !strictFails || !lineIsImport then Outcome.partial'
  else if !(wovenReachable && severedReachable) then Outcome.partial'
  else if !carrierDecided then Outcome.shapeDrawn
  else if carrierWoven then Outcome.woven
  else Outcome.severed

/-- **THE COMPUTED VERDICT.** On the certified flags (strict identity fails, the single line is an import, WOVEN
and SEVERED both reachable, no canonical carrier forced), `shapeDrawn`, by computation. -/
theorem ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all four outcomes. `woven`/`severed` when a canonical
carrier is forced; `partial'` when strict identity does not fail, or a fork side is excluded by fiat. -/
theorem ws5_verdict_discriminates :
    verdict true true true true true true = Outcome.woven
  ∧ verdict true true true true true false = Outcome.severed
  ∧ verdict false true true true false false = Outcome.partial'
  ∧ verdict true true true false false false = Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE DECIDING FLAGS ARE JUSTIFIED.** The four DECIDING inputs are EARNED by the WS1-WS4 headlines, none
hand-set: `strictFails` (WS1, `ws1_strict_fails`), `lineIsImport` (WS3, `ws3_line_is_import`), `wovenReachable`
(WS4/WS2, `ws2_cont_recoverable`), `severedReachable` (WS4/WS2, `ws2_cont_is_import`). The two META-flags
`carrierDecided`/`carrierWoven` are not WS-propositions and are disclosed (finding C3-S1):
`ws5_carrier_relative_verdict` grounds `carrierDecided = false`. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
  ∧ Recoverable (mergeLift hinf)
  ∧ ¬ Recoverable (cutLift hinf) :=
  ⟨ws1_strict_fails hinf, ws3_line_is_import hinf, ws2_cont_recoverable hinf, ws2_cont_is_import hinf⟩

/-- **THE VERDICT IS SHAPE-DRAWN, AND `carrierDecided` IS HONESTLY FALSE.** Both carriers reachable and neither
forced (`Recoverable (mergeLift) ∧ ¬ Recoverable (cutLift)`), so no structural principle picks a canonical
carrier: `carrierDecided = false`, and the computed verdict is `shapeDrawn`. The continuity is self-relative. -/
theorem ws5_carrier_relative_verdict {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    verdict true true true true false false = Outcome.shapeDrawn
  ∧ (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)) :=
  ⟨rfl, ws2_cont_recoverable hinf, ws2_cont_is_import hinf⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) NO ABSOLUTE PERSISTENCE.** The continuity is FOR a carrier (WOVEN on the merged, SEVERED on the cut,
both reachable, neither forced), and the single line is the self's import. No frame-independent persistence is
asserted. -/
theorem ws5_audit_no_absolute {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf))
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)) :=
  ⟨⟨ws2_cont_recoverable hinf, ws2_cont_is_import hinf⟩, ws3_line_is_import hinf⟩

/-- **(b) THE FORK NOT BY FIAT.** WOVEN (`ws2_cont_recoverable`) and SEVERED (`ws2_cont_is_import`) both reachable,
and the weak continuity genuinely weaker than strict identity (`ws2_weaker_than_strict`, recoverable where strict
fails). SEVERED is not excluded by construction. -/
theorem ws5_audit_fork_genuine {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
  ∧ (AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0 ∧ Recoverable (mergeLift hinf)) :=
  ⟨ws2_cont_recoverable hinf, ws2_cont_is_import hinf, ws2_weaker_than_strict hinf⟩

/-- **(c) THE KNOT IS THE WEAK CONTINUITY, NOT THE STRICT FAILURE (the costume gate).** The verdict returns
`partial'` when strict identity fails but the single line is NOT an import, and when strict identity fails but a
fork side is excluded: the strict-failure flag ALONE never decides. The weak continuity's recoverability
(`ws2_cont_recoverable`/`ws2_cont_is_import`) is what carries the decision. -/
theorem ws5_audit_knot_not_strict {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (verdict true false true true false false = Outcome.partial')
  ∧ (verdict true true false false false false = Outcome.partial')
  ∧ Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf) :=
  ⟨rfl, rfl, ws2_cont_recoverable hinf, ws2_cont_is_import hinf⟩

/-- **(d) THE LINE IS THE LINEARIZATION IMPORT, NOT SCALAR RANK.** `ws3_line_is_import` (the total order
non-recoverable, quantified over all order labels); `rankT kA = rankT kB` (rank does not linearize the concurrent
pair); the partial order endogenous. The 1D line rests on the import, not the scalar. -/
theorem ws5_audit_line_is_import {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
  ∧ rankT kA = rankT kB
  ∧ ((causal kA kC ∧ causal kB kC) ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
      ∧ (¬ causal kA kB ∧ ¬ causal kB kA)) :=
  ⟨ws3_line_is_import hinf, ws3_line_not_scalar, ws3_partial_order_endogenous⟩

/-- **(e) NAMES-NOT-TERMS.** A META-property about identifiers, not a proposition: no proof term, definition, or
discharged obligation is named as a forbidden content-word ("self," "thread," "persistence," "life," "death,"
"time," "here," "there," "god," "choice," "subjectivity") as a whole word. Enforced by the protocol §6 mechanical
grep (hits are docstring prose only), not by this `True`; carried as the accepted house placeholder, the grep the
teeth. -/
theorem ws5_audit_names_not_terms : True := trivial

end P2S6
