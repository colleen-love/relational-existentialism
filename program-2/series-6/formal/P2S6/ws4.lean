/-
`program-2/series-6/formal/P2S6/ws4.lean`

WS4 - The continuity's fork (the knot). Program 2 Series 6 (2.6), the genuinely-uncertain obligation.

The fork on the weak continuity: WOVEN reachable (`ws4_woven_reachable`, a recoverable weak continuity on the
merged carrier) and SEVERED reachable (`ws4_severed_reachable`, an import on the cut carrier), both on genuine
carriers, so the continuity is SELF-RELATIVE (`ws4_carrier_relative`) - neither forced. A companion MORTALITY
fork, stated on the DIRECTIONAL knowing the continuity lifts encode (one structure with the lift, finding C2-S1):
`ws4_cessation_relative` - on the cut carrier nothing knows `c0` (a moment nothing holds, attention-relative
cessation) and the SAME asymmetric knowing is the import (`¬ Recoverable (cutLift)`); `ws4_conservative_reachable`
- on the merged carrier every moment is known (mutual, nothing ceases). No fiat (both reachable, the weak
continuity genuinely weaker than strict, WS2); no costume (the fork is the continuity's recoverability, not
strict identity failing); no absolute persistence (the continuity is FOR a carrier).

Design docs: `program-2/series-6/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S6.ws3

universe u

namespace P2S6

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **WOVEN REACHABLE.** A recoverable weak continuity exists (the merged carrier). -/
theorem ws4_woven_reachable (hinf : ℵ₀ ≤ κ) : Recoverable (mergeLift hinf) :=
  ws2_cont_recoverable hinf

/-- **SEVERED REACHABLE.** A non-recoverable weak continuity (an import) exists (the cut carrier). -/
theorem ws4_severed_reachable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (cutLift hinf) :=
  ws2_cont_is_import hinf

/-- **THE CONTINUITY IS SELF-RELATIVE (audit a).** WOVEN and SEVERED both reachable, neither forced by the plain
structure: whether the weak continuity is recoverable is FOR a carrier, self-relative. -/
theorem ws4_carrier_relative (hinf : ℵ₀ ≤ κ) :
    Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf) :=
  ⟨ws2_cont_recoverable hinf, ws2_cont_is_import hinf⟩

/-- **MORTALITY COMPANION - ATTENTION-RELATIVE CESSATION (MORTAL reachable).** On the cut carrier nothing actively
knows `c0` (`∀ y, ¬ cutKnows y c0`, since `c0 ≠ c1`): a moment nothing holds, which ceases when attention
withdraws. The SAME asymmetric knowing is the import (`¬ Recoverable (cutLift)`): the cessation is
attention-relative, one structure with the continuity lift. -/
theorem ws4_cessation_relative (hinf : ℵ₀ ≤ κ) :
    (∃ x : CCar, ∀ y : CCar, ¬ cutKnows y x) ∧ ¬ Recoverable (cutLift hinf) := by
  refine ⟨⟨c0, ?_⟩, ws2_cont_is_import hinf⟩
  intro y; revert y; decide

/-- **CONSERVATIVE REACHABLE.** On the merged carrier every moment is known by another (mutual `mergeKnows`),
so nothing ceases. -/
theorem ws4_conservative_reachable : ∀ x : MCar, ∃ y : MCar, mergeKnows y x := by
  intro x; revert x; decide

end P2S6
