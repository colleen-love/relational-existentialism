/-
`program-3/series-4/formal/P3S4/ws5.lean`

WS5 - The verdict. Program 3 Series 4 (3.4), the curve.

- `Outcome`: `curved` (the metric is genuine, moves under the flow, and obeys the exact flux-curvature
  law), `inert` (the metric never moves — Series 2.13 repeated inside the dynamics), `lawless` (the
  metric moves but no exact law holds), `partial'`;
- `ws5_verdict_tied` in the tying pattern; `ws5_verdict_eq` beside it.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S4.ws1
import P3S4.ws2
import P3S4.ws3
import P3S4.ws4

namespace P3S4

open P3S0 P3S1 P3S2 P3S3

set_option linter.unusedVariables false

/-- The pre-registered outcomes of the series. -/
inductive Outcome where
  | curved
  | inert
  | lawless
  | partial'
deriving DecidableEq

/-- The verdict as a function of the four flags: the metric moving (else `inert`), the flux-curvature law
(else `lawless`), the metric's genuineness and the proximity law (either failing is `partial'`); all four
give `curved`. -/
def verdict (metricMoves fluxLaw metricGenuine proximity : Bool) : Outcome :=
  if metricMoves = false then Outcome.inert
  else if fluxLaw = false then Outcome.lawless
  else if metricGenuine = false ∨ proximity = false then Outcome.partial'
  else Outcome.curved

/-- The verdict computed through flags bound to their justifying propositions: the moving metric, the
universal flux-curvature law, the genuine metric with the static grain underdetermining it, and the
proximity law. Each flag is discharged inside the proof from the series' own theorems. -/
theorem ws5_verdict_tied (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (flowDist gFwd 0 1 = 1
        ∧ flowDist (transport 0 1 2 gFwd) 0 1 = 3
        ∧ flowDist gFwd 0 2 = 3
        ∧ flowDist (transport 0 1 2 gFwd) 0 2 = 1))
    (h2 : b2 = true ↔ (∀ (x y z : Fin 3) (g : G), y ∈ g x → z ∉ g x →
        charge (transport x y z g) z = charge g z - 1
        ∧ flowDist (transport x y z g) x z ≤ 1))
    (h3 : b3 = true ↔ ((∀ w, charge gM01 w = charge gM02 w)
        ∧ flowDist gM01 0 1 ≠ flowDist gM02 0 1))
    (h4 : b4 = true ↔ (∀ (g : G) (x z : Fin 3), z ∈ g x → flowDist g x z ≤ 1)) :
    verdict b1 b2 b3 b4 = Outcome.curved := by
  have e1 : b1 = true := h1.mpr ws2_metric_moves
  have e2 : b2 = true := h2.mpr ws4_flux_curves
  have e3 : b3 = true := h3.mpr ws1_grain_underdetermines
  have e4 : b4 = true := h4.mpr ws3_attention_is_proximity
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- The verdict read off the literal all-true flags, standing beside the tying theorem. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.curved := rfl

end P3S4
