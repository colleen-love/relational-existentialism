/-
`program-3/series-1/formal/P3S1/ws5.lean`

WS5 - The verdict: the outcome computed through flags bound to the series' own theorems. Program 3
Series 1 (3.1), the arrow.

- `Outcome`: `arrow` (micro injective, observation lossy for every move, no decoder), `transparent` (the
  summary loses nothing — no arrow emerges), `opaque` (the microdynamics itself loses — would contradict
  Series 3.0), `partial'`;
- `ws5_verdict_tied`: for any flags whose truth is equivalent to the flag's justifying proposition, the
  verdict is `arrow`, each flag discharged inside the proof from the series' own theorems;
- `ws5_verdict_eq`: the literal reading, standing beside the tying theorem.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1.ws1
import P3S1.ws2
import P3S1.ws3
import P3S1.ws4

namespace P3S1

open P3S0

set_option linter.unusedVariables false

/-- The pre-registered outcomes of the series. -/
inductive Outcome where
  | arrow
  | transparent
  | opaque
  | partial'
deriving DecidableEq

/-- The verdict as a function of the four flags: micro injectivity (else `opaque`), the summary's loss
(else `transparent`), the permanence of the loss under every move and the absence of a decoder (either
failing is `partial'`); all four give `arrow`. -/
def verdict (microInj lossy permanent noDecoder : Bool) : Outcome :=
  if microInj = false then Outcome.opaque
  else if lossy = false then Outcome.transparent
  else if permanent = false ∨ noDecoder = false then Outcome.partial'
  else Outcome.arrow

/-- The verdict computed through flags bound to their justifying propositions: micro injectivity of every
move, the lossy pair, the loss's permanence under every move, and the absence of a decoder. Each flag is
discharged inside the proof from the series' own theorems. -/
theorem ws5_verdict_tied (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (∀ x y z : Fin 3, Function.Injective (transport x y z)))
    (h2 : b2 = true ↔ (gFwd ≠ gBwd ∧ summary gFwd = summary gBwd))
    (h3 : b3 = true ↔ (∀ x y z : Fin 3,
        ¬ Function.Injective (fun g => summary (transport x y z g))))
    (h4 : b4 = true ↔ (¬ ∃ back : (Fin 3 → Fin 3 → Bool) → G, ∀ g, back (summary g) = g)) :
    verdict b1 b2 b3 b4 = Outcome.arrow := by
  have e1 : b1 = true := h1.mpr ws3_micro_loses_nothing
  have e2 : b2 = true := h2.mpr ws2_summary_lossy
  have e3 : b3 = true := h3.mpr ws3_observation_always_lossy
  have e4 : b4 = true := h4.mpr ws2_no_decoder
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- The verdict read off the literal all-true flags. Stands beside `ws5_verdict_tied`, which ties each
flag to its justifying theorem; alone it would be a boolean standing in for the content. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.arrow := rfl

end P3S1
