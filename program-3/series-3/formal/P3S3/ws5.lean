/-
`program-3/series-3/formal/P3S3/ws5.lean`

WS5 - The verdict. Program 3 Series 3 (3.3), the phase.

- `Outcome`: `phase` (composition, path dependence, the forced sign, both interference poles), `exact'`
  (the winding is a state function — no phase), `unforced` (the classification fails), `partial'`;
- `ws5_verdict_tied` in the tying pattern; `ws5_verdict_eq` beside it.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws1
import P3S3.ws2
import P3S3.ws3
import P3S3.ws4

namespace P3S3

open P3S0 P3S1

set_option linter.unusedVariables false

/-- The pre-registered outcomes of the series. -/
inductive Outcome where
  | phase
  | exact'
  | unforced
  | partial'
deriving DecidableEq

/-- The verdict as a function of the four flags: path dependence (else `exact'`), the sign classification
(else `unforced`), composition and the interference poles (either failing is `partial'`); all four give
`phase`. -/
def verdict (pathDependent signForced composes interferes : Bool) : Outcome :=
  if pathDependent = false then Outcome.exact'
  else if signForced = false then Outcome.unforced
  else if composes = false ∨ interferes = false then Outcome.partial'
  else Outcome.phase

/-- The verdict computed through flags bound to their justifying propositions: the co-terminal pair with
distinct windings, the classification of the `±1` phase family, the cocycle law of the winding, and the
two interference poles on named histories. Each flag is discharged inside the proof from the series' own
theorems. -/
theorem ws5_verdict_tied (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (run hDirect gFwd = run hRouted gFwd
        ∧ wind hDirect gFwd = 1 ∧ wind hRouted gFwd = 2))
    (h2 : b2 = true ↔ (∀ s : ℤ → ℤ, (∀ a b : ℤ, s (a + b) = s a * s b) →
        (∀ n : ℤ, s n = 1 ∨ s n = -1) →
        (∀ n : ℤ, s n = 1) ∨ (∀ n : ℤ, s n = if n % 2 = 0 then 1 else -1)))
    (h3 : b3 = true ↔ (∀ (h1 h2 : Hist) (g : G),
        wind (h1 ++ h2) g = wind h1 g + wind h2 (run h1 g)))
    (h4 : b4 = true ↔ ((run hDirect gFwd = run hRouted gFwd
        ∧ (amp (wind hDirect gFwd) + amp (wind hRouted gFwd)) ^ 2
            < (amp (wind hDirect gFwd)) ^ 2 + (amp (wind hRouted gFwd)) ^ 2)
      ∧ (run hLong gFwd = run hDirect gFwd
        ∧ (amp (wind hDirect gFwd)) ^ 2 + (amp (wind hLong gFwd)) ^ 2
            ≤ (amp (wind hDirect gFwd) + amp (wind hLong gFwd)) ^ 2))) :
    verdict b1 b2 b3 b4 = Outcome.phase := by
  have e1 : b1 = true := h1.mpr ws2_winding_path_dependent
  have e2 : b2 = true := h2.mpr ws3_sign_forced
  have e3 : b3 = true := h3.mpr ws1_wind_append
  have e4 : b4 = true := h4.mpr ws4_interference_on_histories
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- The verdict read off the literal all-true flags, standing beside the tying theorem. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.phase := rfl

end P3S3
