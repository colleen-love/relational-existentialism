/-
`program-3/series-0/formal/P3S0/ws5.lean`

WS5 - The verdict: the outcome computed through flags bound to the series' own theorems. Program 3 Series 0
(3.0), THE FLOW.

The verdict of the series, in the tying pattern of Program Review 2-1:

- `Outcome`: `flowing` (all targets land), `rigid` (a move fails bijectivity, refuting the ground at the
  microdynamics), `leaky` (conservation fails), `partial'` (connectivity or non-degeneracy lands only in
  witnessed form);
- `verdict`: the outcome as a function of five boolean flags;
- `ws5_verdict_tied`: for any flags whose truth is equivalent to the flag's justifying proposition, the
  verdict is `flowing` — each flag derived inside the proof from this series' own theorems (reversibility,
  capacity, the zero-sum exchange, connectivity, the wall's non-degeneracy), never assumed;
- `ws5_verdict_eq`: the same verdict read off the literal all-true flags, standing beside the tying theorem.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0.ws1
import P3S0.ws2
import P3S0.ws3
import P3S0.ws4

universe u

namespace P3S0

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- The pre-registered outcomes of the series. -/
inductive Outcome where
  | flowing
  | rigid
  | leaky
  | partial'
deriving DecidableEq

/-- The verdict as a function of the five flags: reversibility (else the ground is `rigid`), capacity and the
zero-sum exchange (either failing is `leaky`), connectivity and non-degeneracy (either only witnessed is
`partial'`); all five give `flowing`. -/
def verdict (reversible capacity exchange connected nondegen : Bool) : Outcome :=
  if reversible = false then Outcome.rigid
  else if capacity = false ∨ exchange = false then Outcome.leaky
  else if connected = false ∨ nondegen = false then Outcome.partial'
  else Outcome.flowing

/-- The verdict computed through flags bound to their justifying propositions. For any five booleans whose
truth is equivalent to the corresponding proposition — reversibility of every transport, capacity
conservation, the bystander-and-partner zero-sum exchange, connectivity of equal-capacity states, and the
non-degeneracy of the wall — the verdict is `flowing`. Each flag is discharged inside the proof from the
series' own theorems, so no boolean stands in for a theorem. -/
theorem ws5_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ (∀ (x y z : Fin 3) (g : G), transport x y z (transport x y z g) = g))
    (h2 : b2 = true ↔ (∀ (x y z : Fin 3) (g : G) (w : Fin 3),
        ((transport x y z g) w).card = (g w).card))
    (h3 : b3 = true ↔ (∀ (x y z : Fin 3) (g : G),
        (∀ w, w ≠ y → w ≠ z → charge (transport x y z g) w = charge g w)
      ∧ (charge (transport x y z g) y + charge (transport x y z g) z = charge g y + charge g z)))
    (h4 : b4 = true ↔ (∀ (g k : G), capVec g = capVec k → Connected g k))
    (h5 : b5 = true ↔ (¬ ∃ R, IsBisim (outDest hinf PR2R1.attV) R ∧ R PR2R1.v1 PR2R1.v0)) :
    verdict b1 b2 b3 b4 b5 = Outcome.flowing := by
  have e1 : b1 = true := h1.mpr ws1_moves_reversible
  have e2 : b2 = true := h2.mpr ws2_capacity_conserved
  have e3 : b3 = true := h3.mpr ws2_exchange_zero_sum
  have e4 : b4 = true := h4.mpr ws4_flow_connects
  have e5 : b5 = true := h5.mpr (ws3_wall_is_a_state hinf).1
  subst e1; subst e2; subst e3; subst e4; subst e5
  rfl

/-- The verdict read off the literal all-true flags. Stands beside `ws5_verdict_tied`, which ties each flag to
its justifying theorem; alone it would be a boolean standing in for the content. -/
theorem ws5_verdict_eq : verdict true true true true true = Outcome.flowing := rfl

end P3S0
