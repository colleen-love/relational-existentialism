/-
`program-3/series-2/formal/P3S2/ws5.lean`

WS5 - The verdict: the outcome computed through flags bound to the series' own theorems. Program 3
Series 2 (3.2), the ledger.

- `Outcome`: `ledger` (all targets land), `unbalanced` (the total is not closed), `porous` (a region law
  fails), `partial'`;
- `ws5_verdict_tied`: for any flags whose truth is equivalent to the flag's justifying proposition, the
  verdict is `ledger`, each flag discharged inside the proof from the series' own theorems;
- `ws5_verdict_eq`: the literal reading, standing beside the tying theorem.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2.ws1
import P3S2.ws2
import P3S2.ws3
import P3S2.ws4

namespace P3S2

open P3S0 P3S1

set_option linter.unusedVariables false

/-- The pre-registered outcomes of the series. -/
inductive Outcome where
  | ledger
  | unbalanced
  | porous
  | partial'
deriving DecidableEq

/-- The verdict as a function of the four flags: the closed total (else `unbalanced`), the region laws
(else `porous`), the orbit characterization and the orthogonality of creation (either failing is
`partial'`); all four give `ledger`. -/
def verdict (totalZero regionLaws orbits orthogonal : Bool) : Outcome :=
  if totalZero = false then Outcome.unbalanced
  else if regionLaws = false then Outcome.porous
  else if orbits = false ∨ orthogonal = false then Outcome.partial'
  else Outcome.ledger

/-- The verdict computed through flags bound to their justifying propositions: the closed total in every
state, the exact flux law for every region and non-degenerate move, the orbit characterization, and the
orthogonality of capacity change to the flow. Each flag is discharged inside the proof from the series'
own theorems. -/
theorem ws5_verdict_tied (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (∀ g : G, ∑ w : Fin 3, charge g w = 0))
    (h2 : b2 = true ↔ (∀ (x y z : Fin 3) (g : G) (r : Finset (Fin 3)), y ≠ z →
        regionCharge (transport x y z g) r - regionCharge g r
          = (if y ∈ r then charge (transport x y z g) y - charge g y else 0)
          + (if z ∈ r then charge (transport x y z g) z - charge g z else 0)))
    (h3 : b3 = true ↔ (∀ g h : G, Connected g h ↔ capVec g = capVec h))
    (h4 : b4 = true ↔ (∀ g h : G, capVec g ≠ capVec h → ¬ Connected g h)) :
    verdict b1 b2 b3 b4 = Outcome.ledger := by
  have e1 : b1 = true := h1.mpr ws1_total_charge_zero
  have e2 : b2 = true := h2.mpr ws2_region_flux
  have e3 : b3 = true := h3.mpr ws3_orbits_are_capacity
  have e4 : b4 = true := h4.mpr ws4_creation_not_flow
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- The verdict read off the literal all-true flags. Stands beside `ws5_verdict_tied`, which ties each
flag to its justifying theorem; alone it would be a boolean standing in for the content. -/
theorem ws5_verdict_eq : verdict true true true true = Outcome.ledger := rfl

end P3S2
