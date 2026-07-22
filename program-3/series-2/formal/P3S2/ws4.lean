/-
`program-3/series-2/formal/P3S2/ws4.lean`

WS4 - Creation orthogonal to the flow, and the residual freedom of the loop. Program 3 Series 2 (3.2), the
ledger.

- `ws4_creation_not_flow`: any change of capacity — the attention-expansion where Program 2 located
  creation — is provably outside the flow: capacity-differing states are never connected. Creation and
  exchange are orthogonal by theorem, not by decree.
- `ws4_holonomy_not_conserved`: a witness that a transport can move Series 2.8's holonomy while the
  world's total ledger stays closed (`ws1_total_charge_zero` holds in every state). The loop structure is
  a finer quantity than the charges — the residual freedom where Program 2 found interference — and the
  ledger does not see it. A forward-note theorem to the phase series.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2.ws3

namespace P3S2

open P3S0 P3S1

set_option linter.unusedVariables false

/-- Any change of capacity is outside the flow: capacity-differing states are never connected. Where
Program 2 located creation — the expansion of attention — the flow cannot go. -/
theorem ws4_creation_not_flow (g h : G) (hne : capVec g ≠ capVec h) : ¬ Connected g h :=
  fun hc => hne ((ws3_orbits_are_capacity g h).mp hc)

/-- A transport can move the holonomy: on Series 2.8's ring, one transport changes the triangle holonomy
from three to one, while the total ledger stays closed in both states. The loop structure is a finer
quantity than the charges; the ledger does not see it. -/
theorem ws4_holonomy_not_conserved :
    P2S8.hol (transport 0 1 2 P2S8.attTri) P2S8.p0 P2S8.p1 P2S8.p2
      ≠ P2S8.hol P2S8.attTri P2S8.p0 P2S8.p1 P2S8.p2
  ∧ ∑ w : Fin 3, charge (transport 0 1 2 P2S8.attTri) w = 0
  ∧ ∑ w : Fin 3, charge P2S8.attTri w = 0 :=
  ⟨by decide, ws1_total_charge_zero _, ws1_total_charge_zero _⟩

end P3S2
