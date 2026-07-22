/-
`program-3/series-0/formal/P3S0.lean`

Program 3 Series 0 (3.0), THE FLOW — the aggregator root.

The ground of Program 3: a reversible, capacity-conserving, charge-exchanging flow dynamics on the whole
state space of attention graphs over a three-element carrier. This root imports the five workstreams:

- `P3S0.ws1` — the state space, the transport move, and its reversibility (the ground);
- `P3S0.ws2` — capacity conservation, the zero-sum exchange, and the bridge to Program 2's increment;
- `P3S0.ws3` — the two-sided wall as a state of the flow, and its reachability (non-degeneracy);
- `P3S0.ws4` — the fuel-based reachability and the connectivity theorem;
- `P3S0.ws5` — the verdict, tied to the series' own theorems.

The series boundary import is `PR2R1` (in `P3S0.ws1`), which reaches `P2S8` and the rest of the built arc
transitively; nothing else is imported directly. `P3S0.AxiomCheck` runs the axiom pass.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0.ws1
import P3S0.ws2
import P3S0.ws3
import P3S0.ws4
import P3S0.ws5
