/-
`program-3/series-2/formal/P3S2.lean`

Program 3 Series 2 (3.2), the ledger — the aggregator root.

Conservation returns as a theorem about regions: the world's total ledger is closed in every state, a
region's ledger obeys an exact flux law under every move (conserved in the interior and exterior, exact at
the boundary), the flow's orbits are precisely the capacity classes, and creation — capacity change — is
provably outside the flow. This root imports the four workstreams and the verdict:

- `P3S2.ws1` — the region ledger and the closed total;
- `P3S2.ws2` — the region laws: the exact flux law and its three faces;
- `P3S2.ws3` — the orbits: connectivity is capacity equality;
- `P3S2.ws4` — creation orthogonal to the flow; the holonomy as the ledger's blind spot;
- `P3S2.ws5` — the verdict, tied to the series' own theorems.

The series boundary import is `P3S1` (in `P3S2.ws1`), reaching `P3S0` and the Program 2 arc transitively.
`P3S2.AxiomCheck` runs the axiom pass.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2.ws1
import P3S2.ws2
import P3S2.ws3
import P3S2.ws4
import P3S2.ws5
