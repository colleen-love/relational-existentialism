/-
`program-3/series-1/formal/P3S1.lean`

Program 3 Series 1 (3.1), the arrow — the aggregator root.

Irreversibility emerges from coarse-graining a reversible flow: the microdynamics destroys no information
(every transport injective), the direction-erasing summary does (lossy, counted on a named fiber, no
decoder), and the loss is permanent under every further move. This root imports the four workstreams and
the verdict:

- `P3S1.ws1` — the summary and the scale of the micro world;
- `P3S1.ws2` — the loss, counted;
- `P3S1.ws3` — the arrow: reversible beneath, irreversible in every observation above;
- `P3S1.ws4` — the bridges: the summary is `P2S0.sym`; what it erases is the charge;
- `P3S1.ws5` — the verdict, tied to the series' own theorems.

The series boundary import is `P3S0` (in `P3S1.ws1`), reaching the Program 2 arc transitively.
`P3S1.AxiomCheck` runs the axiom pass.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1.ws1
import P3S1.ws2
import P3S1.ws3
import P3S1.ws4
import P3S1.ws5
