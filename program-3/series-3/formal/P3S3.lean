/-
`program-3/series-3/formal/P3S3.lean`

Program 3 Series 3 (3.3), the phase — the aggregator root.

Flow histories carry a genuine phase: histories compose and the winding is a cocycle (ws1); the winding is
path-dependent — genuine holonomy (ws2); every composition-respecting `±1` phase is trivial or parity, so
the sign is forced, not chosen (ws3); co-terminal histories interfere by the parity of their winding
difference, with both poles witnessed, and the cancellation test provably does not force the exponent
(ws4); the verdict is tied (ws5).

The series boundary import is `P3S2` (in `P3S3.ws1`). `P3S3.AxiomCheck` runs the axiom pass.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws1
import P3S3.ws2
import P3S3.ws3
import P3S3.ws4
import P3S3.ws5
