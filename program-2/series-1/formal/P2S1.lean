/-
`program-2/series-1/formal/P2S1.lean`

Program 2 Series 1 (2.1), the TICK - aggregator. Imports the five workstreams. Builds on the `P2S0` ground
(and, transitively through it, the `P1` foundation); it does NOT import `P1` directly (the layered chain
`P1 → S0 → S1`, program charter §2). Namespace `P2S1`.

- WS1 (`ws1`): the attention cycle and its composite (the tick), well-formed and finite.
- WS2 (`ws2`): subtractivity (the free residue) and the arrow (the reader load-bearing, the tick irreversible).
- WS3 (`ws3`): the stream (S0's `impLift` at the choice-point), exogenous and load-bearing.
- WS4 (`ws4`): the clock knot - causal order endogenous, linearization import, the two-zone fork.
- WS5 (`ws5`): the verdict computed to twoZone, the audit (a)-(e) folded in.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1
import P2S1.ws2
import P2S1.ws3
import P2S1.ws4
import P2S1.ws5
