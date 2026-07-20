/-
`program-2/series-3/formal/P2S3.lean` — Program 2 Series 3 (2.3), the COHERENCE (aggregator root).

Aggregates the five workstreams: the valuation and `Converges₂` (`ws1`), the in-sight zone forced (`ws2`), the
dissent-is-import zone (`ws3`), the two-zone fork (`ws4`), and the computed verdict (`ws5`). Series 2.3 builds on
the `P2S2` pair (and through it, transitively, `P2S1` / `P2S0` / the `P1` foundation); it never reaches `P2S1` /
`P2S0` / `P1` directly. The convergence machinery (`Valuation` / `Converges₂` / `Faithful₂` / `InSight` /
`valLift`) is built FRESH and constrained, NOT imported from Series 12 (excluded from the foundation for
program-review-1's PR1-S1). The `P2S3.AxiomCheck` root runs the axiom pass.
-/
import P2S3.ws1
import P2S3.ws2
import P2S3.ws3
import P2S3.ws4
import P2S3.ws5
