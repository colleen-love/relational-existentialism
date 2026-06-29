# T.01 — Energy is the rotating band

> *Node `T.01` of the proof DAG ([`NODES.md`](NODES.md)).* Lean: `Theory.RotatingSpectrum`
> (`theory/formal/Theory/RotatingSpectrum.lean`); imports mathlib only. **Double-imported** (paper one and
> paper two), hence a shared `T` node.

The co-direction channel is the Schur (entrywise) multiplier `schur μ M i j = μ i j · M i j`; iterating it,
`(schur μ)ⁿ M i j = (μ i j)ⁿ · M i j`. Each edge is read off `‖μ i j‖`: `‖μ‖ = 1` is **sustained**
(magnitude conserved at every depth — `schur_sustained`), `‖μ‖ < 1` is **transient** (decays to `0` —
`schur_transient_tendsto`). The per-edge generator `genReal μ i j = Re log(μ i j) ≤ 0` is the **arrow**
(strictly `< 0` off the conserved band). The conserved (`‖μ‖ = 1`) edges split into **fixed** (`μ = 1`,
knowing) and **rotating** (`μ ≠ 1`, energy) — the latter is what `T.03` identifies with the conserved
remainder.

Consumed by **T.02** (the band lattice). Canonical axioms: [`AXIOMS.md`](AXIOMS.md).
