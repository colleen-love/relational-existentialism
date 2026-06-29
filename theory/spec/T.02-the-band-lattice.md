# T.02 — The band lattice

> *Node `T.02`.* Lean: `Theory.BandCoincidence` (`theory/formal/Theory/BandCoincidence.lean`); imports
> **T.01** (`Theory.RotatingSpectrum`). **Double-imported**, a shared `T` node.

The bands are submodules of `Matrix A A ℂ` supported on edge predicates (`bandOn P` = coherences vanishing
off the `P`-edges): the **fixed** band (`μ = 1`, knowing), the **rotating** band (`‖μ‖ = 1, μ ≠ 1`, energy),
the **conserved** band (`‖μ‖ = 1`, their join), and the operational **seam** band. Subset relations reduce to
edge-predicate implications (`bandOn_mono`); equal predicates give equal bands (`bandOn_congr`). This is the
lattice on which `T.03` proves the band coincidence (the conserved remainder *is* the energy band) from the
axioms.

Consumed by **T.03** (`BandFromAxioms`). Canonical axioms: [`AXIOMS.md`](AXIOMS.md).
