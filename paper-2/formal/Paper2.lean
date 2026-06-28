/-
# `paper-2/` — the modular self-relation paper (frozen fork)

The materialized modular slice of paper two: the lazy fork-and-freeze of six modules from `theory/`
(`Theory.* → Paper2.*`, handoff XVII), forked at `fca792d`. Self-contained: imports only `Paper2.*` +
mathlib — **no** `paper-1/`, **no** `foundation/`. Paper one's seam→arrow result (`SeamForcing`) is **cited
in prose** in the manuscript, not forked; paper two's quantitative dependence on the arrow is the forked band
layer (`Paper2.RotatingSpectrum`/`BandFromAxioms` — `genReal`, the conserved band).

The slice (the modular reading of A1, the conserved band, the equilibrium one generator, the einselection
principle + presence): `Paper2.{ModularFlow, RotatingSpectrum, BandCoincidence, BandFromAxioms, OneGenerator,
Einselection}`. The A2-priority / A3-generative work (`We`, `Priority`, `MutualCoupling`) is **not** forked —
it serves the conservation and sparsity papers, not the modular slice.
-/
import Paper2.ModularFlow
import Paper2.RotatingSpectrum
import Paper2.BandCoincidence
import Paper2.BandFromAxioms
import Paper2.OneGenerator
import Paper2.Einselection
