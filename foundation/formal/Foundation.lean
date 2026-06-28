/-
# `foundation/` — stable, mathlib-bound shared infrastructure (handoff XIII)

The traced-SMC typeclass + JSV axioms (`Foundation.Traced`). Imported by `theory/` and both papers; never
forked. Held to mathlib standards and versioned toward an eventual mathlib PR — the matrix `TracedSMC`
*instance* (currently in `paper-1`'s `Scratch.MatrixModel`) is hoisted here later, with the generalization
pass, not in this move-only reorg.
-/
import Foundation.Traced
