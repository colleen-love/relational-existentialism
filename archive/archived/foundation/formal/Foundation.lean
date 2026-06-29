/-
# `foundation/` — stable, mathlib-bound shared infrastructure (handoff XIII)

The traced-SMC typeclass + JSV axioms (`Foundation.Traced`), the matrix arena / traced-SMC instance
(`Foundation.MatrixModel`), and the partial-trace *operation* (`Foundation.PartialTrace`). Imported by
`theory/` and both papers; never forked. Held to mathlib standards and versioned toward an eventual mathlib
PR.

The substrate (`MatrixModel`, `PartialTrace`) was hoisted here from `paper-1`'s `Scratch.*` in handoff XXI
(the proof-DAG reorg): it is general, dimension-agnostic, not theory-specific. Module namespaces are
preserved (`RelExist.*`) at the move; only their addresses changed. *(D1 — that self-relation **is** that
trace — stays a theory axiom; only the trace **operation** lives here.)*
-/
import Foundation.Traced
import Foundation.MatrixModel
import Foundation.PartialTrace
