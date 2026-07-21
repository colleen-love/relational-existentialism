/-
`program-2/series-6/formal/P2S6/ws3.lean`

WS3 - The single line is the linearization import (1D lived time). Program 2 Series 6 (2.6).

Reads Series 2.1's linearization import (`P2S1.ws4_linearization_import`, reached transitively) as the SINGLE
LIVED LINE: the partial causal order is endogenous (`ws3_partial_order_endogenous = ws4_causal_order_endogenous`,
witnessed, rank-constrained, genuinely partial with the incomparable pair `kA`,`kB`), but a TOTAL linear order of
the moments is NON-recoverable - for any order label `ord` distinguishing the concurrent pair, the ordered lift
is not `Recoverable` (`ws3_line_is_import`). So the one-dimensionality of lived time is the self's import over a
partially-ordered reality, and it rests on the total order being non-recoverable, NOT on rank being a scalar:
`ws3_line_not_scalar` shows the tower rank cannot even linearize the concurrent pair (`rankT kA = rankT kB`).

Design docs: `program-2/series-6/spec/ws3-design.md`; shared objects `spec/README.md` §2.3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S6.ws2

universe u

namespace P2S6

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE SINGLE LINE IS THE LINEARIZATION IMPORT.** For any order label `ord` distinguishing the concurrent pair
`kA`,`kB`, the ordered lift is NOT `Recoverable`: the single lived line (a total order of the moments) is the
self's import over the partial causal order. Reads `P2S1.ws4_linearization_import` (reached transitively) as the
single line. -/
theorem ws3_line_is_import (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord) :=
  fun ord h => (ws4_linearization_import hinf ord h).2

/-- **THE PARTIAL ORDER IS ENDOGENOUS (the contrast).** The causal order is witnessed (`kA ≺ kC`, `kB ≺ kC`),
rank-constrained, and genuinely PARTIAL (the concurrent pair `kA`,`kB` is incomparable). The partial order is
recoverable; the TOTAL line over it (WS3 headline) is not. -/
theorem ws3_partial_order_endogenous :
    (causal kA kC ∧ causal kB kC)
  ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA) :=
  ws4_causal_order_endogenous

/-- **THE LINE IS NOT SCALAR RANK (audit d).** The tower rank cannot linearize the concurrent pair
(`rankT kA = rankT kB`), so the one-dimensionality of lived time rests on the linearization being non-recoverable,
not on rank being an ℕ-valued scalar. -/
theorem ws3_line_not_scalar : rankT kA = rankT kB := by decide

end P2S6
