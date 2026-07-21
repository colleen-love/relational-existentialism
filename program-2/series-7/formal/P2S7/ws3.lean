/-
`program-2/series-7/formal/P2S7/ws3.lean`

WS3 - The import is the sole source (conservation modulo the import). Program 2 Series 7 (2.7).

Imports `P2S7.ws2`. Proves that every change in `Q` is an import: any two configurations the self's sight
identifies (plain-bisimilar) that carry different `Q` differ by a `¬ Recoverable` distinction (`rankM_sep_general`
from WS1 supplies the label-separation; the collapse engine supplies the plain-bisimilarity; `ws4_recoverable_not_import`,
transitively `P1.Core` / Series 07, turns the whole measure lift into a non-recoverable import). So `Q` is conserved
in the closed subsystem (in-sight) and moves ONLY across an import — the import the sole source. A genuine import
that DOES change `Q` exists (the source is non-vacuous). The import is quantified, never named.

Design docs: `program-2/series-7/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws2

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **EVERY CHANGE IN `Q` IS AN IMPORT (WS3, Series 07).** For any two states with different `Q` (`rankM x ≠
rankM y`), the measure lift plain-identifies them (the collapse engine `ws1_atomless_bisim`, both `SHNE`) yet is
label-separated (the rank gap, `rankM_sep_general`): exactly `AttentionDistinguishes`. So a `Q`-change over the
plain (in-sight) quotient is a `¬ Recoverable` distinction, not an in-sight difference. And the whole measure lift
is non-recoverable (an import), via `ws4_recoverable_not_import` (Series 07): the source is the import, quantified,
never named. Conservation modulo the import, the general-relativity shape. -/
theorem ws3_change_is_source (hinf : ℵ₀ ≤ κ) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ ¬ Recoverable (destML hinf) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    refine ⟨?_, ?_⟩
    · show ∃ R, IsBisim (plainOf (destML hinf)) R ∧ R x y
      rw [destML, plainOf_rankLiftM]
      exact ws1_atomless_bisim (outDest hinf attendsM) x y (SHNE_M hinf x) (SHNE_M hinf y)
    · show ¬ ∃ R, IsBisimL (destML hinf) R ∧ R x y
      exact rankM_sep_general (outDest hinf attendsM) rankM x y hxy (outDestM_ne_empty hinf x)
  · intro hrec
    obtain ⟨hbisim, hsep⟩ := (ws1_rank_nontrivial hinf).2.1
    exact hsep (ws4_recoverable_not_import (destML hinf) hrec _ _ hbisim)

/-- **THE SOURCE IS NON-VACUOUS (WS3, no fiat).** A genuine import that DOES change `Q`: the reified relatum `e1`
and its base `e0` are `AttentionDistinguishes` (plain-alike, label-apart) and carry different `Q` (`rankM e1 =
1 ≠ 0`). The import that sources the measure is inhabited, not empty. -/
theorem ws3_source_nonvacuous (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (destML hinf) e1 e0 ∧ rankM e1 ≠ rankM e0 :=
  ⟨(ws1_rank_nontrivial hinf).2.1, (ws1_rank_nontrivial hinf).1⟩

end P2S7
