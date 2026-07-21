/-
`program-2/series-7/formal/P2S7/ws3.lean`

WS3 - The measure is NOT conserved; the rise is genuine import-content. Program 2 Series 7 (2.7).

Imports `P2S7.ws2`. Two honest facts. (1) `rankM` is NOT conserved in-sight: a plain-bisimilar pair (the tick's
product `e1` and its constituent `e0`) carries DIFFERENT `rankM`, so `rankM` is not plain-bisimulation-invariant;
and any measure that IS plain-invariant (a genuine in-sight-conserved measure) must AGREE on `e1` and `e0`, i.e. is
blind to the tick — the only conserved measures are trivial on the tick pair. So no non-trivial measure is conserved
in-sight (`ws3_not_conserved`). (2) Every change in `rankM` is a genuine import — a non-recoverable distinction
(`ws3_change_is_source`, resting on Series 07 `ws4_recoverable_not_import`) — so the rise is REAL creation of
import-content, not a bookkeeping artifact; the source is non-vacuous (`ws3_source_nonvacuous`). Together: the arrow
is genuine and nothing is conserved (MONOTONE-ONLY).

Design docs: `program-2/series-7/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws2

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE MEASURE IS NOT CONSERVED IN-SIGHT (WS3, the no-ledger heart).** `rankM` is not plain-bisimulation-invariant:
the tick's product `e1` and its constituent `e0` are plain-bisimilar (the collapse engine) yet carry different `rankM`
(`1 ≠ 0`). And any genuinely in-sight-conserved measure — a `plainOf`-bisimulation-invariant `f` — must AGREE on `e1`
and `e0` (they are plain-bisimilar), so it cannot track the tick: the only conserved measures are blind to the rise.
The collapse (states bisimilar) does NOT conserve `rankM`; it hides that `rankM` rose. So no non-trivial measure is
conserved in-sight. -/
theorem ws3_not_conserved (hinf : ℵ₀ ≤ κ) :
    ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (∀ f : MCar → ℕ,
        (∀ x y, (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R x y) → f x = f y) → f e1 = f e0) := by
  have hbisim : ∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0 := (ws1_rank_nontrivial hinf).2.1.1
  refine ⟨⟨hbisim, (ws1_rank_nontrivial hinf).1⟩, ?_⟩
  intro f hf
  exact hf e1 e0 hbisim

/-- **EVERY CHANGE IN `Q` IS A GENUINE IMPORT (WS3, Series 07).** For any two states with different `rankM`, the
measure lift plain-identifies them (the collapse engine) yet is label-separated (`rankM_sep_general`): exactly
`AttentionDistinguishes`. So each increment of the measure is a `¬ Recoverable` import (via `ws4_recoverable_not_import`,
Series 07): the rise is REAL creation of import-content, not a bookkeeping artifact. The import is quantified, never
named. -/
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

/-- **THE RISE IS NON-VACUOUS (WS3).** A genuine import that DOES raise `Q`: the reified relatum `e1` and its base
`e0` are `AttentionDistinguishes` (plain-alike, label-apart) and carry different `Q` (`rankM e1 = 1 ≠ 0`). The arrow
is inhabited, not empty. -/
theorem ws3_source_nonvacuous (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (destML hinf) e1 e0 ∧ rankM e1 ≠ rankM e0 :=
  ⟨(ws1_rank_nontrivial hinf).2.1, (ws1_rank_nontrivial hinf).1⟩

end P2S7
