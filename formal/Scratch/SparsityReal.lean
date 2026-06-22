/-
# ℝ-valued sparsity and the density limit — the analytic upgrade of Lemmas 3.1/3.2

The discrete core in `RelExist.Sparsity` is recast over `ℝ` (step 1 of the spec's
[proof strategy](../../docs/spec/03-sparsity-conjecture.md#35-proof-strategy-for-mechanization)),
and the "density → 0" claim of Lemma 3.1 is proved as a genuine `Filter.Tendsto`:

* `stab_card_le_div` — under a finite budget `β`, with every stabilized self costing
  at least a positive floor `m`, the number of selves is `≤ β / m` — a constant bound
  **independent of how many couplings exist** (`Finset.card_nsmul_le_sum`).
* `stab_density_tendsto_zero` — therefore the **stabilized fraction tends to 0** as
  the number of couplings grows: `|Stab N| / N → 0`. This is the formal content of
  "selves are rare" / "you cannot return to everything".

Selves are modeled as a `Finset` of couplings with a real maintenance cost each.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic

namespace RelExist.Real

open Finset Filter Topology

variable {ι : Type*}

/-- **Core counting bound (ℝ).** If every maintained self costs at least `m`, the
number of selves times `m` is at most the total attention spent. -/
theorem card_mul_le_sum (S : Finset ι) (cost : ι → ℝ) (m : ℝ)
    (h : ∀ i ∈ S, m ≤ cost i) : (S.card : ℝ) * m ≤ ∑ i ∈ S, cost i := by
  have h1 := Finset.card_nsmul_le_sum h
  simpa [nsmul_eq_mul] using h1

/-- **Lemma 3.1 (ℝ), division-free.** Finite budget `β`, positive floor `m` ⇒ the
number of selves times `m` is at most `β`. -/
theorem stab_card_le_budget (S : Finset ι) (cost : ι → ℝ) (m β : ℝ)
    (hcost : ∀ i ∈ S, m ≤ cost i) (hbudget : ∑ i ∈ S, cost i ≤ β) :
    (S.card : ℝ) * m ≤ β :=
  le_trans (card_mul_le_sum S cost m hcost) hbudget

/-- **Lemma 3.1 (ℝ), divided form.** `|Stab| ≤ β / m` — a bound independent of the
total number of couplings. -/
theorem stab_card_le_div (S : Finset ι) (cost : ι → ℝ) (m β : ℝ) (hm : 0 < m)
    (hcost : ∀ i ∈ S, m ≤ cost i) (hbudget : ∑ i ∈ S, cost i ≤ β) :
    (S.card : ℝ) ≤ β / m := by
  rw [le_div_iff hm]
  exact stab_card_le_budget S cost m β hcost hbudget

/-- A nonnegative sequence bounded by a constant has vanishing density: if
`0 ≤ card N ≤ C` for all `N`, then `card N / N → 0`. (Squeeze between `0` and
`C / N → 0`.) -/
theorem density_tendsto_zero {C : ℝ} {card : ℕ → ℝ}
    (h0 : ∀ N, 0 ≤ card N) (hC : ∀ N, card N ≤ C) :
    Tendsto (fun N => card N / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun N : ℕ => C / (N : ℝ))
  · intro N
    exact div_nonneg (h0 N) (Nat.cast_nonneg N)
  · intro N
    gcongr
    exact hC N
  · exact tendsto_const_div_atTop_nhds_zero_nat C

/-- **Sparsity as a vanishing density (the formal "selves are rare").** For a family
of configurations `S N` (the couplings present when there are `N` of them), each
under the same finite budget `β` with the same positive cost floor `m`, the fraction
of couplings that stabilize into selves tends to `0`. -/
theorem stab_density_tendsto_zero (S : ℕ → Finset ι) (cost : ι → ℝ) (m β : ℝ)
    (hm : 0 < m)
    (hcost : ∀ N, ∀ i ∈ S N, m ≤ cost i)
    (hbudget : ∀ N, ∑ i ∈ S N, cost i ≤ β) :
    Tendsto (fun N => ((S N).card : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  apply density_tendsto_zero (C := β / m)
  · intro N; positivity
  · intro N; exact stab_card_le_div (S N) cost m β hm (hcost N) (hbudget N)

end RelExist.Real
