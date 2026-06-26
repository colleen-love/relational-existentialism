/-
# The valuation boundary: non-unit cost on a dense standing lattice is genuinely impossible

[`SparsityPosits`](SparsityPosits.lean) constructed the **unit** valuation — the return index — for the
finite-depth selves sparsity counts, discharging the posited `μ` for unit per-return cost. It flagged a
residue: a *non-unit* numeric cost `λ > 1`, a quantitative *amount* of standing per return, needs a
discretizing measure `μ : standing → ℕ`, "no `ℕ`-valued strictly-monotone map exists on a dense order."
This module proves that flag is a **theorem**, not an excuse — turning the residue into a precise boundary.

* `no_strictMono_to_nat_of_dense` — **a densely-ordered standing lattice admits no `ℕ`-valuation.** If the
  standing order is densely ordered (between any two standings lies a third — e.g. `[0,1]`, `ℝ≥0`, `ℚ`),
  there is **no** strictly-monotone `μ : standing → ℕ`. Proof: density builds an infinite strictly
  ascending sequence inside any interval `(a₀, b₀)`, whose `μ`-images would be an infinite strictly
  ascending sequence of naturals all below `μ b₀` — impossible (`n ≤ μ(seqₙ) < μ b₀` for all `n`).

So a numeric `μ` registering genuine standing increments **cannot exist** when standing is dense: the
non-unit valuation is not a gap we declined to fill, it is **provably unavailable** without first
discretizing the standing lattice. The constructive flip is in `SparsityPosits`: when the orbit is
finite-depth (the **ACC** regime of [`Stabilization`](Stabilization.lean)), the chain is a finite strict
ascent and the return-index *is* the valuation — there the discretization is automatic. Dense ⇒ no `μ`;
ACC/finite ⇒ canonical `μ`. The boundary is exactly the order-theoretic dichotomy, now proved.

**Honest scope.** Elementary order theory (density vs. the discreteness of `ℕ`), mechanized. Its worth is
that it *closes* the last sparsity residue the right way — by proving the boundary rather than asserting
it — and pins the valuation's existence to the same ACC condition that governs finite depth.
-/
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

namespace RelExist.ValuationBoundary

variable {α : Type*} [Preorder α] [DenselyOrdered α]

/-- A strictly ascending sequence inside `(·, b₀)`: starting from any `start < b₀`, density supplies a
next point strictly above and still below `b₀`. The witness that a dense interval contains an infinite
strict ascent. -/
private noncomputable def denseSeq {b₀ : α} (start : {x : α // x < b₀}) :
    ℕ → {x : α // x < b₀}
  | 0 => start
  | n + 1 => ⟨Classical.choose (exists_between (denseSeq start n).2),
              (Classical.choose_spec (exists_between (denseSeq start n).2)).2⟩

private theorem denseSeq_lt {b₀ : α} (start : {x : α // x < b₀}) (n : ℕ) :
    (denseSeq start n).1 < (denseSeq start (n + 1)).1 :=
  (Classical.choose_spec (exists_between (denseSeq start n).2)).1

/-- **A densely-ordered standing lattice admits no `ℕ`-valuation.** Given any two distinct standings
`a₀ < b₀`, there is no strictly-monotone `μ : α → ℕ`: density manufactures an infinite strictly ascending
sequence in `(a₀, b₀)`, and its `μ`-images are an infinite strictly ascending sequence of naturals all
`< μ b₀` — but `n ≤ μ(seqₙ)` forces them unbounded. Hence a numeric per-return cost on dense standing
requires a prior discretization; it cannot be read off the order alone. -/
theorem no_strictMono_to_nat_of_dense {a₀ b₀ : α} (hab : a₀ < b₀)
    (μ : α → ℕ) (hμ : StrictMono μ) : False := by
  -- a strictly ascending sequence in (a₀, b₀)
  let start : {x : α // x < b₀} := ⟨a₀, hab⟩
  -- g n := μ (denseSeq start n) is strictly increasing in ℕ, hence n ≤ g n
  have hstep : ∀ n, μ (denseSeq start n).1 < μ (denseSeq start (n + 1)).1 :=
    fun n => hμ (denseSeq_lt start n)
  have hid : ∀ n, n ≤ μ (denseSeq start n).1 := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hstep k))
  -- but every g n is below μ b₀
  have hbound : ∀ n, μ (denseSeq start n).1 < μ b₀ := fun n => hμ (denseSeq start n).2
  -- contradiction at n = μ b₀
  exact absurd (Nat.lt_of_le_of_lt (hid (μ b₀)) (hbound (μ b₀))) (Nat.lt_irrefl _)

end RelExist.ValuationBoundary
