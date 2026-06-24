/-
# Self in other, quantified — the distribution of self across the relational network

A first quantitative piece of the **spectral form** of the sparsity dichotomy
([spec 03 §3.4, Conjecture 3.4](../../docs/spec/03-sparsity-conjecture.md)): how much of a self
is distributed into others through relating, and the **limit** at which it stays bounded.

Work in a **Banach algebra** `E` (a complete normed ring). An element `x : E` is the
gain-weighted relating — `‖x‖` its intensity. The *self distributed into others* is the
path-sum over relatings of length `≥ 1`: direct (`x`), via a third (`x²`), and onward —

    distributed x = ∑' n, x ^ (n + 1).

The reading of `‖x‖`, exactly as the dynamics suggest:

* **`x = 0` — complete disconnection.** No relating, so no self in any other: `distributed 0 = 0`.
  A perfectly sealed self, present nowhere but itself.
* **`0 < ‖x‖ < 1` — the living regime.** The series converges and the distributed self is
  **bounded**, `‖distributed x‖ ≤ ‖x‖ / (1 - ‖x‖)`: an individuated self with a finite, localized
  footprint in others. The bound rises with intensity — the more you relate, the more of you is
  abroad — but stays finite.
* **`‖x‖ ≥ 1` — death / dissolution.** The bound `‖x‖/(1-‖x‖)` diverges; the self delocalizes,
  its footprint unbounded, the boundary between it and the between dissolving. Past the limit
  there is no longer a localized self to speak of.

So the living self sits in the open interval `0 < ‖x‖ < 1`; the endpoints are the two ways to
have no self — sealed off at `0`, smeared away at `1`.
-/
import Mathlib.Analysis.SpecificLimits.Normed

namespace RelExist.Distribution

variable {E : Type*} [NormedRing E]

/-- **Self distributed into others**: the part of a self carried into the network by the
relating `x`, summed over all relating-paths of length `≥ 1` (direct, via a third, …). -/
noncomputable def distributed (x : E) : E := ∑' n : ℕ, x ^ (n + 1)

/-- **Complete disconnection ⇒ no self in any other.** With no relating (`x = 0`), nothing of
the self is anywhere else. -/
@[simp] theorem distributed_zero : distributed (0 : E) = 0 := by
  have h : (fun n : ℕ => (0 : E) ^ (n + 1)) = fun _ => 0 :=
    funext fun n => zero_pow (Nat.succ_ne_zero n)
  rw [distributed, h, tsum_zero]

/-- In the **living regime** (`‖x‖ < 1`) the path-sum converges — the distributed self is a
well-defined element, not a divergent smear. -/
theorem distributed_summable [CompleteSpace E] {x : E} (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => x ^ (n + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one hx)

/-- **The bound — the quantitative limit of self in other.** In the living regime the
distributed self is bounded by `‖x‖ / (1 - ‖x‖)`: finite, rising with the intensity of
relating, and diverging only as `‖x‖ → 1` (the dissolution limit). -/
theorem distributed_bound [CompleteSpace E] {x : E} (hx : ‖x‖ < 1) :
    ‖distributed x‖ ≤ ‖x‖ / (1 - ‖x‖) := by
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ n : ℕ, ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) :=
    fun n => norm_pow_le' x n.succ_pos
  have hmaj : Summable (fun n : ℕ => ‖x‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hnn hx)
  have hsumnorm : Summable (fun n : ℕ => ‖x ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have hgeo : ∑' n : ℕ, ‖x‖ ^ (n + 1) = ‖x‖ / (1 - ‖x‖) := by
    have hpow : (fun n : ℕ => ‖x‖ ^ (n + 1)) = fun n => ‖x‖ * ‖x‖ ^ n :=
      funext fun n => pow_succ' ‖x‖ n
    rw [hpow, tsum_mul_left, tsum_geometric_of_lt_one hnn hx, div_eq_mul_inv]
  calc ‖distributed x‖ ≤ ∑' n : ℕ, ‖x ^ (n + 1)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n : ℕ, ‖x‖ ^ (n + 1) := tsum_le_tsum hterm hsumnorm hmaj
    _ = ‖x‖ / (1 - ‖x‖) := hgeo

/-! ### The self as a fixed point of feedback — registration and the bound, fused

The **full self** `total x = ∑ xⁿ` (the path-sum *including* length 0 — the self before it
leaves itself) satisfies a feedback fixed-point equation. This is the quantitative **eigenform**
([A3](../../docs/spec/02-axioms.md), [D1](../../docs/spec/02-axioms.md)): the self is a fixed
point of co-directed feedback, now in the same Banach algebra that bounds it — so registration
(the self contains itself, one relating deep) and the distribution bound are one object. -/

/-- The **full self**: the path-sum from length 0 (itself), `∑ xⁿ`. `total x = 1 + distributed x`
— the self is itself, plus the part of it that has left into others. -/
noncomputable def total (x : E) : E := ∑' n : ℕ, x ^ n

theorem total_eq_one_add_distributed [CompleteSpace E] {x : E} (hx : ‖x‖ < 1) :
    total x = 1 + distributed x := by
  rw [total, distributed, tsum_eq_zero_add (summable_geometric_of_norm_lt_one hx), pow_zero]

/-- **The self is a fixed point of feedback** — the quantitative eigenform. `total x = 1 + x·total x`:
the self is itself plus one relating folded back in. This is registration realized in the Banach
algebra — the self contains itself, one step deep — fusing the order-theoretic
`Attention.closed_loop_registers` with the bounded distribution `distributed`. -/
theorem total_feedback [CompleteSpace E] {x : E} (hx : ‖x‖ < 1) :
    total x = 1 + x * total x := by
  have hs : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_norm_lt_one hx
  have hfun : (fun n : ℕ => x ^ (n + 1)) = fun n => x * x ^ n := funext fun n => pow_succ' x n
  have hxt : ∑' n : ℕ, x ^ (n + 1) = x * ∑' n : ℕ, x ^ n := by
    have h : HasSum (fun n : ℕ => x ^ (n + 1)) (x * ∑' n : ℕ, x ^ n) := by
      rw [hfun]; exact hs.hasSum.mul_left x
    exact h.tsum_eq
  calc total x = x ^ 0 + ∑' n : ℕ, x ^ (n + 1) := tsum_eq_zero_add hs
    _ = 1 + x * ∑' n : ℕ, x ^ n := by rw [pow_zero, hxt]
    _ = 1 + x * total x := rfl

/-- The full self is **bounded** by `(1 - ‖x‖)⁻¹` in the living regime. -/
theorem total_bound [CompleteSpace E] [NormOneClass E] {x : E} (hx : ‖x‖ < 1) :
    ‖total x‖ ≤ (1 - ‖x‖)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one x hx
  rw [norm_one, sub_self, zero_add] at h
  exact h

end RelExist.Distribution
