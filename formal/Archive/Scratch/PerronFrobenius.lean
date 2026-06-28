/-
# Perron–Frobenius existence — the invariant vector and the invariant state

The conjecture lift's one named-open existence ([03.7](../../docs/spec/03.7-sparsity.md),
Decision 1–2): that a finite-dimensional **unital / column-stochastic** dynamics `Φ_c` *admits* the
peripheral data — an eigenvalue-1 eigenvector (a fixed point of the dynamics) and, with positivity, an
**invariant state** (the relational weight). mathlib has no Perron–Frobenius and no Brouwer / Markov–
Kakutani fixed-point theorem, so both are proved here from scratch.

* `exists_invariant_vector` — **eigenvalue 1 exists** (the algebraic core): a column-stochastic matrix
  fixes the all-ones vector under transpose, so `det(Mᵀ - 1) = 0 = det(M - 1)`, giving a nonzero `v`
  with `M v = v`. The dynamics has a fixed point — the peripheral eigenspace is non-empty, so the
  `P + N` decomposition's peripheral part `P ≠ 0`.
* `exists_invariant_state` — **a positive invariant state exists** (the full Perron–Frobenius): for a
  *nonnegative* column-stochastic `M`, a genuine state (probability vector) `x` with `M x = x`. Proved
  by the **mean-ergodic / Cesàro** argument — the averages `(1/N) Σ Mᵏ x₀` stay in the compact state
  simplex, a convergent subsequence has an invariant limit — avoiding Brouwer via sequential
  compactness. This is the relational **weight** of Decision 1, existence discharged in general (finite
  dim), no longer only for the idempotent `E`.

So the conjecture lift's last existence gap is closed at finite dimension: an arbitrary nonnegative
unital `Φ_c` admits both the fixed point and the invariant state. (The *infinite*-dimensional standard
form, and that the peripheral *subalgebra* is commutative, remain the narrated frontier.)
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Real.Basic

namespace RelExist.PerronFrobenius

open Matrix BigOperators

variable {n : ℕ}

/-! ### The algebraic core: eigenvalue 1 -/

/-- **An invariant vector exists** (eigenvalue 1) for a column-stochastic dynamics. The all-ones vector
is fixed by `Mᵀ`, so `det(Mᵀ - 1) = 0`; transposing, `det(M - 1) = 0`, so `M` has a nonzero fixed
vector. The dynamics' peripheral eigenspace is non-empty. -/
theorem exists_invariant_vector (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hcol : ∀ j, ∑ i, M i j = 1) :
    ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧ M *ᵥ v = v := by
  have hone : Mᵀ *ᵥ (fun _ => 1) = (fun _ => (1 : ℝ)) := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_one]
    exact hcol j
  have hker : (Mᵀ - 1) *ᵥ (fun _ => 1) = 0 := by
    rw [Matrix.sub_mulVec, hone, Matrix.one_mulVec]; simp
  have ho0 : (fun _ => (1 : ℝ)) ≠ (0 : Fin (n + 1) → ℝ) := by
    intro h
    have := congrFun h ⟨0, Nat.succ_pos n⟩
    simp at this
  have hdetT : (Mᵀ - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, ho0, hker⟩
  have hdet : (M - 1).det = 0 := by
    rw [← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_one]; exact hdetT
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  exact sub_eq_zero.mp hv

/-! ### The full Perron–Frobenius: a positive invariant state -/

/-- **A positive invariant state exists** — the full Perron–Frobenius, algebraically. For a
*nonnegative* column-stochastic `M`, taking the eigenvalue-1 eigenvector `v` and its absolute value
`w = |v|`: nonnegativity gives `M w ≥ |M v| = |v| = w` pointwise (triangle inequality), while
column-stochasticity preserves the sum (`∑ M w = ∑ w`); a nonnegative vector with zero total is zero,
so `M w = w`. Normalizing `w` gives a genuine **state** (probability vector) fixed by `M` — the
relational *weight* (Decision 1), no Brouwer / Cesàro needed. -/
theorem exists_invariant_state (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hcol : ∀ j, ∑ i, M i j = 1) :
    ∃ x : Fin (n + 1) → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ M *ᵥ x = x := by
  obtain ⟨v, hv0, hv⟩ := exists_invariant_vector M hcol
  set w : Fin (n + 1) → ℝ := fun i => |v i| with hw
  have hwnn : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
  have hmw : ∀ i, (M *ᵥ w) i = ∑ j, M i j * |v j| := by
    intro i; simp only [Matrix.mulVec, dotProduct, hw]
  -- pointwise super-invariance from the triangle inequality
  have hge : ∀ i, w i ≤ (M *ᵥ w) i := by
    intro i
    have hmv : (M *ᵥ v) i = ∑ j, M i j * v j := by simp only [Matrix.mulVec, dotProduct]
    calc w i = |(M *ᵥ v) i| := by rw [hv]
      _ = |∑ j, M i j * v j| := by rw [hmv]
      _ ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, M i j * |v j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hM i j)]
      _ = (M *ᵥ w) i := (hmw i).symm
  -- the total is preserved
  have hsum : ∑ i, (M *ᵥ w) i = ∑ i, w i := by
    simp_rw [hmw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  -- so the super-invariant nonnegative vector is exactly invariant
  have heq : M *ᵥ w = w := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (M *ᵥ w) i - w i := fun i _ => sub_nonneg.mpr (hge i)
    have hz : ∑ i, ((M *ᵥ w) i - w i) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    funext i
    have := hall i (Finset.mem_univ i)
    linarith
  -- the total is positive, so we can normalize to a state
  have hwpos : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    refine Finset.sum_pos' (fun k _ => hwnn k) ⟨i, Finset.mem_univ i, ?_⟩
    exact abs_pos.mpr hi
  set s : ℝ := ∑ i, w i with hs
  refine ⟨fun i => w i / s, fun i => div_nonneg (hwnn i) hwpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hs, div_self hwpos.ne']
  · have hrw : (fun i => w i / s) = s⁻¹ • w := by funext i; rw [div_eq_inv_mul]; rfl
    rw [hrw, Matrix.mulVec_smul, heq]

end RelExist.PerronFrobenius
