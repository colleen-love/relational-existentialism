/-
# The partial trace — the physics (quantum) trace, concretely

In categorical quantum mechanics the doctrine's `Tr` is the **partial trace** on
matrices: feeding the `u`-wire back by summing the diagonal over `u`. This module
mechanizes that operator and its defining properties — the building blocks an
`FdHilb`/`FGModuleCat` `TracedSMC` instance would use (the full instance, with the
associator-as-reindexing coherence, remains the marked frontier).

* `ptrace M i j := ∑ k, M (i,k) (j,k)` — trace out the `u`-factor.
* `ptrace_add`, `ptrace_smul` — linearity.
* `ptrace_prod` — **vanishing-II, computationally**: tracing out `u × v` is tracing out
  `u` then `v` (nested sums).
* `trace_ptrace` — **compatibility**: the full trace of a partial trace is the full trace
  (`Tr` of `Tr_u` is `Tr`), the categorical "vanishing into the unit".
-/
import Mathlib.LinearAlgebra.Matrix.Trace

namespace RelExist.PartialTrace

open Matrix BigOperators

variable {R : Type*} [CommSemiring R] {m n u v : Type*} [Fintype u] [Fintype v]

/-- The **partial trace** of a matrix over its `u`-factor (the QM `Tr`). -/
def ptrace (M : Matrix (m × u) (n × u) R) : Matrix m n R :=
  fun i j => ∑ k, M (i, k) (j, k)

@[simp] theorem ptrace_apply (M : Matrix (m × u) (n × u) R) (i j) :
    ptrace M i j = ∑ k, M (i, k) (j, k) := rfl

theorem ptrace_add (M N : Matrix (m × u) (n × u) R) :
    ptrace (M + N) = ptrace M + ptrace N := by
  ext i j; simp [ptrace, Finset.sum_add_distrib]

theorem ptrace_smul (c : R) (M : Matrix (m × u) (n × u) R) :
    ptrace (c • M) = c • ptrace M := by
  ext i j; simp [ptrace, Finset.mul_sum]

/-- **Vanishing-II, computationally.** Tracing out a product wire `u × v` is tracing out
`u` then `v`: `Tr_{u×v} = `nested sums. -/
theorem ptrace_prod (M : Matrix (m × (u × v)) (n × (u × v)) R) (i : m) (j : n) :
    ptrace M i j = ∑ a, ∑ b, M (i, (a, b)) (j, (a, b)) := by
  simp only [ptrace_apply]; rw [Fintype.sum_prod_type]

/-- **Compatibility with the full trace.** The full trace of a partial trace is the full
trace — the categorical "trace vanishes into the unit". -/
theorem trace_ptrace [Fintype m] (M : Matrix (m × u) (m × u) R) :
    (ptrace M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptrace_apply]
  rw [Fintype.sum_prod_type]

variable [DecidableEq u]

/-- The symmetry (swap) on `u ⊗ u`. -/
def swap : Matrix (u × u) (u × u) R :=
  fun p q => (if p.1 = q.2 then 1 else 0) * (if p.2 = q.1 then 1 else 0)

/-- **Yanking** — the characteristic trace law: tracing the swap gives the identity,
`Tr(σ) = id`. This ties the partial trace to the braiding, exactly as the JSV `trace_yank`
axiom demands. -/
theorem ptrace_swap : ptrace (swap : Matrix (u × u) (u × u) R) = 1 := by
  ext i j
  simp only [ptrace_apply, swap, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

end RelExist.PartialTrace
