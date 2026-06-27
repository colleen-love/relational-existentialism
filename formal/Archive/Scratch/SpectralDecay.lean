/-
# The general spectral form of the conjecture — subdominant modes decay to the peripheral self

Conjecture 3.7.4 ([03.7](../../docs/spec/03.7-sparsity.md)) in its **general** form: *under iterated
co-directed feedback, only the eigenforms near the spectral radius self-sustain; the subdominant modes
decay.* This module mechanizes that **dynamical mechanism** in any normed ring, `sorry`-free.

Write the dynamics as `T = P + N`, splitting it into its **peripheral** part `P` (the spectral
projection onto the eigenforms at the spectral radius — idempotent, the *self-sustaining* part) and the
**subdominant** part `N` (everything strictly inside the spectral radius, `‖N‖ < 1`), with the two
orthogonal (`P·N = N·P = 0`). Then:

* `spectral_pow` — `Tⁿ = P + Nⁿ` for `n ≥ 1`: the iterates split exactly, the peripheral part fixed,
  the subdominant part carried to the `n`-th power;
* `spectral_decay` — **`Tⁿ → P`**: the subdominant part decays (`‖N‖ < 1 ⇒ Nⁿ → 0`), so iterating the
  feedback converges to the peripheral projection. *Only the peripheral eigenforms self-sustain; the
  rest decay.* This is the general spectral statement, for any such decomposition.

Combined with [`Peripheral.peripheral_sparse`](Peripheral.lean) (the peripheral set is sparse — `1/n`
density) this is Conjecture 3.7.4's content: **few modes self-sustain, the rest decay**. The peripheral
projection's *existence* is discharged at finite dimension by the idempotent `E = dephase`
([`Peripheral`](Peripheral.lean), the `N = 0` extreme); that an *arbitrary* unital CP `Φ_c` admits the
decomposition with a commutative peripheral subalgebra (the full Perron–Frobenius) stays the named
`[open]` (mathlib has no CP-map spectral theory). What is closed here is the **decay dynamics** in
general — the mechanism the conjecture is about.
-/
import Mathlib.Analysis.SpecificLimits.Normed

namespace RelExist.SpectralDecay

open Filter Topology

variable {R : Type*} [NormedRing R]

/-- **The iterates split.** With `P` idempotent and orthogonal to `N` (`P·N = N·P = 0`),
`(P + N)ⁿ = P + Nⁿ` for every `n ≥ 1`: the peripheral part stays fixed, the subdominant part is carried
to its `n`-th power (all cross terms vanish). -/
theorem spectral_pow (P N : R) (hP : P * P = P) (hPN : P * N = 0) (hNP : N * P = 0) :
    ∀ n, 1 ≤ n → (P + N) ^ n = P + N ^ n := by
  refine Nat.le_induction ?_ ?_
  · simp
  · intro n hn ih
    have hNnP : N ^ n * P = 0 := by
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn) with ⟨m, rfl⟩
      rw [pow_succ, mul_assoc, hNP, mul_zero]
    rw [pow_succ (P + N) n, ih, pow_succ N n, add_mul, mul_add, mul_add, hP, hPN, hNnP]
    abel

/-- **Subdominant modes decay to the peripheral self.** If the subdominant part is a strict contraction
(`‖N‖ < 1`), the iterated dynamics `Tⁿ = (P + N)ⁿ` converge to the peripheral projection `P`: only the
peripheral eigenforms self-sustain, the rest decay. The general spectral form of Conjecture 3.7.4's
"few modes self-sustain". -/
theorem spectral_decay (P N : R) (hP : P * P = P) (hPN : P * N = 0) (hNP : N * P = 0)
    (hN : ‖N‖ < 1) :
    Tendsto (fun n => (P + N) ^ n) atTop (𝓝 P) := by
  have hN0 : Tendsto (fun n => N ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hN
  have hlim : Tendsto (fun n => P + N ^ n) atTop (𝓝 (P + 0)) := hN0.const_add P
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (spectral_pow P N hP hPN hNP n hn).symm

/-- **The peripheral extreme** (the `E = dephase` case): a bare idempotent `P` (subdominant part `N =
0`) is already its own limit — `Pⁿ = P` for `n ≥ 1`. The conditional-expectation case, where the
decay is instantaneous. -/
theorem idempotent_pow (P : R) (hP : P * P = P) (n : ℕ) (hn : 1 ≤ n) : P ^ n = P := by
  have h := spectral_pow P 0 hP (by simp) (by simp) n hn
  rw [add_zero, zero_pow (show (n : ℕ) ≠ 0 by omega), add_zero] at h
  exact h

end RelExist.SpectralDecay
