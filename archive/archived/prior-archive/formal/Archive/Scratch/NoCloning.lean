/-
# No-cloning, concretely — Layer 4, the physics domain

The physics fragment (quantum) is **compact closed, not cartesian**: states cannot be
copied. [`Scratch.Compact`](Compact.lean) gives this categorically (`no_cloning`); here
is the concrete linear-algebra reason, the heart of the no-cloning theorem.

Cloning sends a state `ψ` to `ψ ⊗ ψ`. On the one-dimensional space `ℝ`, under
`ℝ ⊗ ℝ ≅ ℝ` this is `x ↦ x · x = x²` — and that map is **not linear**. So no linear
(hence no unitary / physical) process clones: the obstruction is exactly that copying is
quadratic while quantum evolution is linear. This is the 1-dimensional shadow of the full
no-cloning theorem, and it is what distinguishes the quantum target `FdHilb`/`FdVect`
from the cartesian (social) domains where copying is free.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic

namespace RelExist.NoCloning

/-- **No-cloning (1-dimensional form).** There is no linear map realizing the clone map
`x ↦ x · x` (`≅ x ↦ x ⊗ x`): copying is quadratic, linear evolution is not. -/
theorem no_linear_clone : ¬ ∃ c : ℝ →ₗ[ℝ] ℝ, ∀ x : ℝ, c x = x * x := by
  rintro ⟨c, hc⟩
  -- linearity: c 2 = c (2 • 1) = 2 • c 1 = 2 * c 1
  have key : c 2 = 2 * c 1 := by
    have h : c ((2 : ℝ) • (1 : ℝ)) = (2 : ℝ) • c 1 := map_smul c 2 1
    simpa using h
  -- but the clone law gives c 2 = 2·2 = 4 and c 1 = 1·1 = 1, so 4 = 2
  rw [hc 2, hc 1] at key
  norm_num at key

end RelExist.NoCloning
