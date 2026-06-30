/-
# The mean-ergodic keystone — Conjecture R (the general lift of the converse)

`[open]`. This module carries the **one open step** of the converse direction
([`KnowingFromArrow`](KnowingFromArrow.lean), [`03.10-knowing-from-arrow.md`](../../docs/spec/03.10-knowing-from-arrow.md)).
On the genuine instance `partialDephase p` the converse is **proved** (`KnowingFromArrow`,
sorry-free, footprint `[propext, Classical.choice, Quot.sound]`): an arrow's orbit converges to
`dephase`, the knowing map `E`. This module states the lift of that fact to *every* contractive arrow.

> **Conjecture R (mean-ergodic recovery).** Let `T` be a linear, power-bounded map on a
> finite-dimensional matrix algebra, self-adjoint for the GNS inner product of a faithful invariant
> state, with **trivial peripheral spectrum** (modulus-1 eigenvalue only at `1`, no rotation). Then
> the orbit `Tⁿ` converges to a limit `E`, and `E` is an **idempotent conditional expectation onto
> the fixed subalgebra `Fix(T)`** — with the arrow's monovariant equal to the off-diagonal mass `E`
> annihilates.

**Proof route** (spec §4.3–4.4), two non-trivial steps:
1. **Mean-ergodic projection** — for a power-bounded `T` on a finite-dimensional space,
   `(1/N) Σ_{k<N} Tᵏ → P`, the projection onto `Fix(T)` along `range(1−T)` (finite-dim mean-ergodic
   theorem; mathlib's `LinearMap`/`ContinuousLinearMap` ergodic lemmas are the lever). Tie `P` to the
   Perron–Frobenius eigenprojection ([`PerronFrobenius`](PerronFrobenius.lean)) and the `P + N` split
   ([`SpectralDecay`](SpectralDecay.lean)).
2. **Trivial peripheral spectrum collapses the Cesàro limit to the power limit** (`lim Tⁿ = P`), and
   under GNS-self-adjointness `Fix(T)` is a `*`-subalgebra with `P` a conditional expectation onto it
   (the multiplicative-core / Lindblad-type argument).

**Gating.** This file is deliberately **not** imported by the `Scratch` aggregator, so the default
`lake build Scratch` (and `KnowingFromArrow`, which does not import it) stay sorry-free. It is built
only on explicit `lake build Scratch.MeanErgodic`, where the `sorry` below warns. Discharge the `sorry`
and move the import into `Scratch.lean` to fold the lift into the clean build.
-/
import Scratch.KnowingFromArrow

namespace RelExist.MeanErgodic

open RelExist.Decoherence RelExist.KnowingFromArrow
open Filter Topology Matrix

/-- **Conjecture R (mean-ergodic recovery)** — `[open]`, the general lift of the converse.

The hypothesis `hlim` packages the *dynamical* input the spectral conditions deliver (power-bounded +
trivial peripheral ⟹ the orbit has an entrywise limit `E`). The open content is everything the
converse claims about that limit: that `E` is an **idempotent conditional expectation onto the fixed
subalgebra** — `E∘E = E`, `T∘E = E`, and `E` fixes *exactly* the `T`-fixed points. The genuine
instance `T = partialDephase p`, `E = dephase` discharges all of this in
[`KnowingFromArrow`](KnowingFromArrow.lean); Conjecture R is its lift to every linear contractive
arrow with trivial peripheral spectrum.

Proof obligation: the two steps in the module header (mean-ergodic projection + multiplicative core).
Until discharged this carries `sorry` and is gated out of the default build. -/
theorem conjecture_R {A : Type} [Fintype A] [DecidableEq A]
    (T : Matrix A A ℝ →ₗ[ℝ] Matrix A A ℝ)
    (E : Matrix A A ℝ → Matrix A A ℝ)
    (hlim : ∀ M i j, Tendsto (fun n => ((⇑T)^[n] M) i j) atTop (𝓝 (E M i j))) :
    (∀ M, E (E M) = E M)             -- the recovered limit is idempotent (a projection)
      ∧ (∀ M, ⇑T (E M) = E M)        -- its range is fixed by T
      ∧ (∀ M, ⇑T M = M ↔ E M = M) := by  -- E fixes exactly Fix(T): a CE onto the fixed subalgebra
  sorry

end RelExist.MeanErgodic
