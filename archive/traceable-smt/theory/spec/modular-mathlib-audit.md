# Modular self-relation — mathlib gap audit (handoff X, Stage 0)

What mathlib (pinned `v4.15.0`, see [`formal/lakefile`](../../lake)) provides versus what each later stage
of [the modular-frontier program](modular-frontier.md) needs. The point is to plan Stages 1–3
against reality. **Verdict: Stages 1–2 (finite-dimensional modular flow, modular Hamiltonian, KMS) are
fully achievable in-repo on mathlib as-is; Stage 3 (type III, non-inner flow, crossed products) has
essentially no mathlib support and is scope-only.**

## The table

| Need | Stage | Status | mathlib handle |
|---|---|---|---|
| `Matrix.exp` (= `NormedSpace.exp 𝕂` on `Matrix n n 𝔸`) | 1, 2 | **have** | `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` |
| `exp_add_of_commute`, `exp_neg`, `exp_zero`, `isUnit_exp` | 1 | **have** | same — the one-parameter group law and invertibility |
| `exp_conjTranspose : exp(Aᴴ) = (exp A)ᴴ` | 1 | **have** | same — gives unitarity of `e^{-itK}` for `K` self-adjoint |
| `exp_diagonal : exp(diagonal v) = diagonal (exp∘v)` | 1 | **have** | same — the scalar/maximally-mixed (D1) limit |
| Hermitian functional calculus on matrices (`cfc (f:ℝ→ℝ)`) | 1, 2 | **have** | `Mathlib/LinearAlgebra/Matrix/HermitianFunctionalCalculus.lean` — global instance `Matrix.IsHermitian.instContinuousFunctionalCalculus` (no L²-operator-norm `CStarAlgebra` instance needed) |
| Hermitian `log` and `exp`/`log` inverse laws | 1, 2 | **have** | `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog.lean` — `CFC.log`, `CFC.exp_log` (`exp(log ρ)=ρ` for `spectrum>0`), `CFC.log_exp`, `CFC.log_algebraMap` (`log` of a scalar matrix), `IsSelfAdjoint.log` |
| `exp_eq_normedSpace_exp` (CFC-exp = `NormedSpace.exp`) | 1, 2 | **have** | same file — bridges the spectral `log` to `Matrix.exp` |
| Spectral theorem for Hermitian matrices; `eigenvalues : n → ℝ` | 1, 2 | **have** | `Mathlib/LinearAlgebra/Matrix/Spectrum.lean` — `IsHermitian.spectral_theorem`, `eigenvalues_eq_spectrum_real` |
| `PosDef`/`PosSemidef`, eigenvalues positive, `IsHermitian` | 1, 2 | **have** | `Mathlib/LinearAlgebra/Matrix/PosDef.lean` — `PosDef.eigenvalues_pos`, `PosDef.isHermitian` |
| Density matrix / quantum state type | 1, 2 | **build-in-repo** | none in mathlib; model a faithful state as a `ρ.PosDef` with `trace ρ = 1`, or work generator-first with a self-adjoint `K` and Gibbs `ρ = e^{-βK}/Z` |
| KMS condition | 2 | **build-in-repo** | none; finite-dimensional KMS is a clean `exp`-identity to state and prove here |
| `CStarAlgebra`/`WStarAlgebra` abstract defs | 3 | **have (defs only)** | `Mathlib/Analysis/VonNeumannAlgebra/Basic.lean` — abstract `WStarAlgebra` + concrete double-commutant `VonNeumannAlgebra H`; *"major project ahead"* per its own docstring (no commutant theorem) |
| GNS construction | 3 | **out-of-reach-for-now** | none |
| Modular operator `Δ`, modular automorphism group (abstract / Tomita–Takesaki) | 3 | **out-of-reach-for-now** | none (`Modular*` in mathlib is number theory only) |
| KMS ⇔ modular (general), crossed product `M = N ⋊ ℝ`, flow of weights | 3 | **out-of-reach-for-now** | none |
| Type I/II/III classification, hyperfinite factor | 3 | **out-of-reach-for-now** | none |

## Consequences for the plan

- **Stage 1** is built on `Matrix.exp` + the Hermitian CFC. The cleanest finite-dimensional realization: take
  the modular Hamiltonian as a self-adjoint matrix `K` (recovered as `K = -CFC.log ρ`), and `ρ^{it} =
  e^{it·log ρ} = e^{-itK}` via `Matrix.exp ℂ`. The group law (`exp_add_of_commute`), invertibility
  (`exp_neg`), unitarity (`exp_conjTranspose`), and the maximally-mixed limit (`exp_diagonal` /
  `log_algebraMap` on a scalar matrix) are all direct. **No type III, no operator-norm `CStarAlgebra`
  instance, no eigenvalue bookkeeping is required** — the global Hermitian-CFC instance suffices.
- **Stage 2** (KMS for `ρ = e^{-βK}/Z`; energy `= spectrum K`) is a finite-dimensional identity on the same
  machinery. The *arrow* test is conceptual, not a mathlib gap: the modular flow is the unitary `Ad(e^{-itK})`
  (reversible), so it carries time's flow, not its arrow — to be reported against the spec-IX `genReal < 0`
  dissipator, which lives outside the modular (unitary) automorphism.
- **Stage 3** is genuinely blocked by mathlib: every ingredient (GNS, modular operator, crossed product, type
  classification) is absent, and the von Neumann algebra file itself flags the commutant theorem as unbuilt.
  This stage is therefore **scoping and build-order only** (`docs/spec/modular-frontier.md`), explicitly not a
  mechanization — consistent with the handoff's anti-goal of not claiming type III.

## Mathlib-PR note (deferred, per handoff)

Two eventual upstream contributions are visible but **gated, not submitted now**: (i) finite-dimensional KMS /
modular flow as a clean `Matrix.exp` development; (ii) the traced-SMC formalization. Both wait on finalizing
the in-repo core here and on the pending traced-SMC consolidation. **In-repo only for this handoff.**
