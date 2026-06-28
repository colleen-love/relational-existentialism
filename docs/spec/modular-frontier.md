# The modular frontier — genuinely intrinsic time (handoff X, Stage 3)

> **Status:** scoping and build-order, **not a mechanization**. The finite-dimensional core (Stages 1–2) is
> built and `sorry`-free in [`formal/Scratch/ModularFlow.lean`](../../formal/Scratch/ModularFlow.lean); this
> page maps the deep end it deliberately stops short of. Paper one's headline is untouched — this is
> foundation work for the sequels. **In-repo only; no mathlib PRs** (those are gated on finalizing here and on
> the pending traced-SMC consolidation).

## Where Stages 1–2 land, and why they are not yet "intrinsic"

`ModularFlow.lean` builds, for `Mₙ(ℂ)` with a faithful state `ρ`:

- the modular flow `σ_t(M) = ρ^{it} M ρ^{-it}` as a one-parameter group of \*-automorphisms;
- the modular Hamiltonian `K = -log ρ` as its self-adjoint Stone generator (energy = `spectrum(K)`);
- `D1 : σ = Tr` recovered as the maximally-mixed (infinite-temperature, *timeless*) limit;
- the finite-dimensional KMS/Gibbs identity (`modularEnergy = β·E + log Z`);
- the arrow test: the flow is unitary, hence **reversible** — it is time's *flow*, not its *arrow*.

**The limitation that defines the frontier.** In finite dimensions the modular flow is always **inner**:
`ρ^{it}` lives *inside* the algebra `Mₙ(ℂ)`, so `K` is "only" a Hamiltonian and time is not yet *intrinsic*
— it is a choice of generator, not forced by the algebra. The trace `Tr` exists (type I). Time becomes
intrinsic exactly when the modular flow is **non-inner**, and that forces:

- **type III** (no trace at all), and
- the **continuous decomposition** `M = N ⋊_θ ℝ`, where `N` is a type II∞ factor carrying the trace and the
  modular flow `θ` is exactly what *removes* the trace (the flow of weights).

This is the real destination — Connes' classification — and the real cost: a multi-year operator-algebra
program, downstream of the traced-SMC work.

## Precise statements wanted (the targets, in order of depth)

1. **GNS construction.** From a state `φ` on a C\*-algebra `A`, the Hilbert space `H_φ`, cyclic vector `Ω`,
   and representation `π_φ`. *(mathlib: absent. Prerequisite for everything below.)*
2. **The modular operator `Δ`.** The Tomita operator `S = J Δ^{1/2}` from `S(aΩ) = a^*Ω`; positivity and
   self-adjointness of `Δ`; the modular conjugation `J`. *(absent.)*
3. **Tomita–Takesaki.** `Δ^{it} π(A) Δ^{-it} = π(A)` and `J π(A) J = π(A)'` — the modular automorphism group
   `σ_t = Ad(Δ^{it})` and the commutant theorem. *(absent.)*
4. **KMS ⇔ modular.** `φ` satisfies the `β = 1` KMS condition for `σ_t` (general, infinite-dimensional;
   Stage 2 proves only the finite-dimensional spectral shadow). *(absent.)*
5. **Non-innerness / type III.** A factor on which `σ_t` is *not* inner; the type III classification
   (`III_λ`, `λ ∈ [0,1]`); Connes' `S`-invariant. *(absent.)*
6. **Continuous decomposition.** `M = N ⋊_θ ℝ` with `N` type II∞ and `θ` the trace-scaling flow of weights —
   the structural backbone where "time removes the trace." *(absent.)*

## Minimal infinite example worth targeting first

Do **not** start at general type III. The tractable first target is the **hyperfinite II₁ factor `R`** and the
**flow of weights**: `R` is the inductive limit of the matrix algebras this repo already handles, so the
finite `ModularFlow` development is its natural finite truncation. Concretely, the first non-trivial milestone
is the **modular operator of a non-tracial state on `R`** (e.g. an infinite tensor product of the
`quarterMul`-style states), where `σ_t` is genuinely non-inner — the smallest place intrinsic time appears.
`III_1` (the type of physical thermal states) is the eventual goal, not the entry point.

## mathlib build-order implied by the audit

From [`docs/notes/modular-mathlib-audit.md`](../notes/modular-mathlib-audit.md), the dependency chain
mathlib needs (each gating the next), none of which currently exists:

1. **States and GNS** on C\*-algebras (positive linear functionals → `H_φ`, `π_φ`, `Ω`). *Foundational; unblocks
   everything.*
2. **Standard form / the modular operator** for a von Neumann algebra in standard form (`Δ`, `J`).
3. **Tomita–Takesaki** (`σ_t`, commutant theorem) — the headline theorem the `VonNeumannAlgebra` file already
   flags as "a major project ahead."
4. **KMS theory** and the `KMS ⇔ modular` equivalence.
5. **Crossed products `M ⋊ G`** and the **flow of weights**; type classification.

Realistically (1)–(2) are the achievable next contributions; (3)–(5) are long-horizon.

## An abstract interface (optional scaffold)

So the finite work already points at the infinite goal, the finite `ModularFlow` could be re-exposed as an
instance of an abstract typeclass — *"a von Neumann algebra with a modular automorphism group"* — roughly:

```
class ModularStructure (M : Type*) [/- vN algebra structure -/] where
  modularFlow : ℝ → M ≃⋆ₐ[ℂ] M          -- a one-parameter group of *-automorphisms
  flow_add    : ∀ s t, modularFlow (s + t) = (modularFlow s).trans (modularFlow t)
  kms         : /- the β = 1 KMS condition for the defining state -/
```

`ModularFlow.lean` (`modularFlow_add`, `modularFlow_mul`, `modularFlow_star`, `gibbs_kms`) is exactly a
finite, inner, type I model of such a class; the type III program is the search for *non-inner* instances.
Building the class is optional and only worthwhile once GNS (step 1) lands — until then it would have a single
finite instance and no leverage. **Recorded as the shape to grow into, not built now.**

## Outcomes (honest)

- **Core delivered** (Stages 1–2): `σ = Tr` generalized to `σ = modularFlow ρ`; the trace is its timeless
  limit; energy is the modular Hamiltonian; thermal time recovered finite-dimensionally.
- **Arrow boundary found** (Stage 2): the modular (reversible) flow does **not** yield the arrow — the
  inherited thermal-time open problem, now located precisely. Real, publishable.
- **Frontier scoped** (this page): a credible map and mathlib build-order for type III, **without** claiming a
  mechanization that is not yet possible.
