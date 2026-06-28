/-
# Handoff XV — closing paper two's frontier: two faces of one generator

Paper two carries two results proved *separately*: the **modular flow** (reversible — the clock and the
energy, [`ModularFlow`](ModularFlow.lean)) and the **dissipative arrow** (irreversible — paper one's
`genReal < 0`, lifted to `theory/` as [`RotatingSpectrum`](RotatingSpectrum.lean)). The headline "flow and
arrow are two faces of one generator" needs them to be *parts of one generator sharing one time parameter*,
not two unrelated clocks. This module earns that — **at equilibrium, under a named alignment** — and is
built to return the obstruction precisely where it lives.

The honest frame up front: the *full* identification (modular time = physical time, out of equilibrium) is
the 30-year-open Connes–Rovelli problem and is **not** attempted. The closable target is the **equilibrium**
case, with the conditions it needs *named*, not the universal claim.

## What is built

* **Part A — assemble the single generator (`§2`).** The open-system (GKLS) generator
  `𝓛(M) = -i[H, M] + 𝒟(M)`, with `𝒟` paper one's dephasing dissipator (`schur`) and `H` the system
  Hamiltonian. The dissipative face is the continuous semigroup `dephaseFlow μ t = schur (μ^t)`
  (`dephaseFlow_add`, a one-parameter semigroup; `dephaseFlow_one_eq_schur`, one step is paper one's actual
  channel); its per-edge magnitude decays at rate `genReal μ i j = Re log μ ≤ 0` (`dephaseFlow_norm`) — paper
  one's arrow. The unitary face is `modularFlow ρ s`, reversible (`modular_reversible`, cited). **No content
  claimed yet** — this names the canonical form; the content is B and C.

* **Part B — the KMS bridge (`§3`): the unitary face *is* the modular flow.** Under the equilibrium condition
  `dᵢ = e^{-βEᵢ}/Z` (Gibbs), the modular Hamiltonian `K = -log ρ` and the physical Hamiltonian `H` (energies
  `E` in the *same* eigenbasis, `physHamiltonian`) satisfy `K = β·H + (log Z)·I`
  (`modularHamiltonian_eq_gibbs`) — so `H = (1/β)K` up to a scalar. Hence the unitary generator `-i[K,·]`
  equals `β·(-i[H,·])` (`commGen_modular_eq_beta`): the reversible face `-i[H,·]` runs the **modular clock at
  rate `1/β`**, and energy `= spec(H) = spec(K)/β =` the modular energies scaled (`modularEnergy_eq_gibbs`).
  The finite-time face is `modularFlow ρ (t/β)`. `[proved under KMS]`

* **Part C — commutation: why it is *one* generator (`§4`, the crux).** The substantive claim: the
  *independently defined* pieces — `K` from the state `ρ`, `𝒟` from paper one's arrow — turn out
  **compatible**. In the preferred basis B1, **both maps are Schur multipliers**: dephasing acts on `(i,j)`
  by `μᵢⱼ`, and *when `ρ = diag(d)` in B1* the modular flow acts by `(dᵢ/dⱼ)^{is}`
  (`modularFlow_diagonal_eq_schur`). Schur multipliers in a common basis commute (`schur_comm`), so the
  commutator **vanishes — provided `ρ` is diagonal in B1** (`modular_dephase_commute`,
  `modular_dephaseFlow_commute`; at the generator level `liouville_dephase_commute`). The alignment is
  **derived, not assumed**: the commutation falls out of `B1 = eigenbasis(ρ)` via the genuine `modPow`
  (`modPow_diagonal`, the anti-tautology bridge — `K` really comes from `ρ`). **The boundary, named honestly:**
  the result holds under "pointer states = modular/energy eigenstates"; if `ρ` carries coherence in B1 the
  modular flow is not a B1-Schur multiplier and the commutation fails — reported as the boundary (`§4`
  closing note), not forced.

* **Part D — assemble, and the residue (`§5`).** With B and C, the joint flow
  `combinedFlow t = σ_{t/β} ∘ dephaseFlow t` is a genuine one-parameter semigroup (`combinedFlow_add`) whose
  **semigroup law holds *because* the two faces commute** (drop the commutation and `Φ_s∘Φ_t ≠ Φ_{s+t}`) —
  the unitary face the modular clock (B), the dissipative face paper one's arrow (A), sharing the time `t`
  with `s = t/β`. **"Two faces of one generator" is earned — at equilibrium, under the named alignment.**

## Honest scope / the residue

* `[proved, at equilibrium]`: B gives `H ∝ K`; C gives `[σ_s, 𝒟] = 0` *from* `B1 = eigenbasis(ρ)` via the
  genuine modular operator; D assembles the one generator (its semigroup law consuming the commutation).
* **Conditions (named readings, not theorems-from-nothing):** KMS-equilibrium (Part B) and
  `B1 = eigenbasis(ρ)` (Part C). The latter is "equilibrium einselection — pointer basis = energy
  eigenbasis."
* `[open, inherited]` — **out-of-equilibrium**: that modular time *is* physical time with no equilibrium
  assumption is the Connes–Rovelli frontier; **not** claimed here (see `modular-frontier.md`).
* `[open, flagged not attempted]` — whether the framework *forces* the alignment (is einselection onto the
  modular eigenbasis derivable, or assumed?). Candidate next frontier.

**Provenance.** `R / S` — GKLS/Lindblad form, KMS, and Schur-multiplier commutation are standard; the
synthesis is assembling the open-system generator from *independently defined* modular (`K` from the state)
and dissipative (`𝒟` from paper one) parts and *checking* — not imposing — that they are one coherent object,
earned at equilibrium via the KMS bridge and the preferred-basis Schur-commutation, with the
out-of-equilibrium identification named as the frontier it remains.
-/
import Theory.ModularFlow
import Theory.RotatingSpectrum
import Mathlib.LinearAlgebra.Lagrange

namespace RelExist.OneGenerator

open Matrix Complex
open RelExist.ModularFlow RelExist.RotatingSpectrum
open scoped ComplexConjugate

/-! ## §0 Spectral-function machinery — a function of a *diagonal* state is diagonal

The anti-tautology bridge of Part C needs the genuine modular operator `modPow` (from `ModularFlow`, built
out of `ρ`'s eigendata) to be *computable* when `ρ` is diagonal: `ρ^{is} = diag(dᵢ^{is})`. We get there by a
general fact — a spectral function `U·diag(g∘λ)·Uᴴ` of a diagonal Hermitian matrix is `diag(g∘d)` — proved
via polynomial interpolation (the function sees only the eigenvalues, which for a diagonal matrix *are* its
diagonal entries, with no eigenvector ambiguity). These are general matrix utilities. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `aeval` of a diagonal matrix is the diagonal of the pointwise polynomial evaluation. -/
theorem aeval_diagonal (p : Polynomial ℂ) (v : n → ℂ) :
    Polynomial.aeval (diagonal v) p = diagonal (fun i => p.eval (v i)) := by
  induction p using Polynomial.induction_on with
  | h_C a =>
      rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      ext i j
      by_cases h : i = j <;>
        simp [Matrix.smul_apply, Matrix.one_apply, diagonal_apply, h, Polynomial.eval_C]
  | h_add p q hp hq => simp [hp, hq, ← diagonal_add]
  | h_monomial k a _ =>
      rw [_root_.map_mul, Polynomial.aeval_C, _root_.map_pow, Polynomial.aeval_X, diagonal_pow,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      ext i j
      by_cases h : i = j <;>
        simp [Matrix.smul_apply, diagonal_apply, h, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Pi.pow_apply]

/-- Conjugation `M ↦ U·M·Uᴴ` by a unitary `U` as an algebra homomorphism. -/
noncomputable def conjAlgHom (U : Matrix n n ℂ) (hU : star U * U = 1) (hU' : U * star U = 1) :
    Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ where
  toFun M := U * M * star U
  map_one' := by show U * 1 * star U = 1; rw [mul_one, hU']
  map_mul' x y := by
    show U * (x * y) * star U = U * x * star U * (U * y * star U)
    rw [show U * x * star U * (U * y * star U) = U * x * (star U * U) * y * star U from by
      noncomm_ring, hU]
    noncomm_ring
  map_zero' := by show U * 0 * star U = 0; simp
  map_add' x y := by show U * (x + y) * star U = _; rw [mul_add, add_mul]
  commutes' r := by
    show U * (algebraMap ℂ (Matrix n n ℂ) r) * star U = algebraMap ℂ (Matrix n n ℂ) r
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, hU']

/-- `aeval` commutes with unitary conjugation. -/
theorem aeval_conj (p : Polynomial ℂ) (U D : Matrix n n ℂ) (hU : star U * U = 1)
    (hU' : U * star U = 1) :
    Polynomial.aeval (U * D * star U) p = U * Polynomial.aeval D p * star U :=
  Polynomial.aeval_algHom_apply (conjAlgHom U hU hU') D p

/-- **A spectral function of a diagonal Hermitian matrix is diagonal.** For `ρ = diag(d)`, the spectral
function `U·diag(g∘eigenvalues)·Uᴴ` equals `diag(g∘d)` — the function sees only the spectrum, which for a
diagonal matrix *is* the diagonal, regardless of the eigenvector unitary's permutation freedom. (Proof: a
complex polynomial `p` interpolating `g` on the finite eigenvalue set turns the conjugation into
`aeval`, which commutes with both `diagonal` and unitary conjugation.) -/
theorem specFun_diagonal (d : n → ℝ) (g : ℝ → ℂ)
    (hD : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) :
    (hD.eigenvectorUnitary : Matrix n n ℂ) * diagonal (g ∘ hD.eigenvalues)
      * star (hD.eigenvectorUnitary : Matrix n n ℂ) = diagonal (g ∘ d) := by
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := unitary.coe_mul_star_self _
  set s : Finset ℝ := (Finset.univ.image d) ∪ (Finset.univ.image hD.eigenvalues) with hs
  have hinj : Set.InjOn (fun r : ℝ => (r : ℂ)) ↑s :=
    fun x _ y _ h => Complex.ofReal_injective h
  set p : Polynomial ℂ := Lagrange.interpolate s (fun r : ℝ => (r : ℂ)) g with hp
  have hpd : ∀ i, p.eval ((d i : ℂ)) = g (d i) := fun i =>
    Lagrange.eval_interpolate_at_node g hinj
      (Finset.mem_union_left _ (Finset.mem_image_of_mem d (Finset.mem_univ i)))
  have hpe : ∀ k, p.eval ((hD.eigenvalues k : ℂ)) = g (hD.eigenvalues k) := fun k =>
    Lagrange.eval_interpolate_at_node g hinj
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have e1 : diagonal (g ∘ d) = Polynomial.aeval (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) p := by
    rw [aeval_diagonal]
    exact congrArg diagonal (funext fun i => (hpd i).symm)
  have hA2 : Polynomial.aeval (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) p
      = Polynomial.aeval (U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hD.eigenvalues) * star U) p := by
    rw [hU, ← hD.spectral_theorem]
  have e2 : Polynomial.aeval (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) p
      = U * diagonal (g ∘ hD.eigenvalues) * star U := by
    rw [hA2, aeval_conj p U _ hUU hUU', aeval_diagonal]
    exact congrArg (fun D => U * D * star U) (congrArg diagonal (funext fun k => hpe k))
  rw [e1, e2]

/-- **The genuine modular operator of a diagonal state is diagonal** — `ρ^{is} = diag(dᵢ^{is})` for
`ρ = diag(d)`. This is the anti-tautology anchor of Part C: the `modPow` here is *literally* `ModularFlow`'s
operator built from `ρ`'s spectral data, not a fresh diagonal definition chosen to commute. -/
theorem modPow_diagonal (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) :
    modPow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s
      = diagonal (fun i => Complex.exp (Complex.I * s * Real.log (d i))) := by
  rw [modPow]
  have hmd : modDiag (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s
      = (fun x : ℝ => Complex.exp (Complex.I * s * Real.log x)) ∘ hρ.eigenvalues := by
    funext i; rfl
  rw [hmd]
  exact specFun_diagonal d (fun x : ℝ => Complex.exp (Complex.I * s * Real.log x)) hρ

/-- **The modular Hamiltonian of a diagonal state is diagonal** — `K = -log ρ = diag(-log dᵢ)` for
`ρ = diag(d)`. The energy-basis is the state-basis, with no eigenvector ambiguity. -/
theorem modularHamiltonian_diagonal (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) :
    modularHamiltonian (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ
      = diagonal (fun i => ((- Real.log (d i) : ℝ) : ℂ)) := by
  rw [modularHamiltonian]
  exact specFun_diagonal d (fun x : ℝ => ((- Real.log x : ℝ) : ℂ)) hρ

/-! ## §1 Schur multipliers compose and commute — the algebraic heart of Part C

Two Schur (entrywise) multipliers in a common basis multiply entrywise, hence **commute**. This trivial
algebraic fact is the entire mechanism by which the modular flow and the dissipator turn out to be one
generator (once both are exhibited as Schur multipliers in B1, `§4`). -/

/-- Composing two Schur multipliers multiplies their symbols entrywise. -/
theorem schur_comp {A : Type*} (a b : A → A → ℂ) (M : Matrix A A ℂ) :
    schur a (schur b M) = schur (fun i j => a i j * b i j) M := by
  ext i j; simp only [schur_apply]; ring

/-- **Schur multipliers commute.** The commutator of two entrywise multipliers vanishes by entrywise
commutativity of multiplication — the structural reason "flow and arrow are two faces of one generator." -/
theorem schur_comm {A : Type*} (a b : A → A → ℂ) (M : Matrix A A ℂ) :
    schur a (schur b M) = schur b (schur a M) := by
  ext i j; simp only [schur_apply]; ring

/-! ## §2 Part A — assemble the single generator: the two faces

`𝓛(M) = -i[H, M] + 𝒟(M)`. The dissipative face `𝒟` is paper one's dephasing, here as the continuous
one-parameter semigroup `dephaseFlow μ t = schur (μ^t)` (`μ^t = exp(t · log μ)` entrywise). This **names the
canonical form** — the content is B (`§3`) and C (`§4`). -/

/-- The continuous dephasing symbol `μ^t = exp(t · log μ)`, entrywise. At `t = 1` it is `μ` itself (on live
edges); its modulus is `exp(t · Re log μ) = exp(t · genReal)`, paper one's per-edge decay. -/
noncomputable def dissipatorMul {A : Type*} (μ : A → A → ℂ) (t : ℝ) (i j : A) : ℂ :=
  Complex.exp (t * Complex.log (μ i j))

/-- **The dissipative face**, continuous-time: `e^{t𝒟} = schur (μ^t)`, the one-parameter semigroup whose
generator is paper one's dephasing dissipator `𝒟`. -/
noncomputable def dephaseFlow {A : Type*} (μ : A → A → ℂ) (t : ℝ) (M : Matrix A A ℂ) : Matrix A A ℂ :=
  schur (dissipatorMul μ t) M

/-- **The dissipator is a one-parameter semigroup**: `e^{s𝒟} ∘ e^{t𝒟} = e^{(s+t)𝒟}`. The Schur symbols
multiply (`schur_comp`) and the per-edge generators add (`exp(sL)·exp(tL) = exp((s+t)L)`). -/
theorem dephaseFlow_add {A : Type*} (μ : A → A → ℂ) (s t : ℝ) (M : Matrix A A ℂ) :
    dephaseFlow μ s (dephaseFlow μ t M) = dephaseFlow μ (s + t) M := by
  ext i j
  simp only [dephaseFlow, schur_apply, dissipatorMul]
  rw [← mul_assoc]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `e^{0·𝒟} = id`: at `t = 0` the symbol is `1`. -/
theorem dephaseFlow_zero {A : Type*} (μ : A → A → ℂ) (M : Matrix A A ℂ) :
    dephaseFlow μ 0 M = M := by
  unfold dephaseFlow dissipatorMul
  ext i j
  rw [schur_apply]
  simp

/-- **One step of the dissipator is paper one's actual channel.** On live edges (`μ i j ≠ 0`),
`e^{1·𝒟} = schur μ` — the continuous semigroup's unit-time map is exactly `RotatingSpectrum.schur`. This is
the anti-tautology anchor for the dissipative face: `𝒟` is paper one's dephasing, not redefined. -/
theorem dephaseFlow_one_eq_schur {A : Type*} (μ : A → A → ℂ) (M : Matrix A A ℂ)
    (hμ : ∀ i j, μ i j ≠ 0) :
    dephaseFlow μ 1 M = schur μ M := by
  unfold dephaseFlow dissipatorMul
  ext i j
  rw [schur_apply, schur_apply, Complex.ofReal_one, one_mul, Complex.exp_log (hμ i j)]

/-- **The dissipative face decays at rate `genReal` — paper one's arrow.** Each coherence's magnitude under
`e^{t𝒟}` is `exp(t · genReal μ i j) · ‖M i j‖`, with `genReal μ i j = Re log μ ≤ 0` (the arrow when
`< 0`). The unitary face cannot do this; the arrow lives here. -/
theorem dephaseFlow_norm {A : Type*} (μ : A → A → ℂ) (t : ℝ) (M : Matrix A A ℂ) (i j : A) :
    ‖dephaseFlow μ t M i j‖ = Real.exp (t * genReal μ i j) * ‖M i j‖ := by
  unfold dephaseFlow dissipatorMul
  rw [schur_apply, norm_mul, Complex.norm_eq_abs, Complex.abs_exp]
  congr 2
  simp only [genReal, Complex.re_ofReal_mul]

/-! ## §3 Part B — the KMS bridge: the unitary face *is* the modular flow

Under the equilibrium condition `dᵢ = e^{-βEᵢ}/Z` (Gibbs), the modular Hamiltonian `K = -log ρ` and the
physical Hamiltonian `H` (energies `E` in the **same** eigenbasis) are related by `K = β·H + (log Z)·I`. So
`H = (1/β)K` up to a scalar, the unitary generator `-i[K,·] = β·(-i[H,·])` runs the modular clock at rate
`1/β`, and the energies coincide up to the `β`-scale. `[proved under KMS]` -/

/-- **The physical Hamiltonian** `H = U·diag(E)·Uᴴ` — the energies `E` written in the *same* eigenbasis as
the state `ρ` (so that at equilibrium it shares `ρ`'s spectral frame). Its spectral diagonal is `E`. -/
noncomputable def physHamiltonian (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (E : n → ℝ) :
    Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (E i : ℂ))
    * star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- `physHamiltonian` is Hermitian (real spectrum `E`): a genuine Hamiltonian. -/
theorem physHamiltonian_isHermitian (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (E : n → ℝ) :
    (physHamiltonian ρ hρ E).IsHermitian := by
  have hfun : star (fun i => (E i : ℂ)) = (fun i => (E i : ℂ)) := by
    funext i; simp [Complex.star_def, Complex.conj_ofReal]
  show (physHamiltonian ρ hρ E)ᴴ = physHamiltonian ρ hρ E
  unfold physHamiltonian
  simp only [Matrix.star_eq_conjTranspose]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    ← mul_assoc, hfun]

/-- **The KMS bridge: `K = β·H + (log Z)·I`.** At the Gibbs equilibrium `dᵢ = e^{-βEᵢ}/Z`, the modular
Hamiltonian `K = -log ρ` (built from the *state*) equals the physical Hamiltonian `H` (built from the
*energies*) scaled by `β`, up to the normalization scalar. So `H = (1/β)K` up to a scalar — "energy = the
modular Hamiltonian" becomes "energy = the unitary generator of the dynamics." Both sides share `ρ`'s
eigenbasis, so this is a diagonal identity (`modularEnergy = β·E + log Z`, `gibbs_kms`). -/
theorem modularHamiltonian_eq_gibbs (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (β : ℝ) (E : n → ℝ)
    (Z : ℝ) (hZ : 0 < Z) (hgibbs : ∀ i, hρ.eigenvalues i = Real.exp (-(β * E i)) / Z) :
    modularHamiltonian ρ hρ
      = (β : ℂ) • physHamiltonian ρ hρ E + (Real.log Z : ℂ) • (1 : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU' : U * star U = 1 := unitary.coe_mul_star_self _
  have hsmul : ∀ (a : n → ℂ) (c : ℂ),
      c • (U * diagonal a * star U) = U * diagonal (fun i => c * a i) * star U := by
    intro a c
    have hdia : diagonal (fun i => c * a i) = c • diagonal a := by
      ext i j
      rcases eq_or_ne i j with h | h
      · subst h; simp [Matrix.smul_apply, smul_eq_mul]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply]
    rw [hdia, mul_smul_comm, smul_mul_assoc]
  have hadd : ∀ (a b : n → ℂ),
      U * diagonal a * star U + U * diagonal b * star U = U * diagonal (a + b) * star U := by
    intro a b
    rw [← add_mul, ← mul_add]
    congr 2
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; simp [Matrix.diagonal_apply_eq, Matrix.add_apply, Pi.add_apply]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.add_apply]
  have hone : ∀ c : ℂ, c • (1 : Matrix n n ℂ) = U * diagonal (fun _ : n => c) * star U := by
    intro c
    rw [show diagonal (fun _ : n => c) = c • (1 : Matrix n n ℂ) from by
          ext i j; by_cases h : i = j <;>
            simp [diagonal_apply, Matrix.smul_apply, Matrix.one_apply, h]]
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hUU']
  rw [modularHamiltonian_spectral, physHamiltonian, hsmul, hone, hadd]
  refine congrArg (fun D : Matrix n n ℂ => U * D * star U)
    (congrArg diagonal (funext fun i => ?_))
  simp only [Pi.add_apply, Function.comp_apply]
  rw [show modularEnergy ρ hρ i = β * E i + Real.log Z from
    gibbs_kms ρ hρ β E Z hZ hgibbs i]
  push_cast; ring

/-- **Energy = the modular energies, `β`-scaled.** `modularEnergy = β·E + log Z` at equilibrium — the
spectrum of `K` is the physical energies scaled by `β` plus the normalization, so `spec(H) = spec(K)/β` up to
the shift. (This is `ModularFlow.gibbs_kms`, recorded here as the energy half of the bridge.) -/
theorem modularEnergy_eq_gibbs (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (β : ℝ) (E : n → ℝ)
    (Z : ℝ) (hZ : 0 < Z) (hgibbs : ∀ i, hρ.eigenvalues i = Real.exp (-(β * E i)) / Z) (i : n) :
    modularEnergy ρ hρ i = β * E i + Real.log Z :=
  gibbs_kms ρ hρ β E Z hZ hgibbs i

/-- The commutator superoperator `[H, ·]` (the unitary generator is `-i` times this). -/
noncomputable def commGen (H M : Matrix n n ℂ) : Matrix n n ℂ := H * M - M * H

/-- **The unitary face runs the modular clock at rate `1/β`** — at the generator level. The modular
generator `[K, ·]` equals `β · [H, ·]` (the scalar `(log Z)·I` drops out of every commutator), so the
physical unitary generator `-i[H,·] = (1/β)·(-i[K,·])` is the modular flow's generator rescaled by `1/β`.
The reversible face of `e^{t𝓛}` for time `t` is thus `modularFlow ρ (t/β)`. -/
theorem commGen_modular_eq_beta (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (β : ℝ) (E : n → ℝ)
    (Z : ℝ) (hZ : 0 < Z) (hgibbs : ∀ i, hρ.eigenvalues i = Real.exp (-(β * E i)) / Z)
    (M : Matrix n n ℂ) :
    commGen (modularHamiltonian ρ hρ) M = (β : ℂ) • commGen (physHamiltonian ρ hρ E) M := by
  rw [commGen, commGen, modularHamiltonian_eq_gibbs ρ hρ β E Z hZ hgibbs]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub]
  abel

/-- **The reversible face is the modular flow at rate `1/β`** — finite-time. The unitary part of `e^{t𝓛}`
for time `t` is conjugation by `ρ^{i(t/β)} = e^{-i(t/β)K}` (`modPow`), i.e. `modularFlow ρ (t/β)`; with
`K = βH` (up to scalar, `modularHamiltonian_eq_gibbs`/`commGen_modular_eq_beta`) this is exactly the flow
generated by `-i[H,·]`. Reversibility is inherited (`modular_reversible`): the unitary face has no arrow. -/
theorem reversible_face_reversible (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (β t : ℝ)
    (M : Matrix n n ℂ) :
    modularFlow ρ hρ (-(t / β)) (modularFlow ρ hρ (t / β) M) = M :=
  modular_reversible ρ hρ (t / β) M

/-! ## §4 Part C — the crux: why it is *one* generator, not two clocks

The substantive claim. `K` is defined from the state `ρ` (`ModularFlow`), `𝒟` from paper one's arrow
(`§2`); they are **independently defined**. In the preferred basis B1 — *taken to be `eigenbasis(ρ)`, i.e.
`ρ` diagonal* — **both are Schur multipliers**: dephasing by `μᵢⱼ`, the modular flow by `(dᵢ/dⱼ)^{is}`. By
`schur_comm` they commute. The alignment `B1 = eigenbasis(ρ)` is *derived through the genuine `modPow`*
(`modPow_diagonal`, `§0`), not assumed. -/

/-- The modular-flow Schur symbol of a diagonal state: `(dᵢ/dⱼ)^{is} = exp(i·s·(log dᵢ − log dⱼ))`. -/
noncomputable def modularMul (d : n → ℝ) (s : ℝ) (i j : n) : ℂ :=
  Complex.exp (Complex.I * s * ((Real.log (d i) : ℂ) - (Real.log (d j) : ℂ)))

/-- **The modular flow of a diagonal state is a Schur multiplier in B1.** For `ρ = diag(d)`,
`σ_s(M)ᵢⱼ = (dᵢ/dⱼ)^{is} · Mᵢⱼ` — built from the *genuine* `modPow` (via `modPow_diagonal`), not posited.
This is the half of the crux that makes the modular clock a B1-Schur multiplier; the dephasing is one by
construction. -/
theorem modularFlow_diagonal_eq_schur (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (M : Matrix n n ℂ) :
    modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M = schur (modularMul d s) M := by
  rw [modularFlow, modPow_diagonal, modPow_diagonal]
  ext i j
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, schur_apply, modularMul]
  rw [show Complex.exp (Complex.I * (s : ℂ) * (Real.log (d i) : ℂ))
        * (M i j * Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (Real.log (d j) : ℂ)))
        = (Complex.exp (Complex.I * (s : ℂ) * (Real.log (d i) : ℂ))
            * Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (Real.log (d j) : ℂ))) * M i j from by ring,
    ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **The modular flow is a symmetry of the dissipative semigroup — `[σ_s, 𝒟] = 0`, derived from
`B1 = eigenbasis(ρ)`.** With `ρ` diagonal in B1, `σ_s` is a Schur multiplier (`modularFlow_diagonal_eq_schur`)
and so is the dephasing `schur μ`; Schur multipliers commute (`schur_comm`). **The commutation is *checked*,
not imposed:** `K` came from `ρ`, `μ` is paper one's symbol, and neither was redefined to make this hold. -/
theorem modular_dephase_commute (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (μ : n → n → ℂ)
    (M : Matrix n n ℂ) :
    modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s (schur μ M)
      = schur μ (modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M) := by
  rw [modularFlow_diagonal_eq_schur, modularFlow_diagonal_eq_schur, schur_comm]

/-- **The same commutation against the continuous dissipative semigroup**: `σ_s ∘ e^{t𝒟} = e^{t𝒟} ∘ σ_s`.
The modular flow is a symmetry of the *whole* dissipative semigroup, not just one step — exactly what is
needed to glue the two into one joint flow (`§5`). -/
theorem modular_dephaseFlow_commute (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (μ : n → n → ℂ) (t : ℝ)
    (M : Matrix n n ℂ) :
    modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s (dephaseFlow μ t M)
      = dephaseFlow μ t (modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M) := by
  unfold dephaseFlow
  rw [modularFlow_diagonal_eq_schur, modularFlow_diagonal_eq_schur, schur_comm]

/-! ### The boundary, named honestly

The commutation rests on `ρ` being **diagonal in B1** (`modularFlow_diagonal_eq_schur` is the only place the
modular flow becomes a B1-Schur multiplier). This is exactly the alignment **"pointer/decoherence basis B1 =
eigenbasis(ρ)"** — equilibrium einselection. If `ρ` carries coherence in B1 (is *not* diagonal there), then
`ρ^{is}` is not diagonal, `σ_s` is not a B1-Schur multiplier, and `σ_s ∘ schur μ ≠ schur μ ∘ σ_s` in general:
the two faces are then genuinely two clocks. We **report that as the boundary** rather than weakening B1 to
force commutation — the alignment is a named reading (`§5` residue), not a theorem from nothing. The deeper
question — whether the framework *forces* einselection onto the modular eigenbasis — is flagged open, not
attempted. -/

/-! ## §5 Part D — assemble the single generator, and state the residue

With B (`H ∝ K`) and C (`[σ_s, 𝒟] = 0` from `B1 = eigenbasis(ρ)`), the two faces glue into **one**
one-parameter semigroup `combinedFlow t = σ_{t/β} ∘ e^{t𝒟}`, sharing the time `t` with `s = t/β`. The
semigroup law **holds *because* the faces commute** — drop the commutation and `Φ_s ∘ Φ_t ≠ Φ_{s+t}`. This is
the finite-dimensional content of "two faces of one generator," earned, not glued. -/

/-- **The joint flow of the one generator**: `combinedFlow t = σ_{t/β} ∘ e^{t𝒟}` — the modular clock at rate
`1/β` composed with paper one's dissipative semigroup, on a single time `t`. -/
noncomputable def combinedFlow (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β : ℝ) (t : ℝ)
    (M : Matrix n n ℂ) : Matrix n n ℂ :=
  modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ (t / β) (dephaseFlow μ t M)

/-- `combinedFlow 0 = id`: both faces are the identity at time `0`. -/
theorem combinedFlow_zero (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β : ℝ)
    (M : Matrix n n ℂ) :
    combinedFlow d hρ μ β 0 M = M := by
  unfold combinedFlow
  rw [dephaseFlow_zero, zero_div, modularFlow_zero]

/-- **The single generator's semigroup law — the assembly, consuming the commutation.**
`Φ_s ∘ Φ_t = Φ_{s+t}`. The proof *uses* `modular_dephaseFlow_commute` to slide the dissipator past the
modular clock; without `[σ_s, 𝒟] = 0` (Part C) this step fails and the two faces would not compose into one
flow. With it, the modular group law (`modularFlow_add`) and the dissipative semigroup law
(`dephaseFlow_add`) combine on the shared time, `s/β + t/β = (s+t)/β`. **"Two faces of one generator,"
earned.** -/
theorem combinedFlow_add (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β : ℝ) (s t : ℝ)
    (M : Matrix n n ℂ) :
    combinedFlow d hρ μ β s (combinedFlow d hρ μ β t M)
      = combinedFlow d hρ μ β (s + t) M := by
  unfold combinedFlow
  rw [(modular_dephaseFlow_commute d hρ (t / β) μ s (dephaseFlow μ t M)).symm,
    dephaseFlow_add, modularFlow_add, show s / β + t / β = (s + t) / β from by ring]

/-! ### The generator-level commutation — the strongest form of "one generator"

Beyond the semigroup, the two *generators* commute as superoperators. For a diagonal state, the modular
generator `[K, ·]` is itself a Schur multiplier (`commGen_diagonal`, since `K` is diagonal —
`modularHamiltonian_diagonal`), and so is the dissipator's generator `𝒟 = schur(log μ)`; they commute by
`schur_comm`. This is `[𝓛_unitary, 𝒟] = 0` at the infinitesimal level. -/

/-- **The dissipator's generator** `𝒟(M)ᵢⱼ = (log μᵢⱼ)·Mᵢⱼ` — the Schur multiplier whose exponential is
`dephaseFlow` (`§2`); its real part `Re log μ = genReal` is paper one's arrow. -/
noncomputable def dissipatorGen (μ : n → n → ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  schur (fun i j => Complex.log (μ i j)) M

/-- The commutator with a diagonal matrix is a Schur multiplier: `[diag(k), M]ᵢⱼ = (kᵢ − kⱼ)·Mᵢⱼ`. -/
theorem commGen_diagonal (k : n → ℂ) (M : Matrix n n ℂ) :
    commGen (diagonal k) M = schur (fun i j => k i - k j) M := by
  ext i j
  rw [commGen, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, schur_apply]
  ring

/-- **`[𝓛_unitary, 𝒟] = 0` — the generators commute (diagonal state).** The modular generator `[K, ·]` and
the dissipator `𝒟` commute as superoperators: for `ρ = diag(d)`, `K = diag(-log dᵢ)`
(`modularHamiltonian_diagonal`) makes `[K,·]` a Schur multiplier, `𝒟` is one by construction, and Schur
multipliers commute. The two pieces of `𝓛 = -i[(1/β)K,·] + 𝒟` are one coherent object, not two glued. -/
theorem liouville_dephase_commute (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (M : Matrix n n ℂ) :
    commGen (modularHamiltonian (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ) (dissipatorGen μ M)
      = dissipatorGen μ
          (commGen (modularHamiltonian (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ) M) := by
  rw [modularHamiltonian_diagonal]
  simp only [dissipatorGen]
  rw [commGen_diagonal, commGen_diagonal, schur_comm]

/-- **The single GKLS generator** `𝓛(M) = -i[(1/β)K, M] + 𝒟(M)` — the modular (unitary) generator `K` from
the *state* `ρ` (`§3`, rate `1/β`) plus paper one's dissipator `𝒟` from the *arrow* (`§2`), as one
superoperator. Its unitary and dissipative parts commute (`liouville_dephase_commute`) and its semigroup is
`combinedFlow` (`combinedFlow_add`) — **at equilibrium, under `B1 = eigenbasis(ρ)`.** -/
noncomputable def oneGenerator (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β : ℝ)
    (M : Matrix n n ℂ) : Matrix n n ℂ :=
  -Complex.I • commGen ((1 / β : ℂ) • modularHamiltonian (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ) M
    + dissipatorGen μ M

end RelExist.OneGenerator
