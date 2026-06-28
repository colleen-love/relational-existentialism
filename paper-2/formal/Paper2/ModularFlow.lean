/-
# Handoff X, Stages 1–2 — finite-dimensional modular self-relation

A1's arena is finite, type I, maximally traceable — the home of `D1 : σ = Tr`, the regime where internal
time is *off*. The text reaches further: self-relation as the **intrinsic dynamics a state induces**, which
at the deep end is the **modular flow** of Tomita–Takesaki (thermal time; energy = the modular Hamiltonian).
The whole modular structure already exists for a matrix algebra `Mₙ(ℂ)` with a faithful density matrix `ρ`,
and *that* is achievable now — this file builds it, sorry-free, by the spectral theorem (no `Matrix.exp`,
no operator-norm `CStarAlgebra` instance, no type III). See `docs/notes/modular-mathlib-audit.md` for the
gap audit and `docs/spec/modular-frontier.md` for the type III program this stops short of.

## What is built (all `[proved]`)

* `modPow ρ t = ρ^{it}` (spectral: `U · diag(e^{i t log dᵢ}) · Uᴴ`) — the one-parameter group:
  `modPow_mul`, `modPow_zero`, `modPow_conjTranspose` (`(ρ^{it})ᴴ = ρ^{-it}`), `modPow_neg_eq_inv`.
* `modularFlow ρ t M = ρ^{it} · M · ρ^{-it}` — a one-parameter group of **\*-automorphisms**:
  `modularFlow_add`, `modularFlow_zero`, `modularFlow_mul`/`modularFlow_one`, `modularFlow_star`. This is
  `σ` generalized from `Tr` to the modular flow.
* `modularHamiltonian ρ = -log ρ` (`U · diag(-log dᵢ) · Uᴴ`), Hermitian (`modularHamiltonian_isHermitian`)
  and **the Stone generator**: `ρ^{it} = U · diag(e^{-it·λᵢ}) · Uᴴ` with `λᵢ = -log dᵢ` the eigenvalues of
  `K` (`modPow_eq_generator`). The continuous-time self-adjoint generator the energy reading wanted.
* **`D1` as the timeless limit:** at the maximally mixed `ρ = c·I`, `ρ^{it}` is a scalar
  (`modPow_scalar`) and `modularFlow` is the identity (`modularFlow_maximally_mixed`) — internal time is
  *off*. So `σ = Tr` is the infinite-temperature limit of modular self-relation; departing from maximally
  mixed turns the flow on (`σ = Tr ⇝ σ = modularFlow ρ`).
* **Stage 2 — thermal time:** modular energies `= {-log dᵢ} = spectrum(K)` (`modularEnergy`,
  `modularHamiltonian_spectral`, `modPow_eq_energy`); the finite-dimensional Gibbs/KMS identity
  `modularEnergy = β·E + log Z` (`gibbs_kms`); and the **arrow test** — the modular flow is unitary, hence
  exactly reversible (`modular_reversible`: `σ_{-t} ∘ σ_t = id`), so it gives time's *flow*, not its
  *arrow*. The dissipative arrow (`RotatingSpectrum.genReal < 0`) is not in the modular (unitary) picture —
  the inherited Connes–Rovelli boundary, located not papered over.
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Paper2.ModularFlow

open Matrix Complex
open scoped ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Stage 1 — modular flow `ρ^{it} · M · ρ^{-it}` and the modular Hamiltonian `-log ρ` -/

omit [Fintype n] in
/-- A constant-diagonal matrix is a scalar: `diag(λ i. k) = k • 1`. -/
private lemma diagonal_const (k : ℂ) :
    diagonal (fun _ : n => k) = k • (1 : Matrix n n ℂ) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h; simp
  · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Conjugation by a unitary collapses two factors: `(U A Uᴴ)(U B Uᴴ) = U (A B) Uᴴ` when `Uᴴ U = 1`. -/
private lemma conj_collapse (U A B : Matrix n n ℂ) (h : star U * U = 1) :
    U * A * star U * (U * B * star U) = U * (A * B) * star U := by
  rw [show U * A * star U * (U * B * star U) = U * A * (star U * U) * B * star U from by
      noncomm_ring, h]
  noncomm_ring

/-- The diagonal phase `e^{i t · log dᵢ}` of `ρ^{it}` on the `i`-th eigenvalue `dᵢ`. -/
noncomputable def modDiag (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (i : n) : ℂ :=
  Complex.exp (Complex.I * t * Real.log (hρ.eigenvalues i))

@[simp] lemma modDiag_apply (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (i : n) :
    modDiag ρ hρ t i = Complex.exp (Complex.I * t * Real.log (hρ.eigenvalues i)) := rfl

/-- **`ρ^{it}`** via the spectral theorem: `U · diag(e^{i t log dᵢ}) · Uᴴ`. The intrinsic dynamics the
state `ρ` induces, as a finite-dimensional modular operator. -/
noncomputable def modPow (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) : Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (modDiag ρ hρ t)
    * star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- **The modular Hamiltonian `K = -log ρ`** via the spectral theorem: `U · diag(-log dᵢ) · Uᴴ`. -/
noncomputable def modularHamiltonian (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ)
    * diagonal (fun i => ((- Real.log (hρ.eigenvalues i) : ℝ) : ℂ))
    * star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- **The modular flow** `σ_t(M) = ρ^{it} · M · ρ^{-it}` — the intrinsic dynamics `ρ` induces on the
algebra. `σ = Tr` (D1) is its maximally-mixed limit (`modularFlow_maximally_mixed`). -/
noncomputable def modularFlow (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (M : Matrix n n ℂ) :
    Matrix n n ℂ :=
  modPow ρ hρ t * M * modPow ρ hρ (-t)

/-- **The group law for `ρ^{it}`:** `ρ^{is} · ρ^{it} = ρ^{i(s+t)}`. The conjugating unitaries cancel and
the diagonal phases add. -/
theorem modPow_mul (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (s t : ℝ) :
    modPow ρ hρ s * modPow ρ hρ t = modPow ρ hρ (s + t) := by
  have hfun : (fun i => modDiag ρ hρ s i * modDiag ρ hρ t i) = modDiag ρ hρ (s + t) := by
    funext i
    simp only [modDiag_apply]
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  unfold modPow
  rw [conj_collapse _ _ _ (unitary.coe_star_mul_self hρ.eigenvectorUnitary),
    diagonal_mul_diagonal, hfun]

/-- `ρ^{i·0} = 1`. -/
@[simp] theorem modPow_zero (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : modPow ρ hρ 0 = 1 := by
  have hfun : modDiag ρ hρ 0 = (fun _ : n => (1 : ℂ)) := by
    funext i
    simp only [modDiag_apply, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
  unfold modPow
  rw [hfun, diagonal_one, mul_one]
  exact unitary.coe_mul_star_self _

/-- `ρ^{it} · ρ^{-it} = 1`. -/
theorem modPow_mul_neg (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modPow ρ hρ t * modPow ρ hρ (-t) = 1 := by
  rw [modPow_mul, add_neg_cancel, modPow_zero]

theorem modPow_neg_mul (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modPow ρ hρ (-t) * modPow ρ hρ t = 1 := by
  rw [modPow_mul, neg_add_cancel, modPow_zero]

/-- **`ρ^{it}` is unitary:** its conjugate transpose is `ρ^{-it}` — so the modular flow is reversible
(the fact behind the arrow test, `modular_no_arrow`). -/
theorem modPow_conjTranspose (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    (modPow ρ hρ t)ᴴ = modPow ρ hρ (-t) := by
  have hfun : star (modDiag ρ hρ t) = modDiag ρ hρ (-t) := by
    funext i
    simp only [Pi.star_apply, modDiag_apply, Complex.star_def]
    rw [← Complex.exp_conj]
    congr 1
    simp only [_root_.map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  unfold modPow
  simp only [Matrix.star_eq_conjTranspose]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    ← mul_assoc, hfun]

/-- `ρ^{-it} = (ρ^{it})⁻¹`. -/
theorem modPow_neg_eq_inv (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modPow ρ hρ (-t) = (modPow ρ hρ t)⁻¹ :=
  (Matrix.inv_eq_right_inv (modPow_mul_neg ρ hρ t)).symm

/-! ### `modularFlow` is a one-parameter group of \*-automorphisms -/

/-- **The modular flow group law:** `σ_s ∘ σ_t = σ_{s+t}` — internal time composes additively. -/
theorem modularFlow_add (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (s t : ℝ) (M : Matrix n n ℂ) :
    modularFlow ρ hρ s (modularFlow ρ hρ t M) = modularFlow ρ hρ (s + t) M := by
  unfold modularFlow
  rw [show modPow ρ hρ s * (modPow ρ hρ t * M * modPow ρ hρ (-t)) * modPow ρ hρ (-s)
        = (modPow ρ hρ s * modPow ρ hρ t) * M * (modPow ρ hρ (-t) * modPow ρ hρ (-s)) from by
      noncomm_ring,
    modPow_mul, modPow_mul, show (-t) + (-s) = -(s + t) from by ring]

/-- `σ_0 = id`. -/
@[simp] theorem modularFlow_zero (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (M : Matrix n n ℂ) :
    modularFlow ρ hρ 0 M = M := by
  unfold modularFlow; rw [neg_zero, modPow_zero, one_mul, mul_one]

/-- The modular flow is **multiplicative** — an algebra endomorphism at each `t`. -/
theorem modularFlow_mul (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (M N : Matrix n n ℂ) :
    modularFlow ρ hρ t (M * N) = modularFlow ρ hρ t M * modularFlow ρ hρ t N := by
  unfold modularFlow
  rw [show modPow ρ hρ t * M * modPow ρ hρ (-t) * (modPow ρ hρ t * N * modPow ρ hρ (-t))
        = modPow ρ hρ t * M * (modPow ρ hρ (-t) * modPow ρ hρ t) * N * modPow ρ hρ (-t) from by
      noncomm_ring, modPow_neg_mul]
  noncomm_ring

/-- The modular flow is **unital**: `σ_t(1) = 1`. -/
@[simp] theorem modularFlow_one (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modularFlow ρ hρ t 1 = 1 := by
  unfold modularFlow; rw [mul_one, modPow_mul_neg]

/-- The modular flow is **\*-preserving**: `σ_t(Mᴴ) = (σ_t M)ᴴ`. With multiplicativity and unitality, each
`σ_t` is a unital \*-automorphism of `Mₙ(ℂ)` — the finite-dimensional modular automorphism group. -/
theorem modularFlow_star (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (M : Matrix n n ℂ) :
    modularFlow ρ hρ t (Mᴴ) = (modularFlow ρ hρ t M)ᴴ := by
  unfold modularFlow
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, modPow_conjTranspose, neg_neg,
    mul_assoc]

/-! ### The modular Hamiltonian is the Stone generator -/

/-- **The Stone generator is the modular Hamiltonian.** `ρ^{it} = U · diag(e^{-i t λᵢ}) · Uᴴ` with
`λᵢ = -log dᵢ` the eigenvalues of `K = modularHamiltonian`: `ρ^{it}` and `K` are simultaneously diagonalized
and `ρ^{it}`'s eigenvalue on mode `i` is `e^{-it·(modular energy)}`. The continuous-time self-adjoint
generator the energy reading wanted, finite-dimensionally. -/
theorem modPow_eq_generator (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modPow ρ hρ t = (hρ.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun i => Complex.exp (-Complex.I * t * ((- Real.log (hρ.eigenvalues i) : ℝ) : ℂ)))
      * star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
  have hfun : modDiag ρ hρ t
      = (fun i => Complex.exp (-Complex.I * t * ((- Real.log (hρ.eigenvalues i) : ℝ) : ℂ))) := by
    funext i; simp only [modDiag_apply]; congr 1; push_cast; ring
  unfold modPow; rw [hfun]

/-- `modularHamiltonian` is Hermitian (real spectrum `{-log dᵢ}`): a genuine self-adjoint generator. -/
theorem modularHamiltonian_isHermitian (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) :
    (modularHamiltonian ρ hρ).IsHermitian := by
  have hfun : star (fun i => ((-Real.log (hρ.eigenvalues i) : ℝ) : ℂ))
      = (fun i => ((-Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) := by
    funext i; simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  show (modularHamiltonian ρ hρ)ᴴ = modularHamiltonian ρ hρ
  unfold modularHamiltonian
  simp only [Matrix.star_eq_conjTranspose]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    ← mul_assoc, hfun]

/-! ## Stage 1 — D1 as the maximally-mixed (timeless) limit -/

/-- **At a scalar (maximally mixed) state `ρ = c · I`, `ρ^{it}` is a scalar `e^{i t log c} · I`.** Every
eigenvalue is `c`, so the diagonal phase is constant. -/
theorem modPow_scalar (c : ℝ) (hρ : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) (t : ℝ) :
    modPow ((c : ℂ) • 1) hρ t = (Complex.exp (Complex.I * t * Real.log c)) • 1 := by
  set U : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := unitary.coe_mul_star_self _
  have hc : star U * ((c : ℂ) • (1 : Matrix n n ℂ)) * U = (c : ℂ) • (1 : Matrix n n ℂ) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hUU]
  have heqd : diagonal (RCLike.ofReal ∘ hρ.eigenvalues) = (c : ℂ) • (1 : Matrix n n ℂ) := by
    rw [← hρ.star_mul_self_mul_eq_diagonal]; exact hc
  have heig : ∀ i, Real.log (hρ.eigenvalues i) = Real.log c := by
    intro i
    have h1 := congrFun (congrFun heqd i) i
    simp only [diagonal_apply_eq, Function.comp_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h1
    have h2 : hρ.eigenvalues i = c := RCLike.ofReal_inj.mp h1
    rw [h2]
  have hfun : modDiag ((c : ℂ) • 1) hρ t = (fun _ : n => Complex.exp (Complex.I * t * Real.log c)) := by
    funext i; simp only [modDiag_apply, heig]
  unfold modPow
  rw [hfun, diagonal_const, mul_smul_comm, smul_mul_assoc, mul_one, hUU']

/-- **D1 is the timeless limit of modular self-relation.** At the maximally mixed `ρ = c·I`, the modular
flow is the identity for all `t` — **internal time is off**. So `σ = Tr` (D1's arena) is the
infinite-temperature limit; as `ρ` departs from maximally mixed the flow turns on. The `ρ = I/n ⇒ trivial
flow` end of `σ = Tr ⇝ σ = modularFlow ρ`, proved. -/
theorem modularFlow_maximally_mixed (c : ℝ)
    (hρ : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) (t : ℝ) (M : Matrix n n ℂ) :
    modularFlow ((c : ℂ) • 1) hρ t M = M := by
  have hkk : Complex.exp (Complex.I * (-t : ℝ) * Real.log c)
      * Complex.exp (Complex.I * (t : ℝ) * Real.log c) = 1 := by
    rw [← Complex.exp_add,
      show Complex.I * (-t : ℝ) * Real.log c + Complex.I * (t : ℝ) * Real.log c = 0 from by
        push_cast; ring, Complex.exp_zero]
  unfold modularFlow
  rw [modPow_scalar, modPow_scalar, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
    hkk, one_smul]

/-! ## Stage 2 — thermal time: modular energies, Gibbs/KMS, and the arrow test -/

/-- **The modular energies** — the spectrum of the modular Hamiltonian `K = -log ρ`: `Eᵢ = -log dᵢ`. -/
noncomputable def modularEnergy (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (i : n) : ℝ :=
  - Real.log (hρ.eigenvalues i)

/-- The modular Hamiltonian carries exactly the modular energies on its spectral diagonal: `K = U ·
diag(Eᵢ) · Uᴴ`. So `spectrum(K) = {Eᵢ} = {-log dᵢ}` — energy *is* the modular Hamiltonian. -/
theorem modularHamiltonian_spectral (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) :
    modularHamiltonian ρ hρ = (hρ.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun i => (modularEnergy ρ hρ i : ℂ)) * star (hρ.eigenvectorUnitary : Matrix n n ℂ) :=
  rfl

/-- **`ρ^{it} = e^{-itK}` in the energy basis:** `ρ^{it} = U · diag(e^{-i t Eᵢ}) · Uᴴ`. The modular energies
are the rotation frequencies of the modular flow — the Stone form, read through the energies. -/
theorem modPow_eq_energy (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) :
    modPow ρ hρ t = (hρ.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun i => Complex.exp (-Complex.I * t * (modularEnergy ρ hρ i : ℂ)))
      * star (hρ.eigenvectorUnitary : Matrix n n ℂ) :=
  modPow_eq_generator ρ hρ t

/-- **Gibbs ⇒ KMS, finite-dimensionally.** If `ρ`'s eigenvalues are thermal — `dᵢ = e^{-β Eᵢ}/Z` (the Gibbs
state at inverse temperature `β` for a Hamiltonian with energies `Eᵢ`) — then the modular energy is the
physical energy scaled by `β`, up to the normalization constant: `modularEnergy i = β·Eᵢ + log Z`. So the
modular Hamiltonian is `β·H` up to a scalar, the modular flow `Ad(ρ^{it})` runs the physical Heisenberg
dynamics at rate `β` (the scalar shift drops out of the conjugation), and *time = the modular flow of the
state*. This is the finite-dimensional KMS identity. -/
theorem gibbs_kms (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (β : ℝ) (E : n → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hgibbs : ∀ i, hρ.eigenvalues i = Real.exp (-(β * E i)) / Z) (i : n) :
    modularEnergy ρ hρ i = β * E i + Real.log Z := by
  unfold modularEnergy
  rw [hgibbs i, Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp]
  ring

/-- **The modular flow is reversible — it has no arrow.** `σ_{-t} ∘ σ_t = id`: the unitary modular flow runs
backwards exactly (a consequence of the group law and `modPow` being unitary). So it carries time's *flow* —
a one-parameter group of \*-automorphisms — but **not** its *arrow*. The dissipative, coherence-lowering
arrow (`RotatingSpectrum.genReal < 0`) is **not** in the modular picture: a unitary automorphism cannot
decrease coherence. This is exactly Connes–Rovelli's own disclaimer, located precisely in this framework —
the arrow is the *non-modular* (dissipator) part, inherited as the open boundary, not a defect of this
construction. -/
theorem modular_reversible (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) (t : ℝ) (M : Matrix n n ℂ) :
    modularFlow ρ hρ (-t) (modularFlow ρ hρ t M) = M := by
  rw [modularFlow_add, neg_add_cancel, modularFlow_zero]

end Paper2.ModularFlow
