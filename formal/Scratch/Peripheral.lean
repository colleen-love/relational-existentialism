/-
# The spectral picture of knowing — `E = dephase` as a peripheral spectral projection

This is the finite-dimensional core of the **conjecture lift's** reconciliation (the relation-algebra
model's Decisions 1–2, recorded in [03.7](../../docs/spec/03.7-sparsity.md)): knowing `E` is a
**spectral projection** onto a distinguished part of attention's spectrum, the weight is the *invariant
state* (not an external primitive), and one asks whether the peripheral spectrum carries any *rotating*
coherence (eigenvalue of modulus 1 but `≠ 1`) — coherence that is **sustained but not known**.

For the genuine operation `E = dephase` the answer is sharp and elementary, because `dephase` is an
**idempotent** linear map (`dephase_idem`): a projection. So:

* `dephase_eigenvalue` — every eigenvalue is `0` or `1` (an idempotent has spectrum `⊆ {0,1}`). Hence
  **there is no rotating peripheral spectrum**: the only modulus-1 eigenvalue is `1` itself
  (`dephase_no_rotating_peripheral`). For `E`, *peripheral = fixed*. The three-way split (fixed = known,
  rotating-peripheral = permanent feeling, transient = passing feeling) collapses to two: there is no
  permanent-feeling band — all feeling `(1−E)` is transient, killed in one step.
* the **eigenvalue-1 space is the classical/known subalgebra** (`dephase_eigenspace_one`,
  `Decoherence.dephase_eq_self_iff`): commutative (`classical_comm`), copyable.
* the **eigenvalue-0 space is feeling** (`dephase_eigenspace_zero`): the off-diagonal coherence, the
  `(1−E)` mass; `M = E M + (1−E) M` splits every relation into known ⊕ felt
  (`dephase_add_copyDefect`).
* the **weight is invariant**: the standard trace is `dephase`-invariant (`Decoherence.trace_dephase`),
  so it is the *invariant state* of this `E` — the relational weight of Decision 1, here equal to the
  trace exactly because `dephase` is trace-preserving (the doubly-stochastic / primitive-symmetric case).

So this file discharges, at finite dimension and `sorry`-free, the existence claim the lift's interface
needs *for `E`*: `E` is a spectral projection onto a commutative subalgebra carrying an invariant trace,
with no rotating peripheral part. The general Perron–Frobenius statement for an arbitrary unital CP map
`Φ_c` (where rotating peripheral spectrum *can* occur) is the narrated `[open]` — see the spec.
-/
import Scratch.Decoherence
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

namespace RelExist.Peripheral

open RelExist.Decoherence Matrix

/-! ### The veto-check in full generality — any conditional expectation `E` is `{0,1}`-spectral

Decision 2 fixes `E` as a *projection* (spectral projection ∘ orientation). So the veto-check is not
special to `dephase`: **every idempotent linear map has eigenvalues `⊆ {0,1}`**, hence no rotating
peripheral spectrum and peripheral = fixed. -/

section AbstractIdempotent
variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- **Any conditional expectation `E = P` (idempotent linear map) has eigenvalues `⊆ {0,1}`.** A
projection scales an eigenvector only by `0` or `1`: from `P x = c • x` and `x ≠ 0`, `c² = c`. So for
*every* `E` there is **no rotating peripheral spectrum** — peripheral = fixed. The general form of the
veto-check, of which `dephase_eigenvalue` is the matrix instance. -/
theorem idempotent_eigenvalue (P : M →ₗ[R] M) (hP : ∀ x, P (P x) = P x)
    {c : R} {x : M} (hx : x ≠ 0) (h : P x = c • x) : c = 0 ∨ c = 1 := by
  have hsq : (c ^ 2 - c) • x = 0 := by
    have e : c ^ 2 • x = c • x := by
      calc c ^ 2 • x = c • (c • x) := by rw [sq, smul_smul]
        _ = c • P x := by rw [h]
        _ = P (c • x) := (P.map_smul c x).symm
        _ = P (P x) := by rw [h]
        _ = P x := hP x
        _ = c • x := h
    rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp hsq with hc | hx'
  · have hc' : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq]; exact hc
    rcases mul_eq_zero.mp hc' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · exact absurd hx' hx

end AbstractIdempotent

variable {A : Type} [DecidableEq A]

/-- **Decoherence is `ℝ`-linear in the scalar**: `E (c • M) = c • E M`. (One half of linearity; all we
need for the spectral argument.) -/
lemma dephase_smul (c : ℝ) (M : Matrix A A ℝ) : dephase (c • M) = c • dephase M := by
  ext i j
  by_cases h : i = j <;> simp [dephase_apply, Matrix.smul_apply, h]

/-- **The eigenvalues of `E = dephase` are `0` or `1`.** An idempotent (`E∘E = E`) can only scale an
eigenvector by `0` or `1`: from `E M = c • M` and `M ≠ 0`, `c² = c`. This is the **veto-check**: there
is no eigenvalue of modulus `1` other than `1` itself, so `dephase` has **no rotating peripheral
spectrum** — for `E`, peripheral = fixed. -/
theorem dephase_eigenvalue {c : ℝ} {M : Matrix A A ℝ} (hM : M ≠ 0) (h : dephase M = c • M) :
    c = 0 ∨ c = 1 := by
  have hsq : (c ^ 2 - c) • M = 0 := by
    have e : c ^ 2 • M = c • M := by
      calc c ^ 2 • M = c • (c • M) := by rw [sq, smul_smul]
        _ = c • dephase M := by rw [h]
        _ = dephase (c • M) := (dephase_smul c M).symm
        _ = dephase (dephase M) := by rw [h]
        _ = dephase M := dephase_idem M
        _ = c • M := h
    rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp hsq with hc | hM'
  · have hc' : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq]; exact hc
    rcases mul_eq_zero.mp hc' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · exact absurd hM' hM

/-- **No rotating peripheral spectrum** (the veto-check, stated for the peripheral band): any eigenvalue
of modulus `1` is exactly `1`. So the sustained part of `E` is the *fixed* part — there is no
sustained-but-unknown (rotating) coherence under decoherence. -/
theorem dephase_no_rotating_peripheral {c : ℝ} {M : Matrix A A ℝ}
    (hM : M ≠ 0) (h : dephase M = c • M) (hper : |c| = 1) : c = 1 := by
  rcases dephase_eigenvalue hM h with h0 | h1
  · rw [h0] at hper; norm_num at hper
  · exact h1

/-- **The eigenvalue-1 space is the classical (known) subalgebra.** `E M = 1·M ⟺ M` is classical —
the fixed points are exactly the copyable, commuting relations. -/
theorem dephase_eigenspace_one {M : Matrix A A ℝ} : dephase M = (1 : ℝ) • M ↔ IsClassical M := by
  rw [one_smul]; exact dephase_eq_self_iff

/-- **The eigenvalue-0 space is feeling.** `E M = 0·M ⟺ M` is purely off-diagonal (its diagonal
vanishes): the `(1−E)` coherence with no classical part — pure feeling. -/
theorem dephase_eigenspace_zero {M : Matrix A A ℝ} :
    dephase M = (0 : ℝ) • M ↔ ∀ i, M i i = 0 := by
  rw [zero_smul]
  constructor
  · intro h i
    have : dephase M i i = (0 : Matrix A A ℝ) i i := by rw [h]
    simpa [dephase_apply] using this
  · intro h; ext i j
    by_cases e : i = j
    · subst e; simp [dephase_apply, h i]
    · simp [dephase_apply, e]

/-- **Every relation splits known ⊕ felt**: `M = E M + (1−E) M`, the classical (eigenvalue-1) part plus
the off-diagonal feeling (eigenvalue-0) part. -/
theorem dephase_add_copyDefect (M : Matrix A A ℝ) : dephase M + copyDefect M = M := by
  rw [copyDefect]; abel

/-- **The known part is in the eigenvalue-1 (classical) space.** -/
theorem dephase_dephase_classical (M : Matrix A A ℝ) : IsClassical (dephase M) :=
  isClassical_dephase M

/-- **The felt part is in the eigenvalue-0 space** (its diagonal vanishes): `dephase (copyDefect M) = 0`. -/
theorem dephase_copyDefect (M : Matrix A A ℝ) : dephase (copyDefect M) = 0 := by
  ext i j
  simp only [dephase_apply, copyDefect_apply, Matrix.zero_apply]
  split <;> simp_all

/-- **The weight is invariant.** The standard trace is `E`-invariant — so it is the *invariant state* of
this `E`, the relational weight of Decision 1, here equal to the trace exactly because `dephase` is
trace-preserving (the primitive / doubly-stochastic case). -/
theorem dephase_trace_invariant [Fintype A] (M : Matrix A A ℝ) : (dephase M).trace = M.trace :=
  trace_dephase M

/-! ### The peripheral set is sparse — the finite-dimensional spectral form of "few modes self-sustain" -/

/-- The **diagonal support** of `E` — the peripheral / self-sustaining / known coordinates — has
exactly `card A` elements. -/
lemma card_diag [Fintype A] :
    (Finset.univ.filter (fun ij : A × A => ij.1 = ij.2)).card = Fintype.card A := by
  have h : (Finset.univ.filter (fun ij : A × A => ij.1 = ij.2))
        = Finset.univ.image (fun a : A => (a, a)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hij; subst hij; exact ⟨i, rfl⟩
    · rintro ⟨a, ha⟩; rw [Prod.mk.injEq] at ha; rw [← ha.1, ← ha.2]
  rw [h, Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab), Finset.card_univ]

/-- **The peripheral (self-sustaining / known) set is sparse.** Under the reconciliation the
self-sustaining relations are the peripheral = fixed = classical ones — the **diagonal** support of `E`.
There are `card A` of them among `card (A × A) = (card A)²` couplings: a fraction `1/card A` that
vanishes as the perspective grows. Stated exactly: `(diagonal).card · card A = card (A × A)`. The
finite-dimensional spectral form of Conjecture 3.7.4's "few modes self-sustain". -/
theorem peripheral_sparse [Fintype A] :
    (Finset.univ.filter (fun ij : A × A => ij.1 = ij.2)).card * Fintype.card A
      = Fintype.card (A × A) := by
  rw [card_diag, Fintype.card_prod]

end RelExist.Peripheral
