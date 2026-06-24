/-
# Decoherence in the matrix model — the quantum→classical passage, made literal

This is the concrete half of the spec's next frontier ([04 §4.10](../../docs/spec/04-functorial-semantics.md)):
inside the literal traced SMC `matTracedSMC` (`Scratch/MatrixModel.lean`), exhibit the
**cartesian (classical) fragment** as an internal, definable retract of the relational
(quantum) whole, with **decoherence** the retraction and a **continuous copy-defect** the
knob between them. This is the firewall of `Compact.collapse` seen from the inside: not
"cartesian *or* compact" as a binary, but a *graded* map collapsing one into the other.

The standard basis is the **classical structure**. From it:

* `dephase` — **decoherence**: keep the diagonal, kill the off-diagonal (the coherences).
  It is linear, **idempotent**, trace-preserving, and a **retraction** onto the classical
  fragment (`dephase M = M ↔ IsClassical M`).
* `IsClassical` — the **cartesian fragment**: the diagonal states. Proved closed under
  composition *and mutually commuting* — copyability ⟺ commutativity, the no-broadcasting
  fault line, on the nose.
* `copyDefect` / `defectSq` — the **continuous interpolation**: the off-diagonal mass,
  zero iff classical, strictly positive on a witnessed superposition. So the classical
  fragment is *proper*: decoherence genuinely loses information (the Q→C passage is
  irreversible), the concrete face of `no_cloning`.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Scratch.MatrixModel

namespace RelExist.Decoherence

open Matrix BigOperators

variable {A : Type} [DecidableEq A]

/-! ### Decoherence and the classical fragment (over any `CommSemiring`) -/

section Semiring
variable {R : Type} [CommSemiring R]

/-- **Decoherence / dephasing in the standard basis.** Keep the diagonal, zero the
off-diagonal — the map that destroys the coherences a superposition is made of. The
standard basis is the *classical structure*; this is the induced retraction. -/
def dephase (M : Matrix A A R) : Matrix A A R :=
  fun i j => if i = j then M i j else 0

@[simp] lemma dephase_apply (M : Matrix A A R) (i j : A) :
    dephase M i j = if i = j then M i j else 0 := rfl

/-- A state is **classical** (in this basis) exactly when it is diagonal — no coherence
between distinct basis outcomes. These are the copyable, broadcastable states. -/
def IsClassical (M : Matrix A A R) : Prop := ∀ i j, i ≠ j → M i j = 0

lemma isClassical_iff_diagonal {M : Matrix A A R} :
    IsClassical M ↔ M = diagonal (Matrix.diag M) := by
  constructor
  · intro h; ext i j
    by_cases e : i = j
    · subst e; simp [Matrix.diag]
    · simp [diagonal_apply_ne _ e, h i j e]
  · intro h i j hij; rw [h, diagonal_apply_ne _ hij]

lemma isClassical_diagonal (d : A → R) : IsClassical (diagonal d) := by
  intro i j hij; rw [diagonal_apply_ne _ hij]

/-- The image of decoherence is classical: every dephased state is diagonal. -/
lemma isClassical_dephase (M : Matrix A A R) : IsClassical (dephase M) := by
  intro i j hij; simp [hij]

/-- **Decoherence is a retraction onto the classical fragment**: it fixes exactly the
classical states. (`dephase M = M ↔ M` is already decohered.) -/
lemma dephase_eq_self_iff {M : Matrix A A R} : dephase M = M ↔ IsClassical M := by
  constructor
  · intro h i j hij; rw [← h]; simp [hij]
  · intro h; ext i j; by_cases e : i = j
    · simp [e]
    · simp [e, h i j e]

/-- **Idempotent**: decohering twice is decohering once. Classicality, once achieved,
is stable — the off-diagonal is already gone. -/
@[simp] lemma dephase_idem (M : Matrix A A R) : dephase (dephase M) = dephase M := by
  ext i j; by_cases e : i = j <;> simp [e]

/-- Decoherence **preserves the trace** (probability is not lost, only coherence). -/
lemma trace_dephase [Fintype A] (M : Matrix A A R) : (dephase M).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag]

/-- The classical fragment is **closed under composition**. -/
lemma isClassical_mul [Fintype A] {M N : Matrix A A R}
    (hM : IsClassical M) (hN : IsClassical N) :
    IsClassical (M * N) := by
  rw [isClassical_iff_diagonal.1 hM, isClassical_iff_diagonal.1 hN, diagonal_mul_diagonal]
  exact isClassical_diagonal _

/-- **Copyability ⟺ commutativity.** Classical (copyable, broadcastable) states *commute* —
the no-broadcasting fault line, concretely: the cartesian fragment is the commutative one. -/
lemma classical_comm [Fintype A] {M N : Matrix A A R}
    (hM : IsClassical M) (hN : IsClassical N) :
    M * N = N * M := by
  rw [isClassical_iff_diagonal.1 hM, isClassical_iff_diagonal.1 hN,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
  ext i j; by_cases e : i = j
  · subst e; simp [mul_comm]
  · simp [diagonal_apply_ne _ e]

/-- Decoherence restricted to the classical fragment is the **identity** — so the cartesian
fragment is a genuine sub-thing the relational whole retracts onto. -/
lemma dephase_of_classical {M : Matrix A A R} (h : IsClassical M) : dephase M = M :=
  dephase_eq_self_iff.2 h

/-- The identity is classical — the trivial process is fully copyable. -/
lemma isClassical_one : IsClassical (1 : Matrix A A R) :=
  fun _ _ hij => Matrix.one_apply_ne hij

/-- Decoherence **commutes with the dagger** (transpose): it is a *self-adjoint* idempotent.
This is what makes the classical structure a `†`-Frobenius one — decoherence is "real". -/
lemma transpose_dephase (M : Matrix A A R) : (dephase M)ᵀ = dephase Mᵀ := by
  ext i j
  by_cases e : i = j
  · subst e; simp [dephase_apply, transpose_apply]
  · simp [dephase_apply, transpose_apply, e, Ne.symm e]

end Semiring

/-! ### The continuous knob (over a `CommRing`, so we can subtract) -/

section Ring
variable {R : Type} [CommRing R]

/-- **Copy-defect**: what decoherence destroys — the off-diagonal block (the coherences).
The continuous interpolation between feeling (high defect, irreducibly relational) and
knowing (zero defect, fully classical/copyable). -/
def copyDefect (M : Matrix A A R) : Matrix A A R := M - dephase M

@[simp] lemma copyDefect_apply (M : Matrix A A R) (i j : A) :
    copyDefect M i j = if i = j then 0 else M i j := by
  simp only [copyDefect, sub_apply, dephase_apply]
  by_cases e : i = j <;> simp [e]

/-- **The dial bottoms out exactly at the classical fragment.** Zero copy-defect ⟺ the
state is classical — knowing is unobstructed precisely when there is no coherence left to
disturb. -/
lemma copyDefect_eq_zero_iff {M : Matrix A A R} : copyDefect M = 0 ↔ IsClassical M := by
  rw [copyDefect, sub_eq_zero, eq_comm, dephase_eq_self_iff]

end Ring

/-! ### The fragment is *proper*: a witnessed superposition with nonzero defect -/

section Witness

/-- A genuine superposition: the uniform (all-ones) `2×2` state — maximal coherence, the
qubit `|+⟩⟨+|` up to normalization. -/
def plus : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1

/-- It is **not** classical: it carries coherence between the two basis outcomes. -/
lemma plus_not_classical : ¬ IsClassical plus := by
  intro h; exact one_ne_zero (h 0 1 (by decide))

/-- **Decoherence strictly collapses it** — information is lost, the passage is
irreversible. -/
lemma dephase_plus_ne : dephase plus ≠ plus := by
  intro h; exact plus_not_classical (dephase_eq_self_iff.1 h)

/-- **Its copy-defect is nonzero**: the classical fragment is a *proper* retract, so
decoherence is a real projection, not an isomorphism — the concrete face of `no_cloning`. -/
lemma copyDefect_plus_ne_zero : copyDefect plus ≠ 0 := by
  intro h
  have : copyDefect plus 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [h]
  simp [copyDefect_apply, plus] at this

/-- A **numeric magnitude** for the defect: the squared off-diagonal mass. It is `0`
exactly on the classical fragment and **positive** on the superposition — the literal
continuous coordinate from quantum (positive) to classical (zero). -/
def defectSq [Fintype A] (M : Matrix A A ℝ) : ℝ := ∑ i, ∑ j, (copyDefect M i j) ^ 2

lemma defectSq_nonneg [Fintype A] (M : Matrix A A ℝ) : 0 ≤ defectSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma defectSq_eq_zero_iff [Fintype A] {M : Matrix A A ℝ} : defectSq M = 0 ↔ IsClassical M := by
  rw [defectSq]
  constructor
  · intro h i j hij
    have hj : ∀ j', (copyDefect M i j') ^ 2 = 0 := by
      have hi : ∑ j', (copyDefect M i j') ^ 2 = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h i (Finset.mem_univ i)
        exact this
      exact fun j' => (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hi j'
        (Finset.mem_univ j')
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hj j)
    rwa [copyDefect_apply, if_neg hij] at this
  · intro h
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    by_cases e : i = j
    · simp [copyDefect_apply, e]
    · rw [copyDefect_apply, if_neg e, h i j e]; norm_num

/-- The witness, quantitatively: the superposition sits at **positive** defect. -/
lemma defectSq_plus_pos : 0 < defectSq plus := by
  rcases lt_or_eq_of_le (defectSq_nonneg plus) with h | h
  · exact h
  · exact absurd (defectSq_eq_zero_iff.1 h.symm) plus_not_classical

end Witness

end RelExist.Decoherence
