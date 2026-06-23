/-
# Classical structures and decoherence — the abstract (typeclass) companion

The concrete passage Q→C lives in `Scratch/Decoherence.lean` (dephasing on matrices). Here
is its **abstract** form, in the operative style of `Scratch/Compact.lean`: we axiomatize the
*operative content* of a dagger structure and of a classical-structure-induced decoherence —
rather than reconstruct the full `†`-Frobenius / symmetric-monoidal coherence (large, and the
free coherent SMC `Cl_coh(𝕋)` is the place for that) — and then **validate** it by showing the
matrix model is an instance, so abstract and concrete are the same object.

* `DaggerCategory` — a category with an involutive, contravariant, identity-on-objects
  `dagger` (`(·)†`). The matrix model is one, with `dagger = transpose` (`matDagger`).
* `Decoherence` — the operative content of a classical structure on one object: its
  endomorphism `†`-monoid together with a **decoherence** retraction `dec` whose fixed points
  (the *classical fragment*) form a **commutative** submonoid, with `dec` self-adjoint. The
  matrix model is an instance with `dec = dephase` (`matDecoherence`), discharging every axiom
  from the concrete lemmas — so the abstract decoherence *is* matrix dephasing.

From the axioms alone we get the structural theorems: the classical fragment is a commutative
submonoid containing the identity, and `dec` is an idempotent, self-adjoint retraction onto it.
-/
import Mathlib.Data.Matrix.Basic
import Scratch.MatrixModel
import Scratch.Decoherence

namespace RelExist.Classical

open Matrix
open RelExist.MatrixModel RelExist.Decoherence

universe u v

/-! ### Dagger categories -/

/-- A **dagger category**: a category with an involutive, contravariant, identity-on-objects
involution `dgr` (the adjoint `(·)†`). This is the operative core of `FdHilb`/`Rel`; the full
dagger *symmetric monoidal* coherence is deliberately not reconstructed here. -/
structure DaggerCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)
  dgr : {X Y : Obj} → Hom X Y → Hom Y X
  dgr_dgr : ∀ {X Y} (f : Hom X Y), dgr (dgr f) = f
  dgr_id : ∀ X, dgr (id X) = id X
  dgr_comp : ∀ {X Y Z} (f : Hom X Y) (g : Hom Y Z), dgr (comp f g) = comp (dgr g) (dgr f)

/-- **The matrix model is a dagger category**, with the dagger the matrix transpose — the
real-form adjoint. (Over `ℂ` one would take the conjugate-transpose; transpose is the dagger
of the real/`CommSemiring` model.) -/
def matDagger (R : Type) [CommSemiring R] : DaggerCategory where
  Obj := FinType
  Hom A B := Matrix A.carrier B.carrier R
  id A := (1 : Matrix A.carrier A.carrier R)
  comp f g := f * g
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc
  dgr f := fun i j => f j i        -- transpose
  dgr_dgr _ := rfl
  dgr_id A := by
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  dgr_comp f g := by
    ext i j
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### Decoherence — the operative content of a classical structure -/

/-- The **operative content of a classical structure** on a single object: its endomorphism
`†`-monoid `(Car, one, mul, dgr)` together with a **decoherence** map `dec` such that

* `dec` is idempotent and fixes the identity (decohering twice = once; `id` is classical);
* the **classical fragment** `{a | dec a = a}` is closed under `mul` and **commutative**
  (copyability ⟺ commutativity — the no-broadcasting fault line);
* `dec` is **self-adjoint** (`(dec a)† = dec (a†)`) — the `†`-Frobenius reality.

This is exactly the structure the matrix `dephase` carries; `matDecoherence` is the instance. -/
structure Decoherence where
  Car : Type u
  one : Car
  mul : Car → Car → Car
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  dgr : Car → Car
  dgr_dgr : ∀ a, dgr (dgr a) = a
  dgr_one : dgr one = one
  dgr_mul : ∀ a b, dgr (mul a b) = mul (dgr b) (dgr a)
  dec : Car → Car
  dec_idem : ∀ a, dec (dec a) = dec a
  dec_one : dec one = one
  dec_dgr : ∀ a, dgr (dec a) = dec (dgr a)
  classical_mul : ∀ a b, dec a = a → dec b = b → dec (mul a b) = mul a b
  classical_comm : ∀ a b, dec a = a → dec b = b → mul a b = mul b a

namespace Decoherence

variable (D : Decoherence)

/-- The **classical fragment**: the fixed points of decoherence — the copyable processes. -/
def IsClassical (a : D.Car) : Prop := D.dec a = a

/-- Decohering anything lands in the classical fragment (the image of `dec`). -/
theorem isClassical_dec (a : D.Car) : D.IsClassical (D.dec a) := D.dec_idem a

/-- The identity is classical. -/
theorem isClassical_one : D.IsClassical D.one := D.dec_one

/-- The classical fragment is **closed under composition**. -/
theorem isClassical_mul {a b : D.Car} (ha : D.IsClassical a) (hb : D.IsClassical b) :
    D.IsClassical (D.mul a b) := D.classical_mul a b ha hb

/-- **Copyability ⟺ commutativity**: classical processes commute. -/
theorem isClassical_comm {a b : D.Car} (ha : D.IsClassical a) (hb : D.IsClassical b) :
    D.mul a b = D.mul b a := D.classical_comm a b ha hb

/-- **Decoherence is a retraction**: it fixes exactly the classical fragment. -/
theorem dec_eq_self_iff {a : D.Car} : D.dec a = a ↔ D.IsClassical a := Iff.rfl

/-- The classical fragment is **closed under the dagger** (it is a `†`-submonoid). -/
theorem isClassical_dgr {a : D.Car} (ha : D.IsClassical a) : D.IsClassical (D.dgr a) := by
  unfold IsClassical at *; rw [← D.dec_dgr, ha]

end Decoherence

/-- **The matrix model is a `Decoherence`** — abstract decoherence *is* matrix dephasing.
Every axiom is discharged from the concrete lemmas of `Scratch/Decoherence.lean`. -/
def matDecoherence {A : Type} [Fintype A] [DecidableEq A] (R : Type) [CommSemiring R] :
    Decoherence where
  Car := Matrix A A R
  one := 1
  mul := (· * ·)
  one_mul := Matrix.one_mul
  mul_one := Matrix.mul_one
  mul_assoc := Matrix.mul_assoc
  dgr := Matrix.transpose
  dgr_dgr := Matrix.transpose_transpose
  dgr_one := Matrix.transpose_one
  dgr_mul := fun a b => Matrix.transpose_mul a b
  dec := dephase
  dec_idem := dephase_idem
  dec_one := dephase_eq_self_iff.2 isClassical_one
  dec_dgr := fun M => transpose_dephase M
  classical_mul := fun _ _ ha hb =>
    dephase_eq_self_iff.2 (RelExist.Decoherence.isClassical_mul
      (dephase_eq_self_iff.1 ha) (dephase_eq_self_iff.1 hb))
  classical_comm := fun _ _ ha hb =>
    RelExist.Decoherence.classical_comm (dephase_eq_self_iff.1 ha) (dephase_eq_self_iff.1 hb)

end RelExist.Classical
