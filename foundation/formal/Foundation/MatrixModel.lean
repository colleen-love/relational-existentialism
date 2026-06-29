/-
# The matrix model — a *literal* traced SMC (the physics functor, made concrete)

This is the capstone the spec named as the frontier: a genuine `TracedSMC` whose objects are
finite types, morphisms are matrices, `⊗` is the Kronecker product, and the **trace is the
quantum partial trace** `ptrace`. With it, the physics functor of Layer 4 is *literal* — the
doctrine's `Tr` is, on the nose, the partial trace of categorical quantum mechanics.

Five of the seven JSV trace axioms are exactly the `Scratch/PartialTrace.lean` lemmas
(naturality left/right, sliding, yanking, and trace-compatibility implicitly). The two
**retensoring** axioms — vanishing over `U ⊗ V` and superposing — need the associators,
which here are honest **permutation matrices** (`permMat` of `Equiv.prodAssoc`); we prove the
required reindexing lemmas and discharge them. Yanking is `ptrace` of the swap permutation.

So the marked frontier — a concrete `FdHilb`/`FGModuleCat`-style `TracedSMC` instance — is
**closed**: `matTracedSMC`.
-/
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Foundation.Traced
import Foundation.PartialTrace

namespace RelExist.MatrixModel

open Matrix Kronecker BigOperators RelExist.Traced RelExist.PartialTrace

/-! ### Permutation matrices (the structural isos) -/

/-- The **permutation matrix** of a bijection `e : A ≃ B` — the matrix of the linear iso
sending basis vector `a` to basis vector `e a`. The associators, unitors and braiding of the
matrix model are all of this form. (`R` is explicit so the matrix type is always pinned.) -/
def permMat (R : Type) [CommSemiring R] {A B : Type} [DecidableEq B] (e : A ≃ B) :
    Matrix A B R :=
  fun a b => if e a = b then 1 else 0

variable {R : Type} [CommSemiring R]

/-- Left-multiplying by a permutation matrix **reindexes the rows**. -/
theorem permMat_mul {A B C : Type} [Fintype B] [DecidableEq B]
    (e : A ≃ B) (M : Matrix B C R) (a : A) (c : C) :
    (permMat R e * M) a c = M (e a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e a)]
  · simp [permMat]
  · intro b _ hb; simp [permMat, Ne.symm hb]
  · simp

/-- Right-multiplying by a permutation matrix **reindexes the columns** (by `e⁻¹`). -/
theorem mul_permMat {A B C : Type} [Fintype A] [DecidableEq B]
    (M : Matrix C A R) (e : A ≃ B) (c : C) (b : B) :
    (M * permMat R e) c b = M c (e.symm b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · simp [permMat, Equiv.apply_symm_apply]
  · intro a _ ha
    have hne : e a ≠ b := fun h => ha (by rw [← h, e.symm_apply_apply])
    simp [permMat, hne]
  · simp

/-- A permutation matrix and its inverse compose to the identity. -/
theorem permMat_mul_symm {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) : (permMat R e * permMat R e.symm : Matrix A A R) = 1 := by
  ext a c
  rw [permMat_mul]
  simp [permMat, Matrix.one_apply, Equiv.symm_apply_apply]

/-- And in the other order. -/
theorem permMat_symm_mul {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) : (permMat R e.symm * permMat R e : Matrix B B R) = 1 := by
  ext a c
  rw [permMat_mul]
  simp [permMat, Matrix.one_apply, Equiv.apply_symm_apply]

/-! ### Yanking — the partial trace of the swap permutation -/

/-- **Yanking.** `Tr(σ) = id` for the braiding `σ = permMat (prodComm)`. -/
theorem ptrace_braid {U : Type} [Fintype U] [DecidableEq U] :
    ptrace (permMat R (Equiv.prodComm U U) : Matrix (U × U) (U × U) R) = 1 := by
  ext i j
  rw [ptrace_apply]
  simp only [permMat, Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.mk.injEq, Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · simp

/-! ### Vanishing over the unit -/

/-- **Vanishing-I.** Tracing out the unit wire is conjugation by the unitors. -/
theorem ptrace_vanish_unit {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : Matrix (X × PUnit) (Y × PUnit) R) :
    ptrace f
      = permMat R (Equiv.prodPUnit X).symm * (f * permMat R (Equiv.prodPUnit Y)) := by
  ext a c
  rw [permMat_mul, mul_permMat, ptrace_apply]
  simp [Equiv.prodPUnit]

/-! ### Vanishing over a product wire (with the associator) -/

/-- **Vanishing-II.** Tracing out `U ⊗ V` equals tracing out `V` then `U`, after
reassociating by the associator permutation. -/
theorem ptrace_vanish_tens {X Y U V : Type}
    [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    [DecidableEq X] [DecidableEq Y] [DecidableEq U] [DecidableEq V]
    (f : Matrix (X × (U × V)) (Y × (U × V)) R) :
    ptrace f
      = ptrace (ptrace
          (permMat R (Equiv.prodAssoc X U V) *
            (f * permMat R (Equiv.prodAssoc Y U V).symm))) := by
  have hg : (permMat R (Equiv.prodAssoc X U V) * (f * permMat R (Equiv.prodAssoc Y U V).symm))
      = fun a c => f (Equiv.prodAssoc X U V a) (Equiv.prodAssoc Y U V c) := by
    ext a c; rw [permMat_mul, mul_permMat, Equiv.symm_symm]
  rw [hg]
  ext x y
  simp only [ptrace_apply, Equiv.prodAssoc_apply]
  rw [Fintype.sum_prod_type]

/-! ### Superposing (with the associator) -/

/-- **Superposing.** The trace commutes with whiskering `W ◁ -`, after reassociating. -/
theorem ptrace_superpose {W X Y U : Type}
    [Fintype W] [Fintype X] [Fintype Y] [Fintype U]
    [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq U]
    (f : Matrix (X × U) (Y × U) R) :
    ptrace (permMat R (Equiv.prodAssoc W X U) *
        (((1 : Matrix W W R) ⊗ₖ f) * permMat R (Equiv.prodAssoc W Y U).symm))
      = (1 : Matrix W W R) ⊗ₖ ptrace f := by
  have hg : (permMat R (Equiv.prodAssoc W X U) *
        (((1 : Matrix W W R) ⊗ₖ f) * permMat R (Equiv.prodAssoc W Y U).symm))
      = fun a c => ((1 : Matrix W W R) ⊗ₖ f)
          (Equiv.prodAssoc W X U a) (Equiv.prodAssoc W Y U c) := by
    ext a c; rw [permMat_mul, mul_permMat, Equiv.symm_symm]
  rw [hg]
  ext p q
  obtain ⟨pw, px⟩ := p
  obtain ⟨qw, qy⟩ := q
  simp only [ptrace_apply, Equiv.prodAssoc_apply, kronecker_apply, one_apply, Finset.mul_sum]

/-! ### The instance — finite types and matrices form a traced SMC -/

/-- A **finite type with decidable equality** — the objects of the matrix category. -/
structure FinType where
  /-- the underlying type -/
  carrier : Type
  [fin : Fintype carrier]
  [dec : DecidableEq carrier]

attribute [instance] FinType.fin FinType.dec

/-- **The matrix model: a literal traced symmetric monoidal category.** Objects are finite
types, `Hom A B = Matrix A B R`, `⊗` is the Kronecker product, and the trace **is** the
quantum partial trace. This is the concrete `FdHilb`/`FGModuleCat`-style instance the spec
named as the frontier — now closed. -/
def matTracedSMC : TracedSMC.{1, 0} where
  Obj := FinType
  Hom A B := Matrix A.carrier B.carrier R
  id A := (1 : Matrix A.carrier A.carrier R)
  comp f g := f * g
  id_comp f := Matrix.one_mul f
  comp_id f := Matrix.mul_one f
  assoc f g h := Matrix.mul_assoc f g h
  tens A B := ⟨A.carrier × B.carrier⟩
  unit := ⟨PUnit⟩
  tensH f g := f ⊗ₖ g
  braid X Y := permMat R (Equiv.prodComm X.carrier Y.carrier)
  trace M := ptrace M
  aHom X Y Z := permMat R (Equiv.prodAssoc X.carrier Y.carrier Z.carrier)
  aInv X Y Z := permMat R (Equiv.prodAssoc X.carrier Y.carrier Z.carrier).symm
  a_hom_inv _ _ _ := permMat_mul_symm _
  a_inv_hom _ _ _ := permMat_symm_mul _
  ruHom X := permMat R (Equiv.prodPUnit X.carrier)
  ruInv X := permMat R (Equiv.prodPUnit X.carrier).symm
  ru_hom_inv _ := permMat_mul_symm _
  ru_inv_hom _ := permMat_symm_mul _
  luHom X := permMat R (Equiv.punitProd X.carrier)
  luInv X := permMat R (Equiv.punitProd X.carrier).symm
  lu_hom_inv _ := permMat_mul_symm _
  lu_inv_hom _ := permMat_symm_mul _
  trace_nat_left g f := ptrace_nat_left g f
  trace_nat_right f g := ptrace_nat_right f g
  trace_slide f h := ptrace_slide f h
  trace_yank _ := ptrace_braid
  trace_vanish_unit f := ptrace_vanish_unit f
  trace_vanish_tens f := ptrace_vanish_tens f
  trace_superpose f := ptrace_superpose f

end RelExist.MatrixModel
