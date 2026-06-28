/-
# The matrix model is *coherent* — coherence in the literal physics model

`matTracedSMC` ([`MatrixModel.lean`](MatrixModel.lean)) is the literal traced SMC (matrices,
`⊗` = Kronecker, trace = partial trace). Here we promote it to a `CoherentTracedSMC`: all
eight symmetric-monoidal coherence laws hold. The engine is the **functoriality of permutation
matrices** — `permMat (e.trans e') = permMat e * permMat e'`, `permMat e ⊗ₖ permMat e' =
permMat (e ×' e')`, `permMat (refl) = 1` — which turns the pure-permutation laws (pentagon,
triangle, symmetry, hexagon) into equalities of `Equiv`s that hold by computation, and reduces
the naturality laws to the reindexing lemmas `permMat_mul` / `mul_permMat`.

So coherence is validated not only in `Rel` but in the **literal physics model** too.
-/
import Scratch.MatrixModel
import RelExist.Coherence

namespace RelExist.MatrixModel

open Matrix Kronecker BigOperators RelExist.Traced

variable {R : Type} [CommSemiring R]

/-! ### Functoriality of permutation matrices -/

/-- The identity permutation is the identity matrix. -/
theorem permMat_one {A : Type} [DecidableEq A] :
    (permMat R (Equiv.refl A) : Matrix A A R) = 1 := by
  ext a b; simp [permMat, Matrix.one_apply]

/-- `permMat` turns `Equiv` composition into matrix multiplication. -/
theorem permMat_trans {A B C : Type} [Fintype B] [DecidableEq B] [DecidableEq C]
    (e : A ≃ B) (e' : B ≃ C) :
    (permMat R (e.trans e') : Matrix A C R) = permMat R e * permMat R e' := by
  ext a c; rw [permMat_mul]; simp [permMat, Equiv.trans_apply]

/-- `permMat` turns the product of equivs into the Kronecker product. -/
theorem permMat_kron {A B C D : Type} [DecidableEq B] [DecidableEq D]
    (e : A ≃ B) (e' : C ≃ D) :
    ((permMat R e) ⊗ₖ (permMat R e') : Matrix (A × C) (B × D) R)
      = permMat R (e.prodCongr e') := by
  ext i j
  obtain ⟨a, c⟩ := i; obtain ⟨b, d⟩ := j
  simp only [permMat, kronecker_apply, Equiv.prodCongr_apply, Prod.map_apply, Prod.mk.injEq]
  by_cases h1 : e a = b <;> by_cases h2 : e' c = d <;> simp [h1, h2]

/-! ### The naturality laws (associator, unitors, braiding) -/

theorem mat_assoc_nat {X X' Y Y' Z Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']
    (f : Matrix X X' R) (g : Matrix Y Y' R) (h : Matrix Z Z' R) :
    ((f ⊗ₖ g) ⊗ₖ h) * permMat R (Equiv.prodAssoc X' Y' Z')
      = permMat R (Equiv.prodAssoc X Y Z) * (f ⊗ₖ (g ⊗ₖ h)) := by
  ext i j
  obtain ⟨⟨x, y⟩, z⟩ := i; obtain ⟨x', y', z'⟩ := j
  rw [mul_permMat, permMat_mul]
  simp only [kronecker_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply, mul_assoc]

theorem mat_lu_nat {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : Matrix X Y R) :
    ((1 : Matrix PUnit PUnit R) ⊗ₖ f) * permMat R (Equiv.punitProd Y)
      = permMat R (Equiv.punitProd X) * f := by
  ext i j
  obtain ⟨u, x⟩ := i
  rw [mul_permMat, permMat_mul]
  simp [kronecker_apply, Equiv.punitProd, Matrix.one_apply]

theorem mat_ru_nat {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : Matrix X Y R) :
    (f ⊗ₖ (1 : Matrix PUnit PUnit R)) * permMat R (Equiv.prodPUnit Y)
      = permMat R (Equiv.prodPUnit X) * f := by
  ext i j
  obtain ⟨x, u⟩ := i
  rw [mul_permMat, permMat_mul]
  simp [kronecker_apply, Equiv.prodPUnit, Matrix.one_apply]

theorem mat_braid_nat {X X' Y Y' : Type}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']
    (f : Matrix X X' R) (g : Matrix Y Y' R) :
    (f ⊗ₖ g) * permMat R (Equiv.prodComm X' Y')
      = permMat R (Equiv.prodComm X Y) * (g ⊗ₖ f) := by
  ext i j
  obtain ⟨x, y⟩ := i; obtain ⟨y', x'⟩ := j
  rw [mul_permMat, permMat_mul]
  simp only [kronecker_apply, Equiv.prodComm_apply, Equiv.prodComm_symm, Prod.swap_prod_mk,
    mul_comm]

/-! ### The pure-permutation laws (pentagon, triangle, symmetry, hexagon) -/

theorem mat_pentagon (W X Y Z : Type)
    [Fintype W] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] :
    permMat R (Equiv.prodAssoc (W × X) Y Z) * permMat R (Equiv.prodAssoc W X (Y × Z))
      = ((permMat R (Equiv.prodAssoc W X Y)) ⊗ₖ (1 : Matrix Z Z R)) *
          (permMat R (Equiv.prodAssoc W (X × Y) Z) *
            ((1 : Matrix W W R) ⊗ₖ permMat R (Equiv.prodAssoc X Y Z))) := by
  simp only [← permMat_one, permMat_kron, ← permMat_trans]
  congr 1

theorem mat_triangle (X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    permMat R (Equiv.prodAssoc X PUnit Y) * ((1 : Matrix X X R) ⊗ₖ permMat R (Equiv.punitProd Y))
      = (permMat R (Equiv.prodPUnit X)) ⊗ₖ (1 : Matrix Y Y R) := by
  simp only [← permMat_one, permMat_kron, ← permMat_trans]
  congr 1

theorem mat_braid_symm (X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    permMat R (Equiv.prodComm X Y) * permMat R (Equiv.prodComm Y X) = (1 : Matrix (X × Y) (X × Y) R) := by
  simp only [← permMat_one, ← permMat_trans]
  congr 1

theorem mat_hexagon (X Y Z : Type)
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] :
    permMat R (Equiv.prodAssoc X Y Z) *
        (permMat R (Equiv.prodComm X (Y × Z)) * permMat R (Equiv.prodAssoc Y Z X))
      = ((permMat R (Equiv.prodComm X Y)) ⊗ₖ (1 : Matrix Z Z R)) *
          (permMat R (Equiv.prodAssoc Y X Z) *
            ((1 : Matrix Y Y R) ⊗ₖ permMat R (Equiv.prodComm X Z))) := by
  simp only [← permMat_one, permMat_kron, ← permMat_trans]
  congr 1

/-! ### The instance -/

/-- **The matrix model is a coherent traced symmetric monoidal category.** The literal physics
model satisfies the full monoidal-coherence layer, the structural isos being permutation
matrices. -/
def matCoherentTracedSMC : CoherentTracedSMC.{1, 0} :=
  { toTracedSMC := matTracedSMC (R := R)
    assoc_nat := fun f g h => mat_assoc_nat f g h
    lu_nat := fun f => mat_lu_nat f
    ru_nat := fun f => mat_ru_nat f
    pentagon := fun W X Y Z => mat_pentagon W.carrier X.carrier Y.carrier Z.carrier
    triangle := fun X Y => mat_triangle X.carrier Y.carrier
    braid_nat := fun f g => mat_braid_nat f g
    braid_symm := fun X Y => mat_braid_symm X.carrier Y.carrier
    hexagon := fun X Y Z => mat_hexagon X.carrier Y.carrier Z.carrier }

end RelExist.MatrixModel
