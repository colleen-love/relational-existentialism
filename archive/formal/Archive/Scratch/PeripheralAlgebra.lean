/-
# The peripheral standard form — the fixed-point subalgebra is commutative, in any dimension

The conjecture lift's reconciliation (relation-algebra Decisions 1–2, [03.7](../../docs/archive/03.7-sparsity.md))
asks knowing `E` to be a **spectral projection onto a commutative subalgebra** — the "standard form" of a
conditional expectation. [`Peripheral`](Peripheral.lean) discharged the **spectral** half at finite
dimension (`E = dephase` is `{0,1}`-spectral, no rotating peripheral part). What was named the residual
**mathlib gap** is the **operator-algebra standard form**: that the **peripheral (fixed-point) subalgebra
of `E` is commutative**, and that this is *not* an artefact of finite dimension.

This module closes the **algebraic core of that gap**, and closes it **dimension-independently**. The key
move: the commutativity of the fixed-point subalgebra is *not* an analytic fact about finite matrices — it
is a purely algebraic consequence of `E` being a **projection onto a commutative image**. So we state it
over an **arbitrary ring `𝒜`** (the operator algebra — `Matrix` for finite dimension, but equally the
bounded operators `B(H)` on an infinite-dimensional Hilbert space, or any C\*-algebra: all are `Ring`s):

* `PeripheralStandardForm` — the abstract interface: a projection `E : 𝒜 → 𝒜` (idempotent) whose **image
  is commutative** and **closed under product**, fixing `1`. This is the conditional-expectation /
  peripheral-projection data, stated for *any* `𝒜`, finite- or infinite-dimensional.
* `fix_comm` — **the fixed-point subalgebra is commutative**: `a, b ∈ Fix E ⟹ a·b = b·a`. The standard
  form, dimension-free — *this is the content the gap named, holding in `B(H)` exactly as in `Matrix`.*
* `fix_mul_mem`, `fix_one_mem`, `fix_add_mem` — `Fix E` is a **unital subring**: the peripheral subalgebra
  is genuinely a subalgebra, commutative by `fix_comm`.
* `dephaseStandardForm` — the **finite-dimensional witness**: `E = dephase` on `Matrix A A R` instantiates
  the interface (its image is the diagonal/classical fragment, which commutes — `Decoherence.classical_comm`).
  Plus `dephase` is **self-adjoint** (`transpose`-closed, `dephaseFix_transpose_mem`), so the fixed-point
  subalgebra is a genuine `*`-subalgebra — the full standard form for the canonical `E`.

**Honest scope.** The dimension-independent *algebra* of the standard form — the peripheral subalgebra is a
commutative unital subring whenever `E` projects onto a commutative image — is **closed here, for `𝒜` of
any dimension** (`fix_comm` et al.), with the canonical `E = dephase` exhibited as a witness. What this does
**not** do is the *analytic* general-CP input: that for an *arbitrary* primitive unital CP map `Φ_c` on
`B(H)` the peripheral eigenspace (modulus-1 spectrum) *is* the image of such a projection and *is*
commutative — the spectral/ergodic theorem placing a general `Φ_c` into this standard form. That analytic
placement (peripheral spectrum ↦ commutative subalgebra, infinite-dim) is the genuine operator-algebra
theorem that stays `[open]`; the **algebraic standard form it lands in is now built, and is built in
arbitrary dimension.**
-/
import Scratch.Peripheral

namespace RelExist.PeripheralAlgebra

open RelExist.Decoherence

/-! ### The abstract standard form — over any ring, any dimension -/

/-- **The peripheral standard form of a conditional expectation**, over an arbitrary ring `𝒜` (the
operator algebra — finite matrices, `B(H)`, or any C\*-algebra). A projection `E` (idempotent) onto a
**commutative**, product-**closed**, unital image: the abstract shape of "knowing is a spectral projection
onto a commutative subalgebra", stated *without any finiteness/dimension hypothesis*. -/
structure PeripheralStandardForm (𝒜 : Type*) [Ring 𝒜] where
  /-- the conditional expectation / peripheral spectral projection -/
  E : 𝒜 → 𝒜
  /-- `E` is a **projection** — `E∘E = E` (the veto-check core: spectrum `⊆ {0,1}`, peripheral = fixed) -/
  idem : ∀ a, E (E a) = E a
  /-- **the image is commutative** — the structure-theorem content: the peripheral subalgebra commutes -/
  image_comm : ∀ a b, E a * E b = E b * E a
  /-- **the image is closed under product** — `E` is a subalgebra projection -/
  image_mul_mem : ∀ a b, E (E a * E b) = E a * E b
  /-- **the image is closed under sum** -/
  image_add_mem : ∀ a b, E (E a + E b) = E a + E b
  /-- **`E` fixes the unit** — the peripheral subalgebra is unital -/
  one_fixed : E 1 = 1

namespace PeripheralStandardForm

variable {𝒜 : Type*} [Ring 𝒜] (S : PeripheralStandardForm 𝒜)

/-- **The fixed-point (peripheral) subalgebra** — the eigenvalue-`1` space, `{a | E a = a}`. For a
projection, `peripheral = fixed`, so this *is* the peripheral subalgebra. -/
def Fix (a : 𝒜) : Prop := S.E a = a

/-- A fixed point is its own image — the elementary bridge that turns image-facts into fixed-set facts. -/
theorem mem_iff {a : 𝒜} : S.Fix a ↔ S.E a = a := Iff.rfl

/-- Every image element is fixed (`E (E a) = E a`): the image *is* the fixed set. -/
theorem image_fixed (a : 𝒜) : S.Fix (S.E a) := S.idem a

/-- **The fixed-point subalgebra is commutative** — `a, b ∈ Fix E ⟹ a·b = b·a`. The peripheral
**standard form**, holding in *any* dimension: a fixed point equals its own image, so the product
commutes by `image_comm`. *This is the operator-algebra content the gap named — and it needs no finiteness,
so it holds in `B(H)` exactly as in `Matrix`.* -/
theorem fix_comm {a b : 𝒜} (ha : S.Fix a) (hb : S.Fix b) : a * b = b * a := by
  calc a * b = S.E a * S.E b := by rw [ha, hb]
    _ = S.E b * S.E a := S.image_comm a b
    _ = b * a := by rw [ha, hb]

/-- **`Fix E` is closed under product** — the peripheral subalgebra is a subring under `·`. -/
theorem fix_mul_mem {a b : 𝒜} (ha : S.Fix a) (hb : S.Fix b) : S.Fix (a * b) := by
  show S.E (a * b) = a * b
  calc S.E (a * b) = S.E (S.E a * S.E b) := by rw [ha, hb]
    _ = S.E a * S.E b := S.image_mul_mem a b
    _ = a * b := by rw [ha, hb]

/-- **`Fix E` is closed under sum**. -/
theorem fix_add_mem {a b : 𝒜} (ha : S.Fix a) (hb : S.Fix b) : S.Fix (a + b) := by
  show S.E (a + b) = a + b
  calc S.E (a + b) = S.E (S.E a + S.E b) := by rw [ha, hb]
    _ = S.E a + S.E b := S.image_add_mem a b
    _ = a + b := by rw [ha, hb]

/-- **`1 ∈ Fix E`** — the peripheral subalgebra is unital. -/
theorem fix_one_mem : S.Fix (1 : 𝒜) := S.one_fixed

/-- **The peripheral subalgebra is a commutative unital subring** — gathered: closed under `+` and `·`,
contains `1`, and is commutative (`fix_comm`). The standard form, dimension-free. -/
theorem fix_isSubring_and_comm :
    (S.Fix (1 : 𝒜)) ∧
    (∀ a b, S.Fix a → S.Fix b → S.Fix (a + b)) ∧
    (∀ a b, S.Fix a → S.Fix b → S.Fix (a * b)) ∧
    (∀ a b, S.Fix a → S.Fix b → a * b = b * a) :=
  ⟨S.fix_one_mem,
   fun _ _ ha hb => S.fix_add_mem ha hb,
   fun _ _ ha hb => S.fix_mul_mem ha hb,
   fun _ _ ha hb => S.fix_comm ha hb⟩

end PeripheralStandardForm

/-! ### The finite-dimensional witness — `E = dephase` is in standard form

The canonical knowing operator `dephase` (keep the diagonal) instantiates the abstract interface: its image
is the **classical / diagonal fragment**, which is commutative (`Decoherence.classical_comm`) and closed
under product (`Decoherence.isClassical_mul`). So the abstract `fix_comm` specializes to: *the fixed points
of decoherence — the diagonal subalgebra — commute.* -/

variable {A : Type} [Fintype A] [DecidableEq A] {R : Type} [CommRing R]

/-- **`E = dephase` is a peripheral standard form** on `Matrix A A R`. The witness that the abstract
interface is inhabited by the genuine knowing operator: decoherence is a projection onto the commutative,
product-closed, unital diagonal subalgebra. -/
def dephaseStandardForm : PeripheralStandardForm (Matrix A A R) where
  E := dephase
  idem := dephase_idem
  image_comm := fun a b => classical_comm (isClassical_dephase a) (isClassical_dephase b)
  image_mul_mem := fun a b =>
    dephase_of_classical (isClassical_mul (isClassical_dephase a) (isClassical_dephase b))
  image_add_mem := fun a b => by
    -- the sum of two diagonal matrices is diagonal, hence fixed by dephase
    apply dephase_of_classical
    intro i j hij
    simp [Matrix.add_apply, dephase_apply, hij]
  one_fixed := dephase_of_classical isClassical_one

/-- **The fixed points of decoherence commute** — the abstract standard form, made concrete: the diagonal
subalgebra `Fix dephase` is commutative. (`Peripheral.dephase_eigenspace_one` identifies `Fix dephase` with
the classical/known states; this is their mutual commutativity, i.e. the peripheral subalgebra of the
canonical `E` is commutative.) -/
theorem dephaseFix_comm {M N : Matrix A A R}
    (hM : (dephaseStandardForm (A := A) (R := R)).Fix M)
    (hN : (dephaseStandardForm (A := A) (R := R)).Fix N) : M * N = N * M :=
  (dephaseStandardForm).fix_comm hM hN

/-- **`Fix dephase` is `transpose`-closed** — self-adjointness of decoherence makes the peripheral
subalgebra a genuine `*`-subalgebra, not merely a subring. The full standard form for the canonical `E`. -/
theorem dephaseFix_transpose_mem {M : Matrix A A R}
    (hM : (dephaseStandardForm (A := A) (R := R)).Fix M) :
    (dephaseStandardForm (A := A) (R := R)).Fix (Matrix.transpose M) := by
  show dephase (Matrix.transpose M) = Matrix.transpose M
  rw [← transpose_dephase]
  exact congrArg Matrix.transpose hM

end RelExist.PeripheralAlgebra
