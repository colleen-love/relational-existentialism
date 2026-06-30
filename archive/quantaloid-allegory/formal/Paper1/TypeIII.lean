/-
# Type III — what ports, and the equilibrium entry to the KMS test (handoff I.V)

`Q` is moved to the **hyperfinite type III₁ factor** (the type whose defining trace-*lessness* matches the
limits-of-knowing — the accounting that never closes; see `spec/06-type-III-modular.md`). This file mechanizes
the part that **survives the move**: the `τ`-free results of I.III/I.IV port **unchanged**, because they were
stated over an abstract `[CompleteLattice Q]` — which the **projection lattice of a type III factor**
instantiates (every von Neumann algebra has a complete projection lattice; type III only removes the *global
trace*, not the lattice).

The operator-algebra heart of I.V — the modular flow `σ_t`, KMS, Tomita–Takesaki, Takesaki duality — is **not
in mathlib** and is **not faked here** (Part D of the verdict doc). What *is* mechanizable is the structural
entry point: the derived self is an **equilibrium** of the co-direction dynamics, which is exactly the
hypothesis the KMS-uniqueness lever consumes.
-/
import Paper1.Existence
import Paper1.Seam
import Paper1.TraceSeam

namespace Paper1.TypeIII

variable {Q : Type*} [CompleteLattice Q] {A : Type*}

/-! ## Part A — the `τ`-free results port to type III

These are **not re-proved**; they are the *same* theorems, re-stated over the type III value-object to make
the "survives" claim concrete and checked. The proofs invoke only the complete lattice — never a trace — so
the absence of a global trace in type III costs them nothing. -/

/-- **Existence survives.** A fixed self-relation still exists on the type III projection lattice (relational
Knaster–Tarski needs only completeness). -/
theorem self_exists_typeIII (Φ : Dynamics Q A) :
    Φ (OrderHom.gfp Φ) = OrderHom.gfp Φ :=
  self_exists Φ

/-- **The feedback trace survives.** `Tr` (= D1) was proved `τ`-free in I.IV (join-contraction, lattice only),
so it is untouched by the loss of the global trace. (Witness: `Paper1.TraceSeam.ptrace` and its axioms are
stated over `[CompleteLattice Q]`.) -/
theorem feedback_trace_typeIII (R : Rel Q (A × A) (A × A)) :
    Paper1.TraceSeam.ptrace R = fun a b => ⨆ u, R (a, u) (b, u) := rfl

/-- **The seam survives** (Lawvere; 0 axioms; arena-independent — nothing about `Q` enters). Restated for the
type III value-object. -/
theorem seam_typeIII {B : Type*} (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ g : A → A → B, Paper1.Seam.PointSurjective g :=
  Paper1.Seam.reflexive_opacity f hf

/-! ## The equilibrium entry to the KMS test

The KMS-uniqueness lever (Part C, step 2) consumes an **equilibrium** state: *a faithful normal state that is
stationary for a flow is KMS for that flow, and KMS forces the flow to be the modular one.* The first half of
that hypothesis — stationarity — is exactly the existence theorem. -/

/-- A self-relation is an **equilibrium** (stationary point) of the co-direction dynamics. -/
def IsEquilibrium (Φ : Dynamics Q A) (R : SelfRel Q A) : Prop := Φ R = R

/-- **The derived self is an equilibrium.** This is the KMS test's entry hypothesis, mechanized: the self is
stationary for the co-direction dynamics. Whether that stationarity is a *KMS* equilibrium — and so forces the
generator to be the modular Hamiltonian — is the operator-level question of `06-type-III-modular.md`, blocked
on the mathlib type III gap. -/
theorem self_isEquilibrium (Φ : Dynamics Q A) : IsEquilibrium Φ (OrderHom.gfp Φ) :=
  self_exists Φ

end Paper1.TypeIII
