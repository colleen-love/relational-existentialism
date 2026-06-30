/-
# The trace seam — does `Tr` (D1's feedback) coincide with `τ` (Q's factor trace)? (handoff I.IV)

**The single gate.** I.III found theorems 3/4/5/7 all wait on a *measure on `Q`*. This file is the Lean half
of settling whether the **categorical feedback trace `Tr`** that D1 requires is the **factor trace `τ`** on
`Q` (the II₁ factor). Full prose verdict: `spec/05-trace-seam.md`.

**The decisive observation, made mechanical here.** The categorical feedback trace contracts the looped wire
by **join** `⨆`, and is **`τ`-free**: `ptrace` below is defined and its trace-axioms proved using **only**
`[CompleteLattice Q]` — it never mentions `τ`. So `Tr` is *not* `τ` (verdict **A** is false on types: `Tr`
is relation-valued and join-contracted; `τ` is ℂ-valued and sum-contracted). What relates them is a
**dimension measure** (`DimensionBridge`) layered on top — verdict **B**, with an **orthogonality side
condition**.
-/
import Paper1.Arena
import Mathlib.Data.Real.Basic

namespace Paper1.TraceSeam

variable {Q : Type*} [CompleteLattice Q] {A B U V : Type*}

/-- **The categorical / feedback partial trace** `Tr^U` D1 requires: loop the `U`-wire of a relation
`A⊗U ⇸ B⊗U` (here `A×U → B×U → Q`) by taking the **join over the diagonal**. Returns a relation `A ⇸ B`.

**`τ`-FREE:** the definition uses only `⨆` (completeness). This is the whole point — the feedback trace needs
no factor trace. -/
def ptrace (R : Rel Q (A × U) (B × U)) : Rel Q A B := fun a b => ⨆ u, R (a, u) (b, u)

/-! ## The trace axioms that do not need the quantale product — proved, `τ`-free.

These are the parts of "looping behaves like looping" that the join-contraction settles on its own. Each uses
only `[CompleteLattice Q]`; none mentions `τ`. -/

/-- **Vanishing I** — tracing the trivial (unit) wire does nothing: `Tr^I(R) = R`. -/
theorem ptrace_unit (R : Rel Q (A × PUnit) (B × PUnit)) (a : A) (b : B) :
    ptrace R a b = R (a, ⟨⟩) (b, ⟨⟩) := by
  simp only [ptrace, iSup_unique]

/-- **Vanishing II** — a compound loop is two loops: `Tr^{U⊗V} = Tr^U ∘ Tr^V` (the join factorises). -/
theorem ptrace_prod (R : Rel Q (A × (U × V)) (B × (U × V))) (a : A) (b : B) :
    ptrace R a b = ⨆ u, ⨆ v, R (a, (u, v)) (b, (u, v)) := by
  simp only [ptrace, iSup_prod]

/-- **The loop is order-indifferent** (the Fubini/superposing content): the two looped indices commute. -/
theorem ptrace_comm (f : U → V → Q) : (⨆ u, ⨆ v, f u v) = ⨆ v, ⨆ u, f u v := iSup_comm

/-! ## Step 3 — the minimal instance: the feedback trace is a JOIN, not a sum. -/

/-- A self-loop on a 2-element wire (`U = Bool`), diagonal `g`. Its feedback trace is the **join** of the
diagonal `g true ⊔ g false` — emphatically **not** a sum. A sum would need a measure (`τ`) turning the join
into addition, which the join itself does not do. -/
theorem ptrace_bool_diagonal (g : Bool → Q) :
    ptrace (A := PUnit) (B := PUnit) (fun p q => if p.2 = q.2 then g p.2 else ⊥) ⟨⟩ ⟨⟩
      = g true ⊔ g false := by
  simp only [ptrace, if_pos, eq_self_iff_true, iSup_bool_eq]

/-! ## The bridge (verdict B): a dimension measure connects `Tr` to numbers. -/

/-- **The bridge the gate needs.** A faithful, additive **dimension measure** on the value-object — the factor
trace `τ` restricted to projections, in the intended II₁ model — turning **orthogonal** joins into numerical
**sums**. This is exactly the structure that connects the `τ`-free feedback trace `ptrace` to the quantitative
content A3/sparsity need.

**Not mechanized as an instance here** (a genuine instance needs the II₁ factor, an open arena seam); the
structure *records the bridge lemma precisely*, including its load-bearing **orthogonality side condition**. -/
structure DimensionBridge (Q : Type*) [CompleteLattice Q] where
  dim : Q → ℝ
  dim_bot : dim ⊥ = 0
  dim_mono : Monotone dim
  /-- additivity on **orthogonal** (disjoint) joins — the side condition that makes the bridge an *equality*
  rather than a submodular inequality. -/
  dim_join_orthogonal : ∀ a b : Q, Disjoint a b → dim (a ⊔ b) = dim a + dim b

/-- **The bridge, worked on the minimal instance.** Given a dimension measure and **orthogonality** of the two
diagonal values, the measure of the feedback trace **is** the sum of the diagonal measures — the join becomes
a sum exactly under the side condition. This is verdict **B** made concrete: `Tr` and `τ` are different
structures that *connect* through `dim`, conditionally. -/
theorem bridge_on_instance (D : DimensionBridge Q) (g : Bool → Q)
    (h : Disjoint (g true) (g false)) :
    D.dim (ptrace (A := PUnit) (B := PUnit)
      (fun p q => if p.2 = q.2 then g p.2 else ⊥) ⟨⟩ ⟨⟩)
      = D.dim (g true) + D.dim (g false) := by
  rw [ptrace_bool_diagonal]
  exact D.dim_join_orthogonal _ _ h

end Paper1.TraceSeam
