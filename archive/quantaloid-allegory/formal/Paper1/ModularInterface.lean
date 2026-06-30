/-
# The modular-theory interface (handoff I.VI)

A clean, **cited** interface bundling the established **Tomita–Takesaki / modular** substrate as assumed
axiom-fields. We do **not** mechanize Tomita–Takesaki; we name it, on an inspectable floor, and prove paper
one's **novel relational** results on top of it (`ModularBuild`).

## THE INTEGRITY TEST (the whole point of this file)

> **Every field below must pass:** *would a Tomita–Takesaki textbook state this **without ever using the
> words "relation", "self", "attention", or "co-direction"?*** If not, it is **relational content that must be
> proved, not assumed**, and it does **not** belong here. Assuming a relational fact would be assuming our
> conclusion — the one fatal error. Each field is operator-algebra substrate only, with a citation. **No field
> mentions relations, selves, attention, or co-direction.** (Audited: see `spec/07-interface.md`.)

Citations: Takesaki, *Theory of Operator Algebras* I/II; Bratteli–Robinson, *Operator Algebras and Quantum
Statistical Mechanics* I/II; Haag–Hugenholtz–Winnink (KMS); Connes (type III classification).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Paper1

/-- A **one-parameter group** of transformations: `α 0 = id` and `α (s+t) = α s ∘ α t`. (Purely structural;
no relational content.) -/
def IsOneParam {M : Type*} (α : ℝ → (M → M)) : Prop :=
  α 0 = id ∧ ∀ s t, α (s + t) = α s ∘ α t

/-- **The modular-theory interface.** Standard operator-algebra data and theorems for a von Neumann algebra
`M` with a faithful normal state, **assumed** here (constructed by Tomita–Takesaki elsewhere). Every field is
textbook operator algebra; **none is relational.** -/
class ModularInterface (M : Type*) where
  /-- The **modular automorphism group** `σ_t` (Tomita's theorem *constructs* it from a faithful normal state;
  here it is **assumed** as data). Takesaki I, Ch. VI; Bratteli–Robinson I §2.5. -/
  sigma : ℝ → (M → M)
  /-- `σ` is a one-parameter group of `*`-automorphisms. Takesaki I, Thm VI.1.19. -/
  sigma_oneParam : IsOneParam sigma
  /-- The **KMS condition** for a one-parameter group w.r.t. the faithful normal state. The analytic boundary
  condition of thermal equilibrium. Haag–Hugenholtz–Winnink; Bratteli–Robinson II §5.3. (Predicate assumed;
  its analytic content is the cited definition.) -/
  KMSfor : (ℝ → (M → M)) → Prop
  /-- The modular group **satisfies KMS** for the state (`σ` is the equilibrium dynamics). Takesaki II, Thm
  VIII.1.2; Bratteli–Robinson II, Prop 5.3.7. -/
  sigma_kms : KMSfor sigma
  /-- **Modular uniqueness — the lever.** Any one-parameter automorphism group satisfying the KMS condition
  for the state **equals** the modular group. (A KMS dynamics is forced to be the modular flow.) Takesaki II,
  Thm VIII.1.2 / the modular characterisation; Bratteli–Robinson II, Thm 5.3.10. -/
  kms_unique : ∀ α, IsOneParam α → KMSfor α → α = sigma
  /-- **Complete passivity** of the state w.r.t. a one-parameter group — the thermodynamic equilibrium
  condition (no work extractable by cyclic processes, in all tensor powers). Pusz–Woronowicz. (Predicate
  assumed; its content is the cited definition.) -/
  CompletelyPassive : (ℝ → (M → M)) → Prop
  /-- **Passivity ⇒ KMS — the Pusz–Woronowicz lever.** A one-parameter group for which the state is
  completely passive satisfies the KMS condition. This lets an *equilibrium* (passive) dynamics inherit KMS,
  hence (with `kms_unique`) be forced to the modular flow. Pusz–Woronowicz, *Passive states and KMS states*,
  Comm. Math. Phys. 58 (1978). -/
  passive_kms : ∀ α, IsOneParam α → CompletelyPassive α → KMSfor α
  /-- **The Tomita–Takesaki precondition:** `M` admits a **cyclic and separating vector** (equivalently, a
  faithful normal state). Takesaki II, Ch. VI; the GNS standard form. (Stated as the proposition that the
  precondition holds.) -/
  cyclicSeparating : Prop
  /-- …and it holds. -/
  cyclicSeparating_holds : cyclicSeparating
  /-- **The type II∞ core** of the Takesaki continuous decomposition `M ≅ N ⋊_θ ℝ`. Takesaki II, Ch. XII;
  Connes' classification. (Fixed at `Type` to keep the interface universe-monomorphic.) -/
  Core : Type
  /-- The **semifinite trace** on the core (the core is type II∞, so this exists — unlike on `M`). -/
  traceN : Core → ℝ
  /-- The **dual (trace-scaling) flow** `θ_s` on the core. Takesaki duality, Takesaki II §XII.1. -/
  theta : ℝ → (Core → Core)
  /-- `θ` is a one-parameter group. -/
  theta_oneParam : IsOneParam theta
  /-- **The trace-scaling law** `τ_N ∘ θ_s = e^{−s} · τ_N` — the dual flow scales the core trace; the trace is
  *not* invariant. This non-conservation is the structural fact paper one reads as the arrow of time. Takesaki
  II, Thm XII.1.1 (the dual weight scales). -/
  trace_scaling : ∀ (s : ℝ) (n : Core), traceN (theta s n) = Real.exp (-s) * traceN n

end Paper1
