/-
# Part 1 — self-reference is irreversible (handoff I.VIII)

**Upstream of the self.** This file isolates the irreversibility of **self-reference** — the diagonal
`reenter S = S ⨾ S` (D1) — with **no self, no selectivity, no interface**: only D1 + completeness, and one
concrete model to witness non-invertibility. The claim under test (settled in `spec/09-arrow.md`) is whether
*this* irreversibility is the arrow of time.

**The sharp form.** The modular flow `σ` is a *group* (extends to `t ∈ ℝ`, reversible). Self-reference is a
*semigroup*: `S ↦ S ⨾ S` composes **forward only** and is **information-losing**, so it **cannot be run
backward**. Here we prove that non-invertibility on the canonical relational model — distinct relations
self-compose to the same relation, so `S` is **not recoverable** from `S ⨾ S`.

**Upstream-of-self audit:** this file uses neither `derivedSelf`/`gfp`-as-self, selectivity, nor the modular
interface. (Grep: no `derivedSelf`, no `ModularInterface`, no selfhood lemmas.)
-/
import Paper1.RaisingDynamics

namespace Paper1.Arrow

/-! ## The canonical relational model: `Q = Prop`, the allegory `Rel`.

Relations are `Prop`-valued (ordinary relations); the value product is conjunction. This is the standard
allegory of sets and relations — the cleanest concrete arena. -/

/-- The value product on `Prop` is conjunction (the allegory `Rel`). Local to this witness. -/
local instance : Mul Prop := ⟨And⟩

@[local simp] lemma mul_prop (a b : Prop) : a * b = (a ∧ b) := rfl

/-- The **identity** relation on `Bool`. -/
def idR : SelfRel Prop Bool := fun a b => a = b

/-- The **swap** relation on `Bool` (`a` relates to `¬a`). -/
def swapR : SelfRel Prop Bool := fun a b => a = !b

/-- Self-composing the identity returns the identity. -/
theorem reenter_idR : reenter idR = idR := by
  funext a c
  cases a <;> cases c <;> simp [reenter, Rel.comp, idR, iSup_bool_eq]

/-- **Self-composing the swap also returns the identity** — the swap's *direction* is destroyed by squaring
(going and coming back is standing still). The information that distinguished `swap` from `id` is **lost**. -/
theorem reenter_swapR : reenter swapR = idR := by
  funext a c
  cases a <;> cases c <;> simp [reenter, Rel.comp, swapR, idR, iSup_bool_eq]

/-- `id` and `swap` are distinct relations. -/
theorem idR_ne_swapR : idR ≠ swapR := by
  intro h
  have h2 := congrFun (congrFun h true) true
  simp [idR, swapR] at h2

/-- **Self-reference is irreversible `[proved, τ-free, no self]`.** `reenter` is **not injective**: the
identity and the swap — two *distinct* relations — self-compose to the **same** relation, so `S` cannot be
recovered from `S ⨾ S`. Self-composition is information-losing; there is **no way back**. This is the precise,
intrinsic directionality of the diagonal — established with neither a self nor a global trace nor the modular
flow. -/
theorem reenter_not_injective :
    ¬ Function.Injective (reenter : SelfRel Prop Bool → SelfRel Prop Bool) := by
  intro hinj
  exact idR_ne_swapR (hinj (reenter_idR.trans reenter_swapR.symm))

/-- **Idempotents are the only fixed points** — the dynamics is forward-only *toward* them, and once there it
stays (a terminal direction). (`reenter E = E ↔ E ⨾ E = E`, by definition; recorded to make the directional
target explicit.) -/
theorem reenter_fixed_iff_idempotent {Q : Type*} [CompleteLattice Q] [Mul Q] {A : Type*}
    (E : SelfRel Q A) : reenter E = E ↔ E ⨾ E = E := Iff.rfl

end Paper1.Arrow
