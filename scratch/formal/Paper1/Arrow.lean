/-
# The headline: self-relation generates the irreversibility of time

**The result.** Self-relation — the diagonal `reenter S = S ⨾ S` (D1) — is **irreversible**: it is
**information-losing**, so it **cannot be run backward**. This is the precise, intrinsic sense in which
self-reference has a direction: a reversible flow is a *group* (runs both ways); self-relation is a
*semigroup* (forward only). The whole paper turns on this one theorem, proved on the canonical relational
model with **only `{relations, the diagonal, completeness}`** — no axioms, no self, no operator theory.

**The proof, in one line.** The identity and the swap are **distinct** relations that **self-compose to the
same** relation (the identity) — so the relation that was squared cannot be recovered. *Going and coming back
is standing still; the direction is lost.*

**The honest boundary.** This establishes the arrow's *irreversibility* — that there is a forward-only
direction. It does **not** by itself fix the arrow's *orientation* (which way is the future); that is the
honest open edge (see `spec/02-foundation.md`). We do not overclaim "the arrow of time."
-/
import Paper1.Arena

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
