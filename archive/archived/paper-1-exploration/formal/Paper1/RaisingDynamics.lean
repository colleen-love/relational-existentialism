/-
# Phase 1a — deriving the dynamics from the arena (handoff I.VII)

The demotion of A3 promised: **raising is _derived_, not assumed.** This file discharges the first half (1a):
a **non-trivial monotone dynamics arises on self-relations from D1's composition** (the trace / re-entry),
**interface-free** — it needs neither the modular interface nor a global trace.

**Mechanism (the candidate from the spec).** A self-relation `S : A ⇸ A` **re-enters itself through the
trace** — relating-through-itself, `reenter S = S ⨾ S`. This is a genuine, monotone endo-process; its **fixed
points are the idempotent self-relations** (`S ⨾ S = S` — the projection-like selves), and by relational
Knaster–Tarski a greatest one exists. So the dynamics is real.

**What 1a does _not_ settle (honest scope).** This is the **order/qualitative** dynamics. That it is the
*quantitative* raising (inflationary, capacity-bounded) and that its reversible core is the modular
one-parameter group is **Phase 1b** (needs the measure / the passivity→KMS lever). And note the **minimal-set
finding**: the dynamics' *existence* uses **D1 (composition) + completeness only** — **neither A1 nor A2**.
A1's asymmetry enters later (type III has no symmetric/tracial self); A2 is still not load-bearing in a proof.
-/
import Paper1.Existence
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

namespace Paper1

variable {Q : Type*} [CompleteLattice Q] [Mul Q]
  [CovariantClass Q Q (· * ·) (· ≤ ·)] [CovariantClass Q Q (Function.swap (· * ·)) (· ≤ ·)]
  {A B C : Type*}

/-- **Composition is monotone** (the quantale property: `*` monotone, `⨆` monotone). The order-theoretic
backbone of the re-entry dynamics. -/
theorem comp_mono {R R' : Rel Q A B} {S S' : Rel Q B C}
    (hR : R ≤ R') (hS : S ≤ S') : R ⨾ S ≤ R' ⨾ S' :=
  fun a c => iSup_mono (fun b => mul_le_mul' (hR a b) (hS b c))

/-- **Re-entry through the trace** (D1): a self-relation relating through itself, `S ↦ S ⨾ S`. -/
def reenter (S : SelfRel Q A) : SelfRel Q A := S ⨾ S

/-- Re-entry is monotone, so it is a genuine co-direction **dynamics** (a monotone endo-process on
self-relations). Built from D1's composition alone — **no interface, no A1, no A2**. -/
def reenterHom : Dynamics Q A where
  toFun := reenter
  monotone' := fun _ _ h => comp_mono h h

/-- **Phase 1a — the dynamics exists `[proved, interface-free]`.** The re-entry process has a fixed
self-relation: an **idempotent** self (`S ⨾ S = S`), the greatest one, by relational Knaster–Tarski. The
raising mechanism produces a real dynamics with a real self at its fixed point. -/
theorem reentry_self_exists :
    reenter (OrderHom.gfp (reenterHom (Q := Q) (A := A))) = OrderHom.gfp reenterHom :=
  self_exists reenterHom

/-- The fixed self is **idempotent** — it is its own re-entry. (In the operator reading: a projection /
partial-isometry support — the projection-like self the modular structure lives on.)

**Honest caveat (the selection problem, → Theorem 3).** The *greatest* fixed point is typically **degenerate**
(e.g. `⊤ ⨾ ⊤ = ⊤`, so `gfp = ⊤`, the total "everything-relates" relation). So maximality alone does **not**
pick out the genuine self: the dynamics derives only that selves are **idempotents** (projections), and
*which* idempotent is a genuine self is **selected by the measure** (bounded capacity) — that selection **is**
selectivity / sparsity (Theorem 3). 1a furnishes the candidates; the measure picks the self. -/
theorem reentry_self_idempotent :
    (OrderHom.gfp (reenterHom (Q := Q) (A := A))) ⨾ (OrderHom.gfp reenterHom)
      = OrderHom.gfp reenterHom :=
  reentry_self_exists

end Paper1
