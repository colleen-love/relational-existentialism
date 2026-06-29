/-
# Theorem 1 — Existence (the floor)

**A fixed self-relation of the co-direction dynamics exists** — relational Knaster–Tarski. The co-direction
dynamics is any **monotone** process `Φ` on self-relations (a monotone endo-map on the complete lattice of
relations `A ⇸ A`). Its **greatest fixed point** is a fixed self-relation, and it is the *greatest* one — the
maximal sustained structure, the natural candidate for "the self."

**Axioms invoked (the finding):** *only the arena's completeness.* The proof uses neither A1 (asymmetry) nor
A2 (co-direction) — existence is a fact about the lattice of relations alone. So the floor is clean, and the
content of the axioms must show up *downstream* (in which fixed relation, with what structure), not in whether
one exists. This is the first datum on the minimal axiom set: **existence is free**.
-/
import Paper1.Arena

namespace Paper1

variable {Q : Type*} [CompleteLattice Q] {A : Type*}

/-- The co-direction dynamics on self-relations: a monotone endo-process. (Concrete dynamics derived from the
trace of asymmetric self-relation is theorem 2; here it is abstract — *any* monotone `Φ` suffices for
existence.) -/
abbrev Dynamics (Q : Type*) [CompleteLattice Q] (A : Type*) := SelfRel Q A →o SelfRel Q A

/-- **Theorem 1 (Existence).** Every monotone co-direction process has a fixed self-relation: its greatest
fixed point. -/
theorem self_exists (Φ : Dynamics Q A) : Φ (OrderHom.gfp Φ) = OrderHom.gfp Φ :=
  OrderHom.map_gfp Φ

/-- The derived self is the **greatest** fixed self-relation: any other fixed (indeed, any post-fixed)
relation is below it. The self is the maximal sustained structure. -/
theorem self_greatest (Φ : Dynamics Q A) {R : SelfRel Q A} (hR : R ≤ Φ R) :
    R ≤ OrderHom.gfp Φ :=
  OrderHom.le_gfp Φ hR

/-- Name the derived self. **Not a definition of the self in the signature** — it is the *output* of the
existence theorem, available only once a dynamics `Φ` is given. -/
noncomputable def derivedSelf (Φ : Dynamics Q A) : SelfRel Q A := OrderHom.gfp Φ

theorem derivedSelf_fixed (Φ : Dynamics Q A) : Φ (derivedSelf Φ) = derivedSelf Φ :=
  self_exists Φ

end Paper1
