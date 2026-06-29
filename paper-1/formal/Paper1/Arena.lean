/-
# The relational arena

A **quantaloid / allegory** in which a `Q`-valued **relation** is the primitive arrow. This file fixes the
*vocabulary* — relations, converse, composition, the inclusion order — over an abstract value-object `Q`, and
defines **self-relation** and its **re-entry** (the diagonal, D1). It names **no self**.

**The value-object.** `Q = Prop` is the ordinary allegory of sets and relations (the cleanest concrete model:
`*` is `∧`, `⨆` is `∃`) — used to witness the headline result. The philosophy's intended `Q` is the
hyperfinite **type III₁ factor**, chosen by the **seam** (a self whose accounting never closes ⇒ no trace ⇒
type III; see `spec/00-domain.md`). The arena is kept abstract; the headline (`Arrow`) needs only
`{relations, the diagonal, completeness}`.
-/
import Mathlib.Order.FixedPoints

namespace Paper1

/-- A `Q`-valued relation `A ⇸ B` — **the primitive arrow**. No carrier underneath: the relation is the
thing. (`abbrev` so the pointwise lattice structure on `A → B → Q` transfers automatically.) -/
abbrev Rel (Q : Type*) (A B : Type*) : Type _ := A → B → Q

namespace Rel
variable {Q : Type*} {A B C : Type*}

/-- **Converse** `R°` — a free involution, **not** identified with `R`. (The "other end" of a relation; the
operator-world analogue is the modular conjugation `J`.) -/
def conv (R : Rel Q A B) : Rel Q B A := fun b a => R a b

@[simp] theorem conv_conv (R : Rel Q A B) : R.conv.conv = R := rfl

/-- The converse is monotone for the inclusion order. -/
theorem conv_mono [Preorder Q] {R S : Rel Q A B} (h : R ≤ S) : R.conv ≤ S.conv :=
  fun b a => h a b

/-- **Relational composition** `R ; S` — relating through `B`: the join over the intermediary of the two
weights multiplied. Needs only `⨆` (completeness) and a multiplication on `Q`. -/
def comp [CompleteLattice Q] [Mul Q] (R : Rel Q A B) (S : Rel Q B C) : Rel Q A C :=
  fun a c => ⨆ b, R a b * S b c

@[inherit_doc] infixr:62 " ⨾ " => Rel.comp

/-- The **modular law** of the allegory (composition / converse / meet compatibility), stated as a predicate. -/
def ModularLaw (Q : Type*) [CompleteLattice Q] [Mul Q] : Prop :=
  ∀ {A B C : Type} (R : Rel Q A B) (S : Rel Q B C) (T : Rel Q A C),
    (R ⨾ S) ⊓ T ≤ R ⨾ (S ⊓ (R.conv ⨾ T))

end Rel

/-- A **self-relation** is a relation `A ⇸ A`. -/
abbrev SelfRel (Q : Type*) (A : Type*) : Type _ := Rel Q A A

/-- **Self-relation as the trace — the diagonal (D1).** A self-relation **re-enters itself**: `reenter S =
S ⨾ S`, the relation routed back through itself. This is the *one definition* paper one stands on; the
headline is that **it is irreversible** (`Arrow`). -/
def reenter [CompleteLattice Q] [Mul Q] {A : Type*} (S : SelfRel Q A) : SelfRel Q A := S ⨾ S

end Paper1
