/-
# The relational arena (handoff I.III)

The new-arena scaffolding: a **quantaloid / allegory** in which a `Q`-valued **relation** is the primitive
arrow. This file fixes the *vocabulary* — relations, converse, composition, the inclusion order — over an
abstract value-object `Q`. It names **no self** (the self is derived; see `Existence`).

**Intended models of `Q`.** `Q = Prop` is the ordinary allegory of sets and relations (the cleanest concrete
model: `*` is `∧`, `⨆` is `∃`). The philosophy's intended `Q` is the **hyperfinite II₁ factor** — self-similar
(`Q ≅ Q ⊗ M₂`) and carrying a native trace/modular flow. That `Q` *is* the II₁ factor, and that its operator
structure matches this order structure, is an **open arena seam** (see `spec/00-domain.md`); we do not assume
it here, so the arena is kept abstract and the quantitative content is flagged where it is needed.
-/
import Mathlib.Order.FixedPoints

namespace Paper1

/-- A `Q`-valued relation `A ⇸ B` — **the primitive arrow**. No carrier underneath: the relation is the
thing. (`abbrev` so the pointwise lattice structure on `A → B → Q` transfers automatically.) -/
abbrev Rel (Q : Type*) (A B : Type*) : Type _ := A → B → Q

namespace Rel
variable {Q : Type*} {A B C : Type*}

/-- **Converse** `R°` — a free involution, **not** identified with `R`. (A1's asymmetry is the statement that
`R` and `R°` may differ.) -/
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

/-- The **modular law** of the allegory (composition / converse / meet compatibility), stated as a predicate
to be *tested*, not assumed — it is one of the arena seams. -/
def ModularLaw (Q : Type*) [CompleteLattice Q] [Mul Q] : Prop :=
  ∀ {A B C : Type} (R : Rel Q A B) (S : Rel Q B C) (T : Rel Q A C),
    (R ⨾ S) ⊓ T ≤ R ⨾ (S ⊓ (R.conv ⨾ T))

end Rel

/-- A **self-relation** is a relation `A ⇸ A`. (D1: self-relation as feedback is the trace of such a
relation; the trace is an arena seam — see `spec/03-theorem-debt.md`.) -/
abbrev SelfRel (Q : Type*) (A : Type*) : Type _ := Rel Q A A

end Paper1
