/-
# The Conway fixed-point operator on domains — the cartesian trace, by Hasegawa

[`DomainTraced`](DomainTraced.lean) gave only the **scalar** (identity) trace on a complete lattice and
flagged the *interesting* one as open: the **fixpoint trace** on the category of domains, which by
**Hasegawa/Hyland** is the content of "a cartesian category carries a trace **iff** it has a Conway
fixed-point operator." This module builds that operator and proves the **Conway/Bloom–Ésik identities**
— the algebraic heart of the correspondence — on complete lattices via `OrderHom.lfp`.

The cartesian fixpoint trace it underwrites: for `f : A × U →o B × U`,
`Tr(f)(a) := π₁ (f (a, lfp (u ↦ π₂ (f (a, u)))))` — feed the output wire `U` back into the input wire
and take the least fixed point. The trace's JSV axioms reduce, on this definition, exactly to the
identities below (this reduction is the Hasegawa theorem):

* `pfp` / `pfp_fixed` / `pfp_least` — the **parameterized least fixed point** `pfp f a = lfp (f a)` is a
  monotone-in-the-parameter operator; it is a fixed point (`f a (pfp f a) = pfp f a`) and the least one.
  This is the trace's feedback operator.
* `pfp_param_natural` — **naturality in the parameter** (the input-wire naturality of the trace):
  `pfp (f ∘ g) = pfp f ∘ g`.
* `rolling` — the **rolling / dinaturality rule** `lfp (g ∘ h) = g (lfp (h ∘ g))`: the algebraic shadow
  of the trace **sliding** axiom (`trace_slide`). *Not* in mathlib; proved here by mutual fixpoint
  induction. This is the substantive Conway identity.
* `diagonal` — the **Bekić / diagonal rule** `lfp (pfp h) = lfp (h.onDiag)`: tracing two wires equals
  tracing their diagonal — the shadow of `trace_vanish_tens`. (mathlib's `OrderHom.lfp_lfp`, restated in
  the operator's terms.)

**Honest scope.** A rederivation (Conway/Bloom–Ésik iteration-theory identities; the rolling rule is
folklore) with a real mechanization — in particular `rolling`, which mathlib lacks. What remains is the
**categorical packaging**: assembling these into a full `TracedSMC` *instance* on the category of
complete lattices (objects = complete lattices, morphisms = monotone maps, `⊗ = ×`), i.e. discharging
the seven JSV axioms from these identities through the product/projection bookkeeping. That is the
Hasegawa theorem's "only-if" direction in full; the operator and its load-bearing identities are here,
the multi-object `TracedSMC` wrapper is the remaining work. By `ReflexiveModel`'s duality this is the
*construction* side — orthogonal to the seam.
-/
import Mathlib.Order.FixedPoints

namespace RelExist.ConwayTrace

open OrderHom

universe u v
variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]

/-- **The parameterized least fixed point** `pfp f a := lfp (f a)`, monotone in the parameter `a`. This
is the feedback operator of the cartesian fixpoint trace: it solves `b = f a b` for the least `b`,
uniformly in the parameter. -/
def pfp (f : α →o β →o β) : α →o β where
  toFun a := lfp (f a)
  monotone' _ _ h := OrderHom.lfp.monotone (f.monotone h)

@[simp] theorem pfp_apply (f : α →o β →o β) (a : α) : pfp f a = lfp (f a) := rfl

/-- **The feedback is a fixed point.** `f a (pfp f a) = pfp f a`: the parameterized least fixed point
solves the feedback equation. This is the trace's defining "unrolling." -/
theorem pfp_fixed (f : α →o β →o β) (a : α) : f a (pfp f a) = pfp f a :=
  OrderHom.map_lfp (f a)

/-- **The feedback is the least fixed point** (the induction principle, parameterized): any pre-fixed
point `b` of `f a` dominates `pfp f a`. -/
theorem pfp_least (f : α →o β →o β) (a : α) {b : β} (h : f a b ≤ b) : pfp f a ≤ b :=
  OrderHom.lfp_le (f a) h

/-- **Naturality in the parameter.** Precomposing the parameter commutes with the feedback operator:
`pfp (f ∘ g) = pfp f ∘ g`. (The input-wire naturality `trace_nat_left` of the cartesian trace.) -/
theorem pfp_param_natural {γ : Type u} [CompleteLattice γ] (f : α →o β →o β) (g : γ →o α) :
    pfp (f.comp g) = (pfp f).comp g := rfl

/-- **The rolling / dinaturality rule** `lfp (g ∘ h) = g (lfp (h ∘ g))` — the algebraic shadow of the
trace **sliding** axiom: moving a map `h` across the feedback loop past `g`. Proved by mutual fixed-point
induction (each side's fixed point bounds the other). This is the substantive Conway identity, and is not
in mathlib. -/
theorem rolling (g h : α →o α) : lfp (g.comp h) = g (lfp (h.comp g)) := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    show g (h (g (lfp (h.comp g)))) ≤ g (lfp (h.comp g))
    apply g.monotone
    show h (g (lfp (h.comp g))) ≤ lfp (h.comp g)
    exact le_of_eq (OrderHom.map_lfp (h.comp g))
  · have key : lfp (h.comp g) ≤ h (lfp (g.comp h)) := by
      apply OrderHom.lfp_le
      show h (g (h (lfp (g.comp h)))) ≤ h (lfp (g.comp h))
      apply h.monotone
      show g (h (lfp (g.comp h))) ≤ lfp (g.comp h)
      exact le_of_eq (OrderHom.map_lfp (g.comp h))
    calc g (lfp (h.comp g)) ≤ g (h (lfp (g.comp h))) := g.monotone key
      _ = lfp (g.comp h) := OrderHom.map_lfp (g.comp h)

/-- **The Bekić / diagonal rule.** Tracing two wires successively equals tracing their diagonal:
`lfp (pfp h) = lfp (h.onDiag)` — the shadow of `trace_vanish_tens` (trace over `U ⊗ V` = nested traces).
(mathlib's `OrderHom.lfp_lfp`, in the operator's terms.) -/
theorem diagonal (h : α →o α →o α) : lfp (pfp h) = lfp h.onDiag :=
  OrderHom.lfp_lfp h

end RelExist.ConwayTrace
