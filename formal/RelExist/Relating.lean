/-
# Relating: the topologies of relation, and the obstruction they share

Built only on Lawvere's diagonal ([`RelExist.Mirror`](Mirror.lean), 0 axioms), this isolates
the **difference that self-inclusion makes**. The conversational typology — relating to a
*part* of oneself, to *another*, to the *whole* of oneself, to a *collection containing
oneself* — collapses, for the question "can the relation be completely modelled?", into two
classes by a single criterion: **is the modeller inside the modelled?**

* `disjoint_modelable` — reference **outside** its target (a part you stand outside of; a
  disjoint other) can be modelled completely. There is no diagonal to obstruct it, so the
  seam is **not** about difficulty.
* `self_inclusive_unmodelable` — reference **inside** its target (the whole of yourself; a
  collection that contains you) cannot. This is Lawvere ([T3](../../docs/spec/theorems.md))
  under self-inclusion, and it is exactly the **irreducible seam** of theorem T2: no member
  holds a complete view of a whole it belongs to. It reads equally as "you cannot aim at the
  aimer" — complete *self-direction* of attention is the same obstruction.

So the four topologies are two: *outside ⇒ knowable, inside ⇒ not*, and the boundary is
self-inclusion. The whole of yourself sits on the unknowable side for the *same reason* a
collective does — you cannot get outside the whole you are in.
-/
import RelExist.Mirror

namespace RelExist.Relating

open RelExist.Mirror

universe u v

/-- **Reference outside its target is completely modelable.** When the modelled collection
`Other` is a *different* type from the modeller — a part one stands outside of, or a disjoint
other — a point-surjective complete model exists. The witness is the cheapest possible: let
the modellers *be* the views (`Modeller := Other → View`, `model := id`). The point is its
triviality: modelling an other is *not* hard, so the seam below is **not** about difficulty —
it is about self-inclusion alone. -/
theorem disjoint_modelable {Other : Type u} {View : Type v} :
    ∃ (Modeller : Type (max u v)) (model : Modeller → Other → View),
      ∀ h : Other → View, ∃ m, model m = h :=
  ⟨Other → View, id, fun h => ⟨h, rfl⟩⟩

/-- **Reference inside its target cannot be completely modelled.** When the modelled whole
*contains* the modeller — the same type on both sides — a complete model is a point-surjective
`g : A → (A → B)`, which Lawvere forbids whenever the view-space `B` carries a fixed-point-free
endomap. This is the **seam** (T2): no member holds a complete view of a whole it belongs to;
the missing master perspective is the Lawvere remainder (T3) under self-inclusion. The same
statement, read with `B` as a space of aims, says **complete self-direction of attention is
impossible** — you cannot aim at the aimer. (This is `Mirror.no_complete_selfModel`, framed.) -/
theorem self_inclusive_unmodelable {A : Type u} {B : Type v}
    (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ g : A → A → B, PointSurjective g :=
  no_complete_selfModel f hf

end RelExist.Relating
