/-
# Relating: the topologies of relation, and the obstruction they share

Built only on Lawvere's diagonal ([`RelExist.Mirror`](Mirror.lean), 0 axioms), this isolates
**what relation does to knowability**. The naive reading is that a *disjoint* other is fully
knowable while only the self / a containing collection is not. But the doctrine's own premises
overturn the naive reading: by **A2** a self *is* its relatings, and (D1, the co-directed form)
relating creates a **between** that constitutes *both* parties. So the moment you actually
relate to another, you share a part with them — they are no longer disjoint, and a part of you
is a part of them.

The corrected picture has **one** knowable case and three unknowable ones:

* `disjoint_modelable` — the only fully knowable target is one you have **no relation to**: a
  part you stand entirely outside of, or a stranger you merely observe. Cold, relationless,
  inert. (The witness is trivial — the point is that knowability is reserved for the
  *relationally empty* limit.)
* `related_other_unmodelable` — **anyone you relate to** is not fully knowable, because the
  other is partly constituted by its relation to you, so completely modelling them would yield
  a complete self-model of you — Lawvere-forbidden. *To know fully you must not relate; to
  relate is to make the other unknowable.*
* `self_inclusive_unmodelable` — the whole of yourself, or a collection that contains you, for
  the same reason: you cannot get outside the whole you are in (this is also T2's irreducible
  seam, and read with the view-space as aims, "you cannot aim at the aimer").

So *all* relation-laden targets are unknowable, by the single obstruction (T3, [Lawvere]),
which reaches the other through the shared between. Knowing-fully and relating are antagonistic.
-/
import RelExist.Mirror

namespace RelExist.Relating

open RelExist.Mirror

universe u v w

/-- **The only fully knowable target is one you have no relation to.** When the modelled
`Other` shares *nothing* with the modeller — a different type, no between — a point-surjective
complete model exists; the witness is the cheapest possible (let the modellers *be* the views).
The triviality is the point: knowability is not hard, it is just *relationless*. Anything you
actually relate to fails this case (see `related_other_unmodelable`). -/
theorem disjoint_modelable {Other : Type u} {View : Type v} :
    ∃ (Modeller : Type (max u v)) (model : Modeller → Other → View),
      ∀ h : Other → View, ∃ m, model m = h :=
  ⟨Other → View, id, fun h => ⟨h, rfl⟩⟩

/-- **A related other is not fully knowable.** To *relate* to another is, by A2, to share a
between that constitutes both — so the modeller `A` is a *part of* the other `O`. We encode
"`A` is part of `O`" as: your own views are recoverable from a complete description of the
other's (`share` is surjective — restriction along the inclusion `A ↪ O`). Then a complete
model of `O` would compose to a **complete self-model of `A`**, which Lawvere forbids whenever
the view-space carries a fixed-point-free endomap. So relating to another imports the
self-inclusion obstruction: *completely knowing someone you relate to would require completely
knowing yourself.* -/
theorem related_other_unmodelable {A : Type u} {O : Type v} {View : Type w}
    (f : View → View) (hf : ∀ v, f v ≠ v)
    (share : (O → View) → (A → View)) (hshare : ∀ h : A → View, ∃ k, share k = h) :
    ¬ ∃ model : A → O → View, ∀ h : O → View, ∃ a, model a = h := by
  rintro ⟨model, hmodel⟩
  have hg : PointSurjective (fun a => share (model a)) := by
    intro h
    obtain ⟨k, hk⟩ := hshare h
    obtain ⟨a, ha⟩ := hmodel k
    exact ⟨a, by show share (model a) = h; rw [ha]; exact hk⟩
  obtain ⟨v, hv⟩ := lawvere _ hg f
  exact hf v hv

/-- **A whole that contains the modeller cannot be completely modelled.** When the modelled
whole *contains* the modeller — the same type on both sides — a complete model is a
point-surjective `g : A → (A → B)`, which Lawvere forbids whenever the view-space `B` carries
a fixed-point-free endomap. This is the **seam** (T2): no member holds a complete view of a
whole it belongs to; the missing master perspective is the Lawvere remainder (T3) under
self-inclusion. Read with `B` as a space of aims it says **complete self-direction is
impossible** — you cannot aim at the aimer. (This is `Mirror.no_complete_selfModel`, framed;
`related_other_unmodelable` is the version that reaches *the other* through the shared between.) -/
theorem self_inclusive_unmodelable {A : Type u} {B : Type v}
    (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ g : A → A → B, PointSurjective g :=
  no_complete_selfModel f hf

end RelExist.Relating
