/-
# Deriving `reg` from the dynamics: registration is absorption

The limits-of-knowing obstruction [`Relating.no_complete_view`](../RelExist/Relating.lean) *consumes*
a registration map `reg : (O → View) → O` — "every view of the self is itself one of the self's
relata" — and **posits** it as the A2 reading ("viewing is relating"). The open frontier
([03.4](../../docs/spec/03.4-limits-of-knowing.md)) is to **derive** that map from the co-directed
dynamics `Φ_c`, rather than assume it: to identify the lattice-level *standing-absorption* proved in
[`Attention.closed_loop_registers`](Attention.lean) with the `Type`-level `reg`.

This module takes the step. The recognition that makes it honest: **Lawvere's diagonal uses nothing
of `reg`** (`no_complete_view` holds for *any* `reg`). So "deriving `reg`" is not about giving it a
property the diagonal needs — it is about showing the map is **realized by the dynamics** rather than
stipulated: that each view genuinely *registers* as a relatum, with its standing absorbed into the
self.

* `Registering` — the **dynamical A2-closure** as a structure: every view names a relatum whose
  co-directed loop with the self *closes* (the self relates to it and it relates back). This replaces
  the opaque `reg` with a single, motivated commitment about the coupling `c`: *viewing the self is a
  mutual relating with the self.*
* `reg_absorbs` — **registration is absorption, not bookkeeping** `[proved]`: for a registering
  view-system, each view's relatum has its sustained standing *identified with the self's*, by
  `closed_loop_registers`. The `reg` is dynamically real — the viewer is pulled into the self by
  `Φ_c`'s closed loop, a theorem of the operator.
* `no_complete_view_of_registering` — **the obstruction, with `reg` derived** `[proved]`: a
  registering self has no complete view, the registration map fed to the diagonal being the dynamical
  `reg`, justified by `reg_absorbs`.

**What is discharged, and what remains.** Discharged: the Type-level `reg` is now accompanied by a
proof that it is a genuine `Φ_c`-registration (standing-coincidence in the `gfp`), tying the two
settings the spec flagged. Still posited (the irreducible A2 commitment): that every view *names a
relatum at all* and that its loop *closes* — the `reg`/`closes` fields of `Registering`. We have
reduced "an opaque `reg` exists" to "viewing closes a co-directed loop," and proved that this, via
the operator, *is* absorption. Deriving loop-closure itself from a still-deeper account of "viewing
is relating" is the residue.
-/
import Scratch.Attention
import RelExist.Relating

namespace RelExist.Registration

open RelExist.Relating RelExist.Attention

universe u v w
variable {V : Type u} {α : Type v} [CompleteLattice α] {View : Type w}

/-- **The dynamical A2-closure, as a structure.** With the self the vertex `s`, a `Registering`
view-system says every view `w : V → View` *registers*: it names a relatum `reg w : V` whose
co-directed loop with the self **closes** — `s` relates to it (`c s (reg w)`) and it relates back
(`c (reg w) s`). This is "viewing the self is a mutual relating with the self," made a hypothesis
about the coupling `c` rather than an opaque `reg`. -/
structure Registering (c : V → V → Prop) (s : V) (View : Type w) where
  reg    : (V → View) → V
  closes : ∀ w, c s (reg w) ∧ c (reg w) s

/-- **Registration is absorption, not bookkeeping.** For a registering view-system, each view's
relatum has its sustained standing *identified with the self's* — by `closed_loop_registers`. So the
`reg` map is dynamically real: the viewer is absorbed into the self (`Φ_c`'s closed loop forces the
two standings to coincide), not merely stipulated to be a relatum. -/
theorem reg_absorbs (c : V → V → Prop) (s : V) (R : Registering c s View) (w : V → View) :
    sustainedField (α := α) c (R.reg w) = sustainedField c s :=
  closed_loop_registers (α := α) c (R.closes w).2 (R.closes w).1

/-- **No complete self-view — with `reg` derived from the dynamics.** Given a registering view-system
(the dynamical A2-closure on `c`) and any fixed-point-free `neg` on views, the self has no complete
view. The registration map fed to Lawvere's diagonal is the dynamical `R.reg` — justified by
`reg_absorbs` as a genuine `Φ_c`-registration — rather than the opaque posit of `no_complete_view`.
*Knowing requires relating; the closed loop of relating absorbs the knower into the known; the
diagonal does the rest.* -/
theorem no_complete_view_of_registering
    (c : V → V → Prop) (s : V) (R : Registering c s View)
    (neg : View → View) (hneg : ∀ x, neg x ≠ x) :
    ¬ ∃ v : V → View, ∀ w : V → View, v (R.reg w) = w (R.reg w) :=
  no_complete_view R.reg neg hneg

end RelExist.Registration
