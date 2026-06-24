/-
# The two sustained selves, unified — both realize the ν-modality

The order-theoretic self ([`Scratch/Attention.lean`](Attention.lean), `sustainedField = νΦ` by
Knaster–Tarski on a complete lattice) and the quantitative self
([`Scratch/Distribution.lean`](Distribution.lean), `sustained x b` by Banach contraction in a
normed algebra) are **not** the same operator: one is a `sup` (idempotent / max-plus), the other a
`sum` (a ring), with different universal properties — *greatest* fixed point vs *unique* fixed
point. They cannot be made literally one operator.

What they **do** share is the doctrine's [ν-modality](../../docs/spec/00-doctrine.md): each is *the
canonical fixed point of co-directed feedback*. This module makes that precise — a single
interface `CoDirectedSelf` (a feedback operator with a sustained self that is a fixed point), a
theorem proved once over the interface, and **both** sustained selves exhibited as instances. The
irreducible difference — *how* the fixed point is pinned down (greatest, by order; unique, by
contraction) — is recorded honestly: it is the one thing the unification does not erase.
-/
import Scratch.Attention
import Scratch.Distribution

namespace RelExist.Feedback

open RelExist

universe u

/-- **The shared interface.** Co-directed feedback with a sustained self: a carrier `S`, a feedback
operator `feedback : S → S` (the seed combined with one relating onward), and a `self` that is a
**fixed point** of it. This is the operative content of the doctrine's `ν` — a canonical fixed point
of feedback — abstracted away from *which* fixed-point theorem supplies it. -/
structure CoDirectedSelf where
  /-- the field of standings -/
  S : Type u
  /-- co-directed feedback: the seed, with one relating folded back in -/
  feedback : S → S
  /-- the sustained self -/
  self : S
  /-- it is a fixed point of feedback (the eigenform equation) -/
  fixed : feedback self = self

namespace CoDirectedSelf

/-- A genuinely shared consequence, proved **once** for both models: the sustained self is fixed
under *any* number of feedback iterations — the self persists, round after round of relating. -/
theorem self_iterate (M : CoDirectedSelf) (n : ℕ) : M.feedback^[n] M.self = M.self := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, M.fixed]

end CoDirectedSelf

/-- **The order-theoretic model is an instance.** Attention's `sustainedField = νΦ_c` (greatest
fixed point, Knaster–Tarski) realizes the co-directed self. -/
noncomputable def latticeSelf {V : Type*} {α : Type*} [CompleteLattice α] (c : V → V → Prop) :
    CoDirectedSelf :=
  { S := Attention.Field V α
    feedback := Attention.couplingOp c
    self := Attention.sustainedField c
    fixed := Attention.sustainedField_fixed c }

/-- **The quantitative model is an instance.** Distribution's `sustained x b` (unique fixed point,
Banach contraction) realizes the *same* co-directed self — a different operator, the same ν-role. -/
noncomputable def banachSelf {E : Type*} [NormedRing E] [CompleteSpace E] {x : E} (hx : ‖x‖ < 1) (b : E) :
    CoDirectedSelf :=
  { S := E
    feedback := fun s => b + x * s
    self := Distribution.sustained x b
    fixed := (Distribution.sustained_fixed hx b).symm }

/-! ### What the unification does *not* erase

Both instances satisfy `CoDirectedSelf`, and inherit `self_iterate`. But the **universal property**
that pins each fixed point down differs, irreducibly, and cannot be a field of the shared interface:

* `latticeSelf` — the self is the **greatest** fixed point: `Attention.sustainedField_greatest`
  (any self-upholding field `a ≤ Φ a` lies below it). This is an *order* statement; it needs the
  lattice and has no analogue in a bare normed ring.
* `banachSelf` — the self is the **unique** fixed point: `Distribution.sustained_unique`
  (any `s = b + x·s` equals it). This is a *metric/contraction* statement; it needs `‖x‖ < 1` and
  has no analogue in a bare complete lattice.

So the unification is exact at the level of the ν-role (canonical fixed point of co-directed
feedback) and stops exactly there: *greatest-by-order* and *unique-by-contraction* are two
different ways the doctrine's `ν` gets realized, not one. -/

end RelExist.Feedback
