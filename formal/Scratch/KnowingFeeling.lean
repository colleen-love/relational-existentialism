/-
# Knowing vs feeling — the T3 contrast, mechanized

[T3](../../docs/spec/03-theorems.md) says the two ways relation turns are different *kinds of
arrow*. The honest, mechanized content is a **type-level asymmetry**, not a proof of
"wholeness":

* *Knowing* is the σ-move, an **endomap** `D → D`; on it the diagonal runs, and it is
  Lawvere-obstructed — it leaves a remainder (`knowing_can_fail_to_close`,
  `no_complete_boolModel`, from [`RelExist.Mirror`](../RelExist/Mirror.lean)).
* *Feeling* is the `≈`-**relation** `D → D → Prop`, living one type-level up. The diagonal
  argument needs an endomap `g a a`; against a *relation* there is no such diagonal to run, so
  the obstruction simply does not typecheck. What is positively provable about `≈` is that it
  is an **equivalence** (here: reflexive) — and *that it is not the kind of arrow the
  σ-obstruction applies to*. We do **not** claim "feeling is whole / global / has no
  remainder": no such absence-of-obstruction is proved, and a universal negative cannot be
  established by one positive property. The asymmetry is in the **types**, and that is enough.
-/
import Scratch.We
import RelExist.Mirror

namespace RelExist.KnowingFeeling

/-- **Knowing can fail to close.** There is a fixed-point-free endomap (here `not` on
`Bool`): a self-map need not be reachable by its own object — the σ-move leaves a
remainder. -/
theorem knowing_can_fail_to_close : ∃ f : Bool → Bool, ∀ b, f b ≠ b :=
  ⟨not, by decide⟩

/-- **No complete self-model, even in one bit.** Because `not` is fixed-point-free,
Lawvere forbids any complete `Bool`-valued self-model of any system `A`: knowing is
structurally partial. -/
theorem no_complete_boolModel {A : Type*} :
    ¬ ∃ g : A → A → Bool, RelExist.Mirror.PointSurjective g :=
  RelExist.Mirror.no_complete_selfModel not (by decide)

/-- **Feeling is reflexive** — the honest positive content of the `≈`-side. The
`≈`-relation, living one level up as a relation `X → X → Prop` rather than an endomap
`X → X`, is reflexive: every state is bisimilar (lived-identical) to itself. This is *not* a
proof of "wholeness"; the real asymmetry with knowing is **type-level** — there is no
diagonal `g a a` to run against a relation, so the Lawvere obstruction that blocks the
σ-move (an endomap) does not even typecheck against `≈`. -/
theorem feeling_is_reflexive {X O : Type*} (obs : X → O) (step : X → X → Prop) (a : X) :
    RelExist.We.bisim obs step a a :=
  RelExist.We.bisim_refl obs step a

end RelExist.KnowingFeeling

