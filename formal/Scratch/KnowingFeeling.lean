/-
# Knowing vs feeling — the T3 contrast, mechanized

[T3](../../docs/spec/02-axioms.md) says the two ways relation turns are different kinds
of arrow with diverging properties: *knowing* (the σ-move, an endomap, cartesian) is
Lawvere-obstructed — local, leaving a remainder; *feeling* (the `≈`-relation, one level
up) is unobstructed — global, whole. This module states that contrast as theorems,
joining the σ-side ([`RelExist.Mirror`](../RelExist/Mirror.lean)) to the `≈`-side
([`RelExist.We`](We.lean)).
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

/-- **Feeling is whole.** The `≈`-relation, living one level up as a relation rather
than an endomap, is reflexive: every state is observationally identical to itself, with
no remainder. There is no diagonal to obstruct — feeling is global where knowing is
local. -/
theorem feeling_is_whole {X O : Type*} (obs : X → O) (step : X → X → Prop) (a : X) :
    RelExist.We.bisim obs step a a :=
  RelExist.We.bisim_refl obs step a

end RelExist.KnowingFeeling
