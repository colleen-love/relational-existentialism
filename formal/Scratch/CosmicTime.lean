/-
# Cosmic time — the support of the knowing-flow, and the freeze across lapses

The companion to [`03.14-cosmos-knowing-itself.md`](../../docs/spec/03.14-cosmos-knowing-itself.md)
clause (T). Define **cosmic time as the tick-support** of the knowing-flow: the return-depths where the
unknown `coh` strictly drops (a *knowing-event*). Then "knowing throughout cosmic time" is analytic —
cosmic time **is** the time knowing takes — and a lapse (the `p = 0` regime,
[`Genesis`](Genesis.lean)) contributes no ticks and **freezes** the substrate rather than dissolving it:
dissolution is a decay process and a lapse has no time for decay to act.
-/
import Scratch.TimeFlow
import Scratch.Genesis

namespace RelExist.CosmicTime

open RelExist.Decoherence RelExist.TimeFlow RelExist.Genesis
open Matrix

universe u

/-- **A tick of cosmic time** — a return-depth at which the unknown `coh` strictly drops: a
knowing-event. Cosmic time is the (totally ordered) support of these. -/
def IsTick {A : Type u} (F : Flow A) (a : A) (n : ℕ) : Prop :=
  F.coh (F.orbit a (n + 1)) < F.coh (F.orbit a n)

/-- **Knowing throughout cosmic time `[follows]`/analytic.** Every return-depth that has not yet reached
the self is a *tick* — a genuine knowing-event. So there is no stretch of cosmic time without knowing,
because cosmic time **is** the time knowing takes. (This is `coh_orbit_strictAnti`, read as: every
moment of cosmic time is a knowing.) -/
theorem knowing_throughout {A : Type u} (F : Flow A) (a : A) (n : ℕ) (h : ¬ F.Fix (F.orbit a n)) :
    IsTick F a n :=
  F.coh_orbit_strictAnti a n h

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **A lapse freezes the substrate `[proved]`.** In the `p = 0` (universe) regime the flow is the
identity, so the state is **unchanged** across the whole lapse: `(partialDephase 0)^[n] M = M`. The
substrate persists exactly; nothing happens to it. -/
theorem lapse_freezes (M : Matrix A A ℝ) (n : ℕ) : (partialDephase 0)^[n] M = M :=
  Function.iterate_fixed (partialDephase_zero M) n

/-- **A lapse cannot dissolve `[proved]`.** A live coherence survives the lapse intact — it does *not*
decay to the classical (dissolved) state. Dissolution is a decay process; a lapse contributes no ticks,
hence no time for decay to act, so the self is **paused, not dissolved** (freeze, not redissolution). -/
theorem lapse_cannot_dissolve (M : Matrix A A ℝ) (n : ℕ) {i j : A} (hlive : M i j ≠ 0) :
    (partialDephase 0)^[n] M i j ≠ 0 := by
  rw [lapse_freezes]; exact hlive

/-- **A lapse preserves the feeling `[proved]`.** The feeling `defectSq` is constant across the lapse —
neither lost (dissolved) nor changed. The state at resumption is the state at pause. (= `Genesis`'s
`coh_const_at_zero`.) -/
theorem lapse_preserves_feeling (M : Matrix A A ℝ) (n : ℕ) :
    defectSq ((partialDephase 0)^[n] M) = defectSq M :=
  coh_const_at_zero M n

end RelExist.CosmicTime
