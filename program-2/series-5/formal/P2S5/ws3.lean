/-
`program-2/series-5/formal/P2S5/ws3.lean`

WS3 - Causation is acyclic (the tower does not return). Program 2 Series 5 (2.5).

The fresh structural causal relation `causalDep attends comp t u := comp u ∧ t ∈ attends u`: `u`, a reified
composite (`comp u`), consumes its constituent `t`. NO rank in the definition (audit b), so its acyclicity is a
PROVED consequence, not a definitional triviality. On the tick carrier `TCar` (`comp := isTick`), `causalDep`
sits inside strict `rankT`-increase (`ws3_causal_rank_lift`, by `decide`: a composite outranks its constituents),
hence has no closed `Relation.TransGen` loop (`ws3_causation_acyclic`, via the general order lemma
`causation_acyclic`). The reified cycle of WS2 spirals up; following causation goes up, never back.

Design docs: `program-2/series-5/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S5.ws2

universe u

namespace P2S5

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## The general order spine (the rank argument) -/

/-- **The rank rises along the transitive closure.** If every edge of `r` strictly raises `rank`, so does every
`Relation.TransGen r` path. -/
theorem transgen_rank_lt {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (h : ∀ a b, r a b → rank a < rank b) :
    ∀ a b, Relation.TransGen r a b → rank a < rank b := by
  intro a b hab
  induction hab with
  | single hr => exact h _ _ hr
  | tail _ hr ih => exact lt_trans ih (h _ _ hr)

/-- **A rank-raising relation has no closed loop.** The order spine of acyclicity. -/
theorem causation_acyclic {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (h : ∀ a b, r a b → rank a < rank b) : ¬ ∃ x, Relation.TransGen r x x := by
  rintro ⟨x, hx⟩
  exact lt_irrefl _ (transgen_rank_lt r rank h x x hx)

/-! ## The fresh structural causal relation -/

/-- **The reification-dependency (the causal relation), built fresh.** `u`, a reified composite (`comp u`),
consumes its constituent `t` (`t ∈ attends u`). The definition does NOT mention rank (audit b). -/
@[reducible] def causalDep {X : Type u} (attends : X → Finset X) (comp : X → Prop) (t u : X) : Prop :=
  comp u ∧ t ∈ attends u

/-! ## The payoffs on the tick carrier -/

/-- **THE RANK-LIFT, PROVED (WS3, audit b).** On the tick carrier the causal relation strictly raises `rankT`: a
reified composite (`isTick u`) outranks every constituent it consumes. Discharged by `decide`, a separate fact
from the definition of `causalDep`. -/
theorem ws3_causal_rank_lift :
    ∀ t u : TCar, causalDep attendsT isTick t u → rankT t < rankT u := by decide

/-- **CAUSATION IS ACYCLIC (WS3).** The reification-dependency on the tick carrier has no closed causal loop: no
`Relation.TransGen (causalDep attendsT isTick)` returns to its origin. From the rank-lift via `causation_acyclic`. -/
theorem ws3_causation_acyclic :
    ¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x :=
  causation_acyclic (causalDep attendsT isTick) rankT ws3_causal_rank_lift

/-- **THE CYCLE CARRIES NO CAUSATION (the coexistence, made load-bearing).** The SAME directed attention cycle
of WS2 (`p0 ⇄ p1`) carries NO causal edge: neither `causalDep attendsT isTick p0 p1` nor `causalDep attendsT
isTick p1 p0` holds, because `p0`, `p1` are base relata (`¬ isTick`), not reified composites. So the loop is
precisely the place causation is NOT: following causation climbs OUT of the loop (up into the composite `kA`)
rather than around it. This is the proven INTERACTION the knot rests on - "the relating loops but time does not"
as a proof term - beyond "a cycle exists" and "causation is acyclic" holding separately. -/
theorem ws2_cycle_not_causal :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1)
  ∧ ¬ causalDep attendsT isTick p0 p1
  ∧ ¬ causalDep attendsT isTick p1 p0 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end P2S5
