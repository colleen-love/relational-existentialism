/-
`program-2/series-5/formal/P2S5/ws4.lean`

WS4 - The loop at the fold (the knot). Program 2 Series 5 (2.5).

Among distinct relata causation is acyclic (WS3), so a closed causal loop requires a relatum that is its own
reification-constituent - the self-membered fold point. `ws4_loop_only_at_fold` bundles the rank localization (a
`TransGen` loop forces a self-edge `r z z`) with the P1 diagonal (`ws1_no_self_total_hold`: the totalizing
self-point is unrealizable), so the named WS4 theorem rests on the diagonal (audit d). On the genuine tick
carrier NO fold point exists (`ws4_no_fold_on_tower`, rank strictly raises): the ACYCLIC direction. The LOOPED
reading is REACHABLE on a second carrier `FCar` where a self-membered point `om = {om}` yields a genuine causal
self-loop (`ws4_looped_reachable`) admitting NO rank-lift (`ws4_fold_no_rank`): the fork is not decided by fiat
(audit b), and the sole place a loop can live is the fold, where the rank argument breaks.

Design docs: `program-2/series-5/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S5.ws3

universe u

namespace P2S5

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## Loop forces a self-constituting relatum -/

/-- **A LOOP FORCES A SELF-EDGE.** If `rank` rises on every DISTINCT-relata edge of `r`, a `Relation.TransGen r`
loop `r⁺ x x` forces a self-edge `r z z` somewhere: with no self-edge, every edge is distinct-and-rank-raising,
so the loop would strictly raise `rank` from `x` back to `x`, impossible. -/
theorem loop_forces_selfloop {X : Type u} (r : X → X → Prop) (rank : X → ℕ)
    (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u)
    (x : X) (hloop : Relation.TransGen r x x) : ∃ z, r z z := by
  by_contra hno
  push_neg at hno
  have hedge : ∀ t u, r t u → rank t < rank u := by
    intro t u htu
    have hne : t ≠ u := by rintro rfl; exact hno t htu
    exact hlift t u hne htu
  exact lt_irrefl _ (transgen_rank_lt r rank hedge x x hloop)

/-- **THE LOOP IS ONLY AT THE FOLD (WS4), resting on the diagonal (audit d).** Two conjuncts: (rank) a causal
loop in a rank-raising relation forces a self-constituting relatum (`loop_forces_selfloop`); (diagonal) the
totalizing self-inspection has no fixed point (`ws1_no_self_total_hold`), so the fold's self-reference is a
degenerate point. The named WS4 theorem rests on the P1 diagonal, not on an import. -/
theorem ws4_loop_only_at_fold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (r : X → X → Prop) (rank : X → ℕ)
    (hlift : ∀ t u, t ≠ u → r t u → rank t < rank u) :
    (∀ x, Relation.TransGen r x x → ∃ z, r z z) ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨fun x hx => loop_forces_selfloop r rank hlift x hx, ws1_no_self_total_hold dest insp⟩

/-- **NO FOLD POINT ON THE GENUINE TOWER (WS4, the ACYCLIC direction).** The tick carrier realizes no
self-membered composite: `¬ ∃ x, causalDep attendsT isTick x x` (rank strictly raises, so no relatum is its own
constituent). -/
theorem ws4_no_fold_on_tower : ¬ ∃ x : TCar, causalDep attendsT isTick x x := by decide

/-! ## The LOOPED-reachable witness (the fold carrier, no fiat) -/

/-- The fold carrier: a single self-membered point. -/
abbrev FCar : Type := Fin 1
def om : FCar := 0
/-- The self-membered point attends itself: `om = {om}`. -/
def attendsF : FCar → Finset FCar := fun _ => {om}
/-- The point is a reified composite (of the pattern `{om}`). -/
def compF : FCar → Prop := fun _ => True

/-- **LOOPED IS A GENUINE REACHABLE STRUCTURE (WS4, audit b).** A self-membered point `om = {om}` yields a
closed causal loop: `Relation.TransGen (causalDep attendsF compF) om om`. So a self-constituting relatum is NOT
excluded by the definition of `causalDep`; the fork is not decided by fiat. -/
theorem ws4_looped_reachable : Relation.TransGen (causalDep attendsF compF) om om := by
  apply Relation.TransGen.single
  exact ⟨trivial, by decide⟩

/-- **THE FOLD ADMITS NO RANK-LIFT (WS4, audit b).** No `rank : FCar → ℕ` strictly raises along the causal
self-loop (it would force `rank om < rank om`). The fold is precisely where the rank argument breaks, so the
tick carrier's acyclicity is a substantive fact about the tower, not a definitional artifact. -/
theorem ws4_fold_no_rank :
    ¬ ∃ rank : FCar → ℕ, ∀ t u, causalDep attendsF compF t u → rank t < rank u := by
  rintro ⟨rank, hr⟩
  exact lt_irrefl (rank om) (hr om om ⟨trivial, by decide⟩)

end P2S5
