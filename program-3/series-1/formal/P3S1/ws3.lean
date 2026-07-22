/-
`program-3/series-1/formal/P3S1/ws3.lean`

WS3 - The arrow: reversible beneath, irreversible in every observation above. Program 3 Series 1 (3.1).

The pair of facts the series exists for:

- `ws3_micro_loses_nothing`: every transport is injective — the microdynamics destroys no information.
  From Series 3.0's involution.
- `ws3_observation_always_lossy`: for every move, the composite "flow then summarize" is non-injective —
  the loss is permanent, and no amount of further flowing repairs it. Structural: transport bijectivity
  carries the lossy pair through every move.

Together: the arrow is not in the dynamics, which can always be run backward; it is in the summary, which
can never be. Irreversibility emerges from coarse-graining a reversible flow.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S1.ws2

namespace P3S1

open P3S0

set_option linter.unusedVariables false

/-- Every transport is injective: the microdynamics destroys no information. An involution is its own
left inverse. -/
theorem ws3_micro_loses_nothing (x y z : Fin 3) : Function.Injective (transport x y z) :=
  Function.LeftInverse.injective (ws1_moves_reversible x y z)

/-- For every move, the composite "flow then summarize" is non-injective: the summary's loss survives
every further transport. The proof is structural — the transport carries the lossy one-edge pair to a
lossy pair, because it is a bijection and the summary already identified the pair before the move ran. -/
theorem ws3_observation_always_lossy (x y z : Fin 3) :
    ¬ Function.Injective (fun g => summary (transport x y z g)) := by
  intro hinj
  have hpair : summary (transport x y z (transport x y z gFwd))
      = summary (transport x y z (transport x y z gBwd)) := by
    rw [ws1_moves_reversible, ws1_moves_reversible]
    exact ws2_summary_lossy.2
  have := hinj hpair
  exact ws2_summary_lossy.1 (ws3_micro_loses_nothing x y z this)

end P3S1
