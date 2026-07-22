/-
`program-3/series-1/formal/P3S1/ws3.lean`

WS3 - The arrow: reversible beneath, irreversible in every observation above. Program 3 Series 1 (3.1).

The pair of facts the series exists for:

- `ws3_micro_loses_nothing`: every transport is injective — the microdynamics destroys no information.
  From Series 3.0's involution.
- `ws3_observation_always_lossy`: for each single move, the composite "flow then summarize" is
  non-injective. Given 3.0's bijectivity this is equivalent to the summary's own lossiness — stated for
  the record, not as independent content (Program Review 3-1, P3R1-S2).
- `ws3_macro_not_autonomous`: the genuinely dynamical fact, landed from step zero's `check3b` at the
  review's direction — two summary-identical states diverge in summary under the same move, so the macro
  evolution is not a function of the macro state. The summary level cannot carry its own dynamics.

Scope, repaired at Program Review 3-1 (P3R1-S2): what this series proves is observational
non-invertibility over a reversible microdynamics — a many-to-one summary with no decoder, whose loss no
move repairs, and whose level supports no autonomous evolution. No theorem here distinguishes past from
future, and the pre-registered refutation arms were closed before the series was built (`transparent` by
counting, `opaque` by 3.0); the closed-arms disclosure is in the status ledger.

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

/-- For each single move, the composite "flow then summarize" is non-injective. Given 3.0's bijectivity
this is equivalent to the summary's own lossiness; it is stated for the record. The proof carries the
lossy one-edge pair through the move's inverse. -/
theorem ws3_observation_always_lossy (x y z : Fin 3) :
    ¬ Function.Injective (fun g => summary (transport x y z g)) := by
  intro hinj
  have hpair : summary (transport x y z (transport x y z gFwd))
      = summary (transport x y z (transport x y z gBwd)) := by
    rw [ws1_moves_reversible, ws1_moves_reversible]
    exact ws2_summary_lossy.2
  have := hinj hpair
  exact ws2_summary_lossy.1 (ws3_micro_loses_nothing x y z this)

/-- The macro evolution is not a function of the macro state: two summary-identical states diverge in
summary under the same move. The information the summary discards is information its own next step needs
— the summary level supports no autonomous dynamics. (Step zero's `check3b`, landed at Program Review
3-1's direction, P3R1-S2: the series' genuinely dynamical fact.) -/
theorem ws3_macro_not_autonomous :
    summary gFwd = summary gBwd
  ∧ summary (transport 0 1 2 gFwd) ≠ summary (transport 0 1 2 gBwd) := by
  refine ⟨ws2_summary_lossy.2, ?_⟩
  intro h
  have := congrFun (congrFun h 0) 2
  revert this
  decide

end P3S1
