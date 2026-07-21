/-
`program-2/series-10/formal/P2S10/ws1.lean`

WS1 - The tick as a map and its measure (the ground). Program 2 Series 10 (2.10), THE REVERSAL.

Imports its predecessor `P2S8` (reaching `P2S7 / … / P2S0 / P1` transitively) and builds on its transitive API. This
file fixes the SHARED objects of the series, on the IMPORTED carrier and the BUILT measure (audit d), never a fresh
gadget:

- the configuration carrier `Cfg := P2S7.MCar` (= Fin 4; states `e0`, `e0'`, `e1`, `e2`);
- the measure `mu := P2S7.rankM` — the BUILT reification rank, the measure a genuine reversal must PRESERVE;
- the tick `tick x := reifyM {x}` — the BUILT reification map on the singleton pattern (no new dynamics is built).

The tick unfolds (all `decide`/`rfl`): `tick e0 = e1`, `tick e1 = e2`, `tick e0' = e0`, `tick e2 = e0` — a tail `e0'`
feeding a 3-cycle `e0→e1→e2→e0`. WS1 proves the ground non-trivial (`ws1_tick_moves`): the tick genuinely changes the
configuration and RAISES its measure — there is something to reverse.

Design docs: `program-2/series-10/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8

universe u

namespace P2S10

open P2S7

set_option linter.unusedVariables false

/-! ## The shared objects (the imported carrier and the built rank; the built reification tick) -/

/-- The configuration carrier: the imported four-state carrier (`P2S7.MCar = Fin 4`). -/
abbrev Cfg : Type := P2S7.MCar

/-- **THE MEASURE.** The BUILT reification rank (`P2S7.rankM`): `mu e0 = mu e0' = 0`, `mu e1 = 1`, `mu e2 = 2`. The
measure the tick moves and that a genuine reversal must PRESERVE (audit d). Not a fresh or rigged measure. -/
abbrev mu : Cfg → ℕ := P2S7.rankM

/-- **THE TICK.** The BUILT reification map on the singleton pattern: `tick x = reifyM {x}`. Unfolds to
`tick e0 = e1`, `tick e1 = e2`, `tick e0' = e0`, `tick e2 = e0`. No new dynamics — the map under study is the
imported `reifyM`. -/
def tick : Cfg → Cfg := fun x => reifyM {x}

/-! ## Carrier lemmas (all reduce by the kernel; `decide`/`rfl`) -/

lemma tick_e0  : tick e0  = e1 := by decide
lemma tick_e1  : tick e1  = e2 := by decide
lemma tick_e0' : tick e0' = e0 := by decide
lemma tick_e2  : tick e2  = e0 := by decide

/-! ## The payoff -/

/-- **THE TICK MOVES (WS1).** The tick genuinely changes the configuration (`tick e0 = e1 ≠ e0`) and RAISES its
measure at the base relatum (`mu (tick e0) = mu e0 + 1`). There is something to reverse; the ground is non-trivial.
The measure-rise is the content of `P2S7.ws2_tick_raises.1` (`rankM (reifyM {e0}) = rankM e0 + 1`), here discharged
directly by `decide` and cited from the built theorem in WS5 audit (d). -/
theorem ws1_tick_moves :
    tick e0 ≠ e0
  ∧ mu (tick e0) = mu e0 + 1 := by
  refine ⟨by decide, by decide⟩

end P2S10
