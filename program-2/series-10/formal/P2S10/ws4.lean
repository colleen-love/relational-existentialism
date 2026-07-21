/-
`program-2/series-10/formal/P2S10/ws4.lean`

WS4 - The fork (RECOVERED-CORE vs NOT-RECOVERED), the knot. Program 2 Series 10 (2.10).

Imports `P2S10.ws3`. Proves the fork on the built tick, neither side by fiat, both against the SAME built rank `mu`.

`ws4_core_reachable`: the criterion is SATISFIABLE — a genuine measure-preserving bijective sub-dynamics EXISTS on the
built rank (the control swap `tickR` has the core `{e0,e0'}`). So the NOT-RECOVERED finding is discriminating, not a
definitional impossibility. `tickR` is a control, NOT the built reification tick.

`ws4_no_core_built`: the BUILT reification tick has NO nonempty measure-preserving bijective sub-dynamics. Its only
bijective sub-dynamics is the 3-cycle `e0→e1→e2→e0`, whose rank reads `0,1,2` and so cannot be preserved; every other
nonempty `D` fails closure or bijectivity. Proved by `decide` over the sixteen subsets of the four-state carrier. The
tick raises the measure at every scale; the arrow is fundamental. This is the pre-registered NOT-RECOVERED headline.

Design docs: `program-2/series-10/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S10.ws3

universe u

namespace P2S10

open P2S7

set_option linter.unusedVariables false

/-- **A CORE IS REACHABLE (WS4, the criterion is not vacuous — audit b).** On the built rank a genuine measure-
preserving bijective sub-dynamics EXISTS: the relabelling swap `tickR` of the two rank-0 states has the core
`{e0, e0'}`. The fork is genuine — the NOT-RECOVERED finding on the built tick is discriminating, not a definitional
impossibility. `tickR` is a control, NOT the built reification tick and NOT an inverse of it. -/
theorem ws4_core_reachable :
    ∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D :=
  ⟨{e0, e0'}, ⟨e0, by decide⟩, by decide⟩

/-- **THE BUILT TICK HAS NO CORE (WS4, the NOT-RECOVERED headline).** For EVERY nonempty `D`, the built reification
tick is NOT a measure-preserving bijection on `D`: no rank-preserving bijective sub-dynamics exists inside it. The one
bijective sub-dynamics (the 3-cycle `e0→e1→e2→e0`) raises the rank on its edges; every other nonempty `D` fails
closure or bijectivity. Proved by `decide` over the sixteen subsets. The tick raises the measure at every scale; the
arrow is fundamental. No inverse is smuggled — the map tested IS the built `tick`. -/
theorem ws4_no_core_built :
    ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D := by
  decide

end P2S10
