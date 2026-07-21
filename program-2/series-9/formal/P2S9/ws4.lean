/-
`program-2/series-9/formal/P2S9/ws4.lean`

WS4 - The fork (CONE vs NO-CONE). Program 2 Series 9 (2.9), THE CONE.

The two sides of the fork, both reachable on genuine finite-attention carriers, neither by fiat.
`ws4_cone_reachable`: the local attention `attSlow` has a finite rate (1) and a NON-TRIVIAL cone — some event (`p4`)
strictly outside the depth-1 cone of `p0`. A genuine finite speed: relativity's cone.
`ws4_nocone_reachable`: the total attention `attAll` reifies the whole world in one tick — every event is inside the
depth-1 cone of `p0` (`ws4_nocone_trivial`: the cone is `univ`). No event causally disconnected, no finite speed: the
honest non-relativistic pole (instantaneous reification), reported, not relabelled.

CONE is not built into `ball` (attAll gives the whole world); NO-CONE is not built in (attSlow leaves `p4` outside):
same `rate`, same `ball`, same `dist`, only the directed attention differs. The fork is a fact about which world you
are in.

Design docs: `program-2/series-9/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S9.ws1

namespace P2S9

set_option linter.unusedVariables false

/-- **CONE-REACHABLE (WS4).** The local attention `attSlow` has rate 1 and a non-trivial cone: `p4` lies strictly
outside the depth-1 cone of `p0`. A finite rate, some events inside and some outside — relativity's cone. -/
theorem ws4_cone_reachable : rate attSlow = 1 ∧ (∃ y, y ∉ ball attSlow p0 1) := by
  refine ⟨by decide, ⟨p4, by decide⟩⟩

/-- **NO-CONE-REACHABLE (WS4).** The total attention `attAll` reifies the whole world in one tick: every event is
inside the depth-1 cone of `p0`. No finite speed — the instantaneous, non-relativistic pole. -/
theorem ws4_nocone_reachable : ∀ y, y ∈ ball attAll p0 1 := by
  decide

/-- **THE NO-CONE CONE IS EVERYTHING.** `ball attAll p0 1 = univ`: the cone is the whole world, no elsewhere. -/
theorem ws4_nocone_trivial : ball attAll p0 1 = Finset.univ := by
  decide

end P2S9
