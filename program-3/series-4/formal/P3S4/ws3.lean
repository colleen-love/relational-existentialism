/-
`program-3/series-4/formal/P3S4/ws3.lean`

WS3 - Attending is being close. Program 3 Series 4 (3.4), the curve.

For every state, an attended relatum is within distance one: attention is proximity, structurally. This is
the half of the coupling law that holds without any move; WS4 puts it under the dynamics.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S4.ws2

namespace P3S4

open P3S0 P3S1 P3S2 P3S3

set_option linter.unusedVariables false

/-- An attended relatum lies in the one-step ball. -/
lemma mem_ball_one {g : G} {x z : Fin 3} (hz : z ∈ g x) : z ∈ ball g 1 x := by
  unfold ball
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_singleton_self z⟩)

/-- Attending is being close: for every state, an attended relatum is within distance one. -/
theorem ws3_attention_is_proximity (g : G) (x z : Fin 3) (hz : z ∈ g x) :
    flowDist g x z ≤ 1 := by
  unfold flowDist
  split_ifs with h0 h1 h2
  · omega
  · omega
  · exact absurd (mem_ball_one hz) h1
  · exact absurd (mem_ball_one hz) h1

end P3S4
