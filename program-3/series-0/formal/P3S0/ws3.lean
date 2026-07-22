/-
`program-3/series-0/formal/P3S0/ws3.lean`

WS3 - Non-degeneracy: the two-sided wall as a state of the flow, and its reachability. Program 3 Series 0
(3.0), THE FLOW.

The witness discipline, discharged inside the state space of the flow:

- `ws3_wall_is_a_state`: the two-sided wall carrier of Program Review 2-1, `PR2R1.attV` (a leaf and two
  self-loops), is literally a state of `G` — its carrier `V` is `Fin 3`, matching the relata of the flow —
  and the review's three wall facts hold there: plain bisimilarity is not the total relation, a non-constant
  label aligned with the plain structure is recoverable, and a non-constant label across the bisimilar loops
  is a non-recoverable import. The facts enter by bridge to the `PR2R1` theorems; they are not reproved.
- `ws3_wall_reachable`: the wall is not an isolated exhibit. A concrete transport carries it to another state
  of the same capacity class, so the flow passes through the non-degenerate world. Connectivity is the WS4
  reachability; equal capacity follows from WS2's capacity conservation.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0.ws2
import P3S0.ws4

universe u

namespace P3S0

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- The wall state: the two-sided wall carrier of Program Review 2-1, read as a state of `G`. -/
abbrev wall : G := PR2R1.attV

/-- The two-sided wall carrier is literally a state of `G`, and the three wall facts of Program Review 2-1
hold at it: the plain collapse is not total, a non-constant plain-aligned label is recoverable, and a
non-constant label across the bisimilar loops is a non-recoverable import. Bridged to `PR2R1`. -/
theorem ws3_wall_is_a_state (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisim (outDest hinf PR2R1.attV) R ∧ R PR2R1.v1 PR2R1.v0)
  ∧ (PR2R1.labL PR2R1.v0 ≠ PR2R1.labL PR2R1.v1
      ∧ Recoverable (rankLift (outDest hinf PR2R1.attV) PR2R1.labL))
  ∧ (PR2R1.labD PR2R1.v1 ≠ PR2R1.labD PR2R1.v2
      ∧ ¬ Recoverable (rankLift (outDest hinf PR2R1.attV) PR2R1.labD)) :=
  PR2R1.pr2s1_two_sided_wall hinf

/-- The wall state is connected by a transport to another state of its capacity class. The transport
`transport 1 1 0` moves the loop at self `1` from `{1}` to `{0}`, a state distinct from the wall; it is
reached in one round, and capacity conservation (WS2) makes the two states share a capacity vector. The
non-degenerate world is a place the flow passes through. -/
theorem ws3_wall_reachable :
    Connected wall (transport 1 1 0 wall)
  ∧ transport 1 1 0 wall ≠ wall
  ∧ (∀ x, (wall x).card = ((transport 1 1 0 wall) x).card) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    rw [flowReach_one]
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨wall, Finset.mem_singleton_self wall,
        Finset.mem_image.mpr ⟨(1, 1, 0), Finset.mem_univ _, rfl⟩⟩)
  · decide
  · exact fun x => (ws2_capacity_conserved 1 1 0 wall x).symm

end P3S0
