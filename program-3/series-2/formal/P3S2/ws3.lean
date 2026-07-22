/-
`program-3/series-2/formal/P3S2/ws3.lean`

WS3 - The orbits: the flow's reach is exactly the capacity classes. Program 3 Series 2 (3.2), the ledger.

- `ws3_flow_preserves_capacity`: nothing the flow does, over any number of rounds, changes any self's
  capacity;
- `ws3_orbits_are_capacity`: connectivity is exactly capacity equality. One direction is Series 3.0's
  connectivity theorem; the other is the preservation above. The flow's orbits are the capacity classes,
  fully characterized.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2.ws2

namespace P3S2

open P3S0 P3S1

set_option linter.unusedVariables false

/-- Everything the closure reaches keeps the capacity vector of something in the seed set. -/
lemma reach_preserves_cap : ∀ (n : ℕ) (R : Finset G) (h : G),
    h ∈ flowReach n R → ∃ g ∈ R, capVec h = capVec g := by
  intro n
  induction n with
  | zero => intro R h hh; exact ⟨h, hh, rfl⟩
  | succ n ih =>
      intro R h hh
      rw [flowReach_succ] at hh
      obtain ⟨g, hg, hcap⟩ := ih (flowStep R) h hh
      rcases Finset.mem_union.mp hg with hgR | hgM
      · exact ⟨g, hgR, hcap⟩
      · obtain ⟨g0, hg0, hgm⟩ := Finset.mem_biUnion.mp hgM
        obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hgm
        refine ⟨g0, hg0, ?_⟩
        rw [hcap, ← ht]
        funext w
        exact ws2_capacity_conserved t.1 t.2.1 t.2.2 g0 w

/-- The flow never changes any self's capacity, through any number of rounds. -/
theorem ws3_flow_preserves_capacity (g h : G) (hc : Connected g h) : capVec h = capVec g := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨g0, hg0, hcap⟩ := reach_preserves_cap n {g} h hn
  rw [Finset.mem_singleton] at hg0
  rw [hcap, hg0]

/-- The flow's orbits are exactly the capacity classes: two states are connected precisely when every self
has the same capacity in both. The forward direction is the preservation above; the backward direction is
Series 3.0's connectivity theorem. -/
theorem ws3_orbits_are_capacity (g h : G) : Connected g h ↔ capVec g = capVec h := by
  constructor
  · intro hc
    exact (ws3_flow_preserves_capacity g h hc).symm
  · exact ws4_flow_connects g h

end P3S2
