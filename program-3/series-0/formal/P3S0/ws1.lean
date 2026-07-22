/-
`program-3/series-0/formal/P3S0/ws1.lean`

WS1 - The ground: the state space, the transport move, and its reversibility. Program 3 Series 0 (3.0),
THE FLOW.

This file is the series boundary import: it imports `PR2R1` (reaching `P2S8` and the whole built arc of
Program 2 transitively) so that the later workstreams can bridge to Program 2's signed increment and to the
two-sided wall. Its own content is the ground of the flow:

- the state space `G` of attention graphs on a three-element carrier, taken whole (512 states);
- the transport move `transport x y z`, a self `x` moving one unit of attention between two targets `y` and
  `z`, a function of the attention alone;
- the two row lemmas that localise the move, and the two headline facts of the ground: every transport is an
  involution on every state (`ws1_moves_reversible`), and a transport changes only the moving self's row and
  acts only when a swap precondition holds (`ws1_move_local`).

The involution is proved structurally, using nothing about `Fin 3`; the step-zero lesson forbids a
whole-space `decide`. Adapted from the compiled de-risk `program-3/spec/derisk/Derisk.lean`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import PR2R1

namespace P3S0

set_option linter.unusedVariables false

/-- The whole universe of the series: every attention graph on three relata. 512 states, taken whole. -/
abbrev G : Type := Fin 3 → Finset (Fin 3)

/-- The transport move: self `x` moves one unit of attention between targets `y` and `z`. If `x` attends `y`
and not `z`, the attention moves to `z`; in the mirror situation it moves back; otherwise nothing happens.
Total on the state space, and a function of the attention alone. -/
def transport (x y z : Fin 3) (g : G) : G := fun w =>
  if w = x then
    if y ∈ g x ∧ z ∉ g x then insert z ((g x).erase y)
    else if z ∈ g x ∧ y ∉ g x then insert y ((g x).erase z)
    else g x
  else g w

/-- The transport rewrites only the moving self's row to the swap value. -/
lemma transport_row (x y z : Fin 3) (g : G) :
    (transport x y z g) x =
      (if y ∈ g x ∧ z ∉ g x then insert z ((g x).erase y)
       else if z ∈ g x ∧ y ∉ g x then insert y ((g x).erase z)
       else g x) := by
  simp [transport]

/-- Every row other than the moving self's is left untouched. -/
lemma transport_other (x y z w : Fin 3) (hw : w ≠ x) (g : G) :
    (transport x y z g) w = g w := by
  simp [transport, hw]

/-- Every transport is an involution, hence a bijection, on every state. The argument is structural: it uses
nothing about `Fin 3`, and so holds on the whole state space without any finite enumeration. -/
theorem ws1_moves_reversible (x y z : Fin 3) (g : G) :
    transport x y z (transport x y z g) = g := by
  funext w
  by_cases hw : w = x
  · subst hw
    set g' := transport w y z g with hg'
    rw [transport_row, hg', transport_row]
    by_cases hA : y ∈ g w ∧ z ∉ g w
    · have hyz : y ≠ z := fun h => hA.2 (h ▸ hA.1)
      rw [if_pos hA]
      have hy' : y ∉ insert z ((g w).erase y) := by
        simp [Finset.mem_insert, Finset.mem_erase, hyz]
      have hz' : z ∈ insert z ((g w).erase y) := Finset.mem_insert_self _ _
      rw [if_neg (fun h => hy' h.1), if_pos ⟨hz', hy'⟩,
          Finset.erase_insert (by simp [Finset.mem_erase]; intro _; exact hA.2),
          Finset.insert_erase hA.1]
    · by_cases hB : z ∈ g w ∧ y ∉ g w
      · have hyz : y ≠ z := fun h => hB.2 (h ▸ hB.1)
        rw [if_neg hA, if_pos hB]
        have hz' : z ∉ insert y ((g w).erase z) := by
          simp [Finset.mem_insert, Finset.mem_erase, hyz.symm]
        have hy' : y ∈ insert y ((g w).erase z) := Finset.mem_insert_self _ _
        rw [if_pos ⟨hy', hz'⟩,
            Finset.erase_insert (by simp [Finset.mem_erase]; intro _; exact hB.2),
            Finset.insert_erase hB.1]
      · rw [if_neg hA, if_neg hB, if_neg hA, if_neg hB]
  · rw [transport_other x y z w hw, transport_other x y z w hw]

/-- A transport changes only the moving self's row, and acts only when the swap precondition holds. The first
clause: every row other than `x` is unchanged. The second: if neither swap precondition holds at row `x`, the
move is the identity. Together they show the generator is a function of the attention alone, with no free
parameter. -/
theorem ws1_move_local (x y z : Fin 3) (g : G) :
    (∀ w, w ≠ x → (transport x y z g) w = g w)
  ∧ (¬ (y ∈ g x ∧ z ∉ g x) → ¬ (z ∈ g x ∧ y ∉ g x) → transport x y z g = g) := by
  refine ⟨fun w hw => transport_other x y z w hw g, ?_⟩
  intro hA hB
  funext w
  by_cases hw : w = x
  · subst hw
    rw [transport_row, if_neg hA, if_neg hB]
  · exact transport_other x y z w hw g

end P3S0
