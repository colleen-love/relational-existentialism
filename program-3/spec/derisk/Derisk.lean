/-
`program-3/spec/derisk/Derisk.lean`

Step zero: the scratch de-risk for Program 3 (charter, "Step zero"). A throwaway, self-contained file,
compiled by hand (`lake env lean`), not a build root. It checks that the flow design can exist on the
state space of attention graphs over a three-element carrier:

1. a generator of signed single-edge moves (transports) exists whose every move is a bijection on the
   whole state space (an involution) — the reversible microdynamics;
2. every transport conserves each self's attention capacity (out-degree), and exchanges the signed
   charge zero-sum: every bystander's charge is unchanged, and the two exchange partners' total is
   unchanged;
3. a reification-style coarse-graining (direction erasure, the summary Program 2 proved blind to the
   knowing-asymmetry) is genuinely lossy, and the macro-step depends on the erased microstate — the
   seed of the emergent arrow.

Checks 1 and 2 are proved structurally, for every state and every move. A first attempt proved them by
`decide` over the whole 512-state space; the kernel cannot evaluate a `decide` over this function space
in reasonable time, which is itself a de-risk result: Series 3.0 must prove its universal targets
structurally and reserve `decide` for witnesses and small existentials. Check 3 is two concrete
witnesses. Result recorded in `program-3/status.md`.
-/
import Mathlib

namespace P3Derisk

/-- The whole universe of the de-risk: every attention graph on three relata. 512 states. -/
abbrev G : Type := Fin 3 → Finset (Fin 3)

/-- The transport move: self `x` moves one unit of attention between targets `y` and `z`.
If `x` attends `y` and not `z`, the attention moves to `z`; in the mirror situation it moves back;
otherwise nothing happens. Total on the state space, and its own inverse. -/
def transport (x y z : Fin 3) (g : G) : G := fun w =>
  if w = x then
    if y ∈ g x ∧ z ∉ g x then insert z ((g x).erase y)
    else if z ∈ g x ∧ y ∉ g x then insert y ((g x).erase z)
    else g x
  else g w

/-- The in-degree: how many selves attend `w`. -/
def inDeg (g : G) (w : Fin 3) : ℕ := (Finset.univ.filter (fun u => w ∈ g u)).card

/-- The signed charge of a self: attention given minus attention received (the sum of the signed
increments, Series 2.8's quantity, restated on the state space). -/
def charge (g : G) (w : Fin 3) : ℤ := ((g w).card : ℤ) - (inDeg g w : ℤ)

/-- The direction-erasing summary: the symmetric relating, blind to who attends whom. -/
def sym (g : G) : Fin 3 → Fin 3 → Bool := fun a b => decide (b ∈ g a) || decide (a ∈ g b)

/-! ## Row lemmas -/

lemma transport_row (x y z : Fin 3) (g : G) :
    (transport x y z g) x =
      (if y ∈ g x ∧ z ∉ g x then insert z ((g x).erase y)
       else if z ∈ g x ∧ y ∉ g x then insert y ((g x).erase z)
       else g x) := by
  simp [transport]

lemma transport_other (x y z w : Fin 3) (hw : w ≠ x) (g : G) :
    (transport x y z g) w = g w := by
  simp [transport, hw]

/-! ## Check 1: the generator is reversible on the whole state space -/

/-- Every transport is an involution, hence a bijection, on every state. Structural, not a
finite-space check: the argument uses nothing about `Fin 3`. -/
theorem check1_moves_reversible (x y z : Fin 3) (g : G) :
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

/-! ## Check 2: capacity conserved, charge exchanged zero-sum -/

/-- Every transport conserves every self's attention capacity (out-degree). -/
theorem check2a_capacity_conserved (x y z : Fin 3) (g : G) (w : Fin 3) :
    ((transport x y z g) w).card = (g w).card := by
  by_cases hw : w = x
  · subst hw
    rw [transport_row]
    by_cases hA : y ∈ g w ∧ z ∉ g w
    · rw [if_pos hA,
          Finset.card_insert_of_not_mem (by simp [Finset.mem_erase]; intro _; exact hA.2),
          Finset.card_erase_of_mem hA.1]
      have : 1 ≤ (g w).card := Finset.card_pos.mpr ⟨y, hA.1⟩
      omega
    · by_cases hB : z ∈ g w ∧ y ∉ g w
      · rw [if_neg hA, if_pos hB,
            Finset.card_insert_of_not_mem (by simp [Finset.mem_erase]; intro _; exact hB.2),
            Finset.card_erase_of_mem hB.1]
        have : 1 ≤ (g w).card := Finset.card_pos.mpr ⟨z, hB.1⟩
        omega
      · rw [if_neg hA, if_neg hB]
  · rw [transport_other x y z w hw]

/-- Membership in the moved row is unchanged for anyone who is neither exchange partner. -/
lemma transport_row_mem (x y z w : Fin 3) (hwy : w ≠ y) (hwz : w ≠ z) (g : G) :
    (w ∈ (transport x y z g) x) ↔ w ∈ g x := by
  rw [transport_row]
  by_cases hA : y ∈ g x ∧ z ∉ g x
  · rw [if_pos hA]; simp [Finset.mem_insert, Finset.mem_erase, hwy, hwz]
  · by_cases hB : z ∈ g x ∧ y ∉ g x
    · rw [if_neg hA, if_pos hB]; simp [Finset.mem_insert, Finset.mem_erase, hwy, hwz]
    · rw [if_neg hA, if_neg hB]

/-- A bystander's charge is unchanged by a transport. -/
theorem check2b_bystander (x y z : Fin 3) (g : G) (w : Fin 3) (hwy : w ≠ y) (hwz : w ≠ z) :
    charge (transport x y z g) w = charge g w := by
  have hin : inDeg (transport x y z g) w = inDeg g w := by
    unfold inDeg
    congr 1
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hu : u = x
    · subst hu; exact transport_row_mem u y z w hwy hwz g
    · rw [transport_other x y z u hu]
  unfold charge
  rw [hin, check2a_capacity_conserved]

/-- The exchange partners' indicator pair at the moved row is preserved as a sum. -/
lemma transport_row_pair (x y z : Fin 3) (g : G) :
    ((if y ∈ (transport x y z g) x then 1 else 0) + (if z ∈ (transport x y z g) x then 1 else 0) : ℕ)
      = (if y ∈ g x then 1 else 0) + (if z ∈ g x then 1 else 0) := by
  rw [transport_row]
  by_cases hA : y ∈ g x ∧ z ∉ g x
  · have hyz : y ≠ z := fun h => hA.2 (h ▸ hA.1)
    rw [if_pos hA]
    simp [Finset.mem_insert, Finset.mem_erase, hyz, hA.1, hA.2]
  · by_cases hB : z ∈ g x ∧ y ∉ g x
    · have hyz : y ≠ z := fun h => hB.2 (h ▸ hB.1)
      rw [if_neg hA, if_pos hB]
      simp [Finset.mem_insert, Finset.mem_erase, hyz, hyz.symm, hB.1, hB.2]
    · rw [if_neg hA, if_neg hB]

/-- The exchange is zero-sum: the two partners' total charge is unchanged. What one gains the other
loses, exactly. Together with `check2b_bystander`, this is the local conservation law. -/
theorem check2b_exchange_zero_sum (x y z : Fin 3) (g : G) :
    charge (transport x y z g) y + charge (transport x y z g) z = charge g y + charge g z := by
  have hsum : inDeg (transport x y z g) y + inDeg (transport x y z g) z
      = inDeg g y + inDeg g z := by
    unfold inDeg
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    congr 1
    · exact transport_row_pair x y z g
    · apply Finset.sum_congr rfl
      intro u hu
      rw [transport_other x y z u (Finset.ne_of_mem_erase hu)]
  have hy := check2a_capacity_conserved x y z g y
  have hz := check2a_capacity_conserved x y z g z
  unfold charge
  omega

/-! ## Check 3: the summary is lossy and the macro-step reads the erased microstate -/

/-- One directed edge, each way: two distinct microstates. -/
def gFwd : G := fun w => if w = 0 then {1} else ∅
def gBwd : G := fun w => if w = 1 then {0} else ∅

/-- The summary erases the direction: the two microstates are distinct but summarize identically. -/
theorem check3a_summary_lossy : gFwd ≠ gBwd ∧ sym gFwd = sym gBwd := by
  constructor
  · intro h
    have := congrFun h 0
    simp [gFwd, gBwd] at this
  · decide

/-- The same transport applied to the two summary-identical microstates yields different summaries:
the macro-evolution is not a function of the macro-state. The information the summary discards is
exactly what the next step needs — the seed of the emergent arrow. -/
theorem check3b_macro_reads_microstate :
    sym gFwd = sym gBwd
    ∧ sym (transport 0 1 2 gFwd) ≠ sym (transport 0 1 2 gBwd) := by
  constructor
  · decide
  · intro h
    have := congrFun (congrFun h 0) 2
    revert this
    decide

end P3Derisk
