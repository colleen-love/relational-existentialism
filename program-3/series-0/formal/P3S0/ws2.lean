/-
`program-3/series-0/formal/P3S0/ws2.lean`

WS2 - Conservation: capacity, the zero-sum exchange, and the bridge to Program 2's increment. Program 3
Series 0 (3.0), THE FLOW.

Building on the ground of WS1, this file reads two derived quantities off the state and shows the transport
conserves them:

- the in-degree `inDeg` (attention received) and the signed charge `charge` (attention given minus attention
  received), both computed from the state, never painted;
- `ws2_capacity_conserved`: every transport preserves every self's attention capacity (out-degree);
- `ws2_exchange_zero_sum`: every self other than the two exchange partners keeps its charge, and the two
  partners' total charge is unchanged;
- `ws2_charge_is_incr_sum`: the bridge to Program 2 — the charge of a self is the sum over targets of Series
  2.8's signed increment `P2S8.incr`. The reuse enters by theorem, not by prose.

Capacity conservation and the bystander/partner laws are proved structurally, adapted from the compiled
de-risk `program-3/spec/derisk/Derisk.lean`. The bridge is proved by expanding the increment as an indicator
difference and splitting the sum.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0.ws1

namespace P3S0

set_option linter.unusedVariables false

/-- The in-degree: how many selves attend `w`. -/
def inDeg (g : G) (w : Fin 3) : ℕ := (Finset.univ.filter (fun u => w ∈ g u)).card

/-- The signed charge of a self: attention given minus attention received. -/
def charge (g : G) (w : Fin 3) : ℤ := ((g w).card : ℤ) - (inDeg g w : ℤ)

/-! ## Capacity conservation -/

/-- Every transport conserves every self's attention capacity (out-degree). -/
theorem ws2_capacity_conserved (x y z : Fin 3) (g : G) (w : Fin 3) :
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

/-! ## The zero-sum exchange -/

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
lemma bystander_charge (x y z : Fin 3) (g : G) (w : Fin 3) (hwy : w ≠ y) (hwz : w ≠ z) :
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
  rw [hin, ws2_capacity_conserved]

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

/-- The exchange is zero-sum: every bystander keeps its charge, and the two partners' total is unchanged.
What one partner gains the other loses, exactly. This is the local conservation law of the flow. -/
theorem ws2_exchange_zero_sum (x y z : Fin 3) (g : G) :
    (∀ w, w ≠ y → w ≠ z → charge (transport x y z g) w = charge g w)
  ∧ (charge (transport x y z g) y + charge (transport x y z g) z = charge g y + charge g z) := by
  refine ⟨fun w hwy hwz => bystander_charge x y z g w hwy hwz, ?_⟩
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
  have hy := ws2_capacity_conserved x y z g y
  have hz := ws2_capacity_conserved x y z g z
  unfold charge
  omega

/-! ## The bridge to Program 2's signed increment -/

/-- The charge of a self is the sum over targets of Series 2.8's signed increment `P2S8.incr`: the reuse of
Program 2's directed increment, entering by theorem. Proved structurally by expanding the increment as the
difference of two indicators and splitting the sum into the out-degree and the in-degree. -/
theorem ws2_charge_is_incr_sum (g : G) (w : Fin 3) :
    charge g w = ∑ y : Fin 3, P2S8.incr g w y := by
  have e1 : (∑ y : Fin 3, (if y ∈ g w then (1 : ℤ) else 0)) = ((g w).card : ℤ) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have e2 : (∑ y : Fin 3, (if w ∈ g y then (1 : ℤ) else 0)) = (inDeg g w : ℤ) := by
    rw [Finset.sum_boole]; rfl
  unfold charge
  rw [← e1, ← e2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rfl

end P3S0
