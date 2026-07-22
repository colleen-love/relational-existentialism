/-
`program-3/spec/derisk/Derisk.lean`

Step zero: the scratch de-risk for Program 3 (charter, "Step zero"). A throwaway, self-contained file,
compiled by hand (`lake env lean`), not a build root. It checks, on the full state space of attention
graphs over a three-element carrier, that the flow design can exist:

1. a generator of signed single-edge moves (transports) exists whose every move is a bijection on the
   whole state space (an involution) — the reversible microdynamics;
2. every transport conserves each self's attention capacity (out-degree), and exchanges the signed
   charge zero-sum: only the two exchange partners' charges move, and their sum is unchanged;
3. a reification-style coarse-graining (direction erasure, the summary Program 2 proved blind to the
   knowing-asymmetry) is genuinely lossy, and the macro-step depends on the erased microstate — the
   seed of the emergent arrow.

All three checks pass by `decide` over the whole 512-state space (no hand-picked witness tables except
where an existential asks for one). Result recorded in `program-3/status.md`.
-/
import Mathlib

namespace P3Derisk

set_option maxRecDepth 100000

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

/-- The signed charge of a self: attention given minus attention received (the sum of the signed
increments, Series 2.8's quantity, restated on the state space). -/
def charge (g : G) (w : Fin 3) : ℤ :=
  ((g w).card : ℤ) - ((Finset.univ.filter (fun u => w ∈ g u)).card : ℤ)

/-- The direction-erasing summary: the symmetric relating, blind to who attends whom. -/
def sym (g : G) : Fin 3 → Fin 3 → Bool := fun a b => decide (b ∈ g a) || decide (a ∈ g b)

/-! ## Check 1: the generator is reversible on the whole state space -/

/-- Every transport is an involution, hence a bijection, on all 512 states. -/
theorem check1_moves_reversible :
    ∀ (x y z : Fin 3) (g : G), transport x y z (transport x y z g) = g := by decide

/-! ## Check 2: capacity conserved, charge exchanged zero-sum -/

/-- Every transport conserves every self's attention capacity (out-degree). -/
theorem check2a_capacity_conserved :
    ∀ (x y z : Fin 3) (g : G) (w : Fin 3),
      ((transport x y z g) w).card = (g w).card := by decide

/-- Every transport moves charge only between the two exchange partners, and zero-sum: every other
self's charge is unchanged, and the partners' total is unchanged. What one gains the other loses. -/
theorem check2b_exchange_zero_sum :
    ∀ (x y z : Fin 3) (g : G),
      (∀ w, w ≠ y → w ≠ z → charge (transport x y z g) w = charge g w)
      ∧ charge (transport x y z g) y + charge (transport x y z g) z
          = charge g y + charge g z := by decide

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
