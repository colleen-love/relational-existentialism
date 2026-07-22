/-
`program-3/series-0/formal/P3S0/ws4.lean`

WS4 - Connectivity: the fuel-based reachability of the flow, and the connectivity theorem. Program 3 Series 0
(3.0), THE FLOW.

Building on the ground of WS1, this file defines when the flow connects two states and proves the
connectivity target at full strength:

- `moves` (the one-step transport neighbours of a state, over every move triple), `flowStep` (one round of
  closure), and `flowReach` (the fuel-based closure of all transport moves), a fresh definition on the shape
  of Series 2.9's `reachN`;
- `Connected` (two states joined by some finite number of transport rounds) and its transitivity;
- the capacity vector `capVec`, and `ws4_flow_connects`: any two states with the same capacity vector are
  connected by transports.

The route is structural and row-wise. A single lemma over `Finset (Fin 3)` (`row_swap`, discharged by
`decide` over the eight-element powerset, not over the state space) shows any two equal-card rows differ by at
most one transport swap. From it, one transport moves any single row to a target of equal card
(`oneStepRow`), and the three rows are fixed in turn, composing to full connectivity.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S0.ws1

namespace P3S0

set_option linter.unusedVariables false

/-! ## The fuel-based closure of the transport moves -/

/-- The one-step transport neighbours of a state: the image of `g` under every move triple `(x, y, z)`. -/
def moves (g : G) : Finset G :=
  (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3)).image (fun t => transport t.1 t.2.1 t.2.2 g)

/-- One round of closure: the set together with every one-transport neighbour of its members. -/
def flowStep (R : Finset G) : Finset G := R ∪ R.biUnion moves

/-- The fuel-based closure of the transport moves (the shape of Series 2.9's `reachN`, written fresh here):
`flowReach n R` is the set reached from `R` in `n` rounds of transport closure. -/
def flowReach : ℕ → Finset G → Finset G
  | 0, R => R
  | (n + 1), R => flowReach n (flowStep R)

/-- Two states are connected when some finite number of transport rounds joins them. -/
def Connected (g h : G) : Prop := ∃ n, h ∈ flowReach n {g}

@[simp] lemma flowReach_one (R : Finset G) : flowReach 1 R = flowStep R := rfl

lemma flowReach_succ (n : ℕ) (R : Finset G) :
    flowReach (n + 1) R = flowReach n (flowStep R) := rfl

/-- `flowStep` is monotone in the set it closes. -/
lemma flowStep_mono {R S : Finset G} (h : R ⊆ S) : flowStep R ⊆ flowStep S := by
  apply Finset.union_subset_union h
  intro a ha
  rw [Finset.mem_biUnion] at ha ⊢
  obtain ⟨i, hi, ha⟩ := ha
  exact ⟨i, h hi, ha⟩

/-- The closure is monotone in the fuel-free sense: closing a larger set gives a larger result. -/
lemma flowReach_mono_set : ∀ (n : ℕ) {R S : Finset G}, R ⊆ S → flowReach n R ⊆ flowReach n S := by
  intro n
  induction n with
  | zero => intro R S h; exact h
  | succ n ih => intro R S h; exact ih (flowStep_mono h)

/-- The seed set sits inside its own closure. -/
lemma subset_flowReach : ∀ (n : ℕ) (R : Finset G), R ⊆ flowReach n R := by
  intro n
  induction n with
  | zero => intro R; exact le_refl R
  | succ n ih =>
      intro R
      exact Finset.Subset.trans Finset.subset_union_left (ih (flowStep R))

/-- The fuel adds: closing for `n + m` rounds is closing for `m` after closing for `n`. -/
lemma flowReach_add : ∀ (n m : ℕ) (R : Finset G),
    flowReach (n + m) R = flowReach m (flowReach n R) := by
  intro n
  induction n with
  | zero => intro m R; rw [Nat.zero_add]; rfl
  | succ n ih =>
      intro m R
      have key : flowReach (n + 1 + m) R = flowReach (n + m) (flowStep R) := by
        have e : n + 1 + m = n + m + 1 := by ring
        rw [e, flowReach_succ]
      rw [key, ih m (flowStep R), flowReach_succ]

/-- Connectivity is transitive: chains of transport rounds compose. -/
lemma connected_trans {a b c : G} (hab : Connected a b) (hbc : Connected b c) : Connected a c := by
  obtain ⟨n, hn⟩ := hab
  obtain ⟨m, hm⟩ := hbc
  refine ⟨n + m, ?_⟩
  rw [flowReach_add]
  have hsub : ({b} : Finset G) ⊆ flowReach n {a} := Finset.singleton_subset_iff.mpr hn
  exact flowReach_mono_set m hsub hm

/-! ## Row-wise connectivity -/

/-- Any two equal-card rows over the three-element carrier differ by at most one transport swap: either they
are equal, or one lies one insert-erase step from the other. Discharged by `decide` over the eight-element
powerset of `Fin 3` — a statement about the row alphabet, never over the state space. -/
lemma row_swap : ∀ (A B : Finset (Fin 3)), A.card = B.card →
    A = B ∨ ∃ y z : Fin 3, y ∈ A ∧ z ∉ A ∧ insert z (A.erase y) = B := by
  decide

/-- One transport moves a single row to any target of equal card, leaving every other row fixed. If `g'`
agrees with `g` off row `x` and has the same card there, then `g'` is reached from `g` in one round. -/
lemma oneStepRow (x : Fin 3) (g g' : G)
    (hoff : ∀ w, w ≠ x → g' w = g w) (hcard : (g x).card = (g' x).card) :
    g' ∈ flowReach 1 {g} := by
  rw [flowReach_one]
  rcases row_swap (g x) (g' x) hcard with heq | ⟨y, z, hy, hz, hins⟩
  · have hgg : g' = g := by
      funext w
      by_cases hw : w = x
      · subst hw; exact heq.symm
      · exact hoff w hw
    rw [hgg]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self g)
  · have htg : transport x y z g = g' := by
      funext w
      by_cases hw : w = x
      · subst hw; rw [transport_row, if_pos ⟨hy, hz⟩]; exact hins
      · rw [transport_other x y z w hw]; exact (hoff w hw).symm
    have hmem : g' ∈ moves g := by
      rw [← htg]
      exact Finset.mem_image.mpr ⟨(x, y, z), Finset.mem_univ _, rfl⟩
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨g, Finset.mem_singleton_self g, hmem⟩)

/-! ## The connectivity theorem -/

/-- The capacity vector of a state: the out-degree of each self. -/
def capVec (g : G) : Fin 3 → ℕ := fun x => (g x).card

/-- Any two states with the same capacity vector are connected by transports. Proved row by row: the three
rows are fixed to the target in turn, each in one transport (`oneStepRow`), and the rounds compose
(`connected_trans`). The full connectivity target lands at full strength — no witnessed-only weakening. -/
theorem ws4_flow_connects (g h : G) (hcap : capVec g = capVec h) : Connected g h := by
  have hpt : ∀ x, (g x).card = (h x).card := fun x => congrFun hcap x
  set g1 := Function.update g 0 (h 0) with hg1
  set g2 := Function.update g1 1 (h 1) with hg2
  set g3 := Function.update g2 2 (h 2) with hg3
  -- row 0
  have c1 : Connected g g1 := by
    refine ⟨1, oneStepRow 0 g g1 (fun w hw => ?_) ?_⟩
    · rw [hg1]; exact Function.update_of_ne hw (h 0) g
    · rw [hg1, Function.update_self]; exact hpt 0
  -- row 1
  have c2 : Connected g1 g2 := by
    refine ⟨1, oneStepRow 1 g1 g2 (fun w hw => ?_) ?_⟩
    · rw [hg2]; exact Function.update_of_ne hw (h 1) g1
    · rw [hg2, Function.update_self, hg1,
          Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide) (h 0) g]
      exact hpt 1
  -- row 2
  have c3 : Connected g2 g3 := by
    refine ⟨1, oneStepRow 2 g2 g3 (fun w hw => ?_) ?_⟩
    · rw [hg3]; exact Function.update_of_ne hw (h 2) g2
    · rw [hg3, Function.update_self, hg2,
          Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide) (h 1) g1,
          hg1, Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide) (h 0) g]
      exact hpt 2
  -- g3 = h
  have hgh : g3 = h := by
    funext w
    rw [hg3, hg2, hg1]
    fin_cases w <;> simp [Function.update_apply]
  rw [hgh] at c3
  exact connected_trans (connected_trans c1 c2) c3

end P3S0
