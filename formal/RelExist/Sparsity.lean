/-
# Sparsity of `Stab` — discrete core (Lemmas 3.1 & 3.2)

Machine-checked, dependency-free (Lean 4 core, **no mathlib**) formalization of the
combinatorial heart of the sparsity conjecture in
`docs/spec/03-sparsity-conjecture.md`:

* **Lemma 3.1 (sparsity from a budget).** Under a finite attention budget `β`, with
  every stabilized self costing at least a positive floor `m`, the number of selves
  times `m` is at most `β`; equivalently the count is `≤ β / m` — a bound
  **independent of how many couplings exist**.
* **Lemma 3.2 (collapse without a bound).** Absent the budget the count is
  unbounded, so finiteness of the budget is *necessary* for sparsity.

A collection of stabilized selves is modeled as a `List Nat` of their per-self
maintenance costs (in natural-number attention units); `totalSpend` is the budget
actually consumed. The real-valued and density-→-0 / nowhere-dense refinements
(steps 3–4 of the spec's proof strategy) need mathlib and are deferred — see
`formal/README.md`.
-/

namespace RelExist

/-- A collection of stabilized selves, each tagged by the attention cost (in ℕ
units) of maintaining its loop. -/
abbrev Selves := List Nat

/-- Total attention spent maintaining a collection of selves. -/
def totalSpend : Selves → Nat
  | []      => 0
  | c :: cs => c + totalSpend cs

@[simp] theorem totalSpend_nil : totalSpend [] = 0 := rfl

@[simp] theorem totalSpend_cons (c : Nat) (cs : Selves) :
    totalSpend (c :: cs) = c + totalSpend cs := rfl

/-- **Core counting bound.** If every maintained self costs at least `m`, then the
number of selves times `m` is at most the total attention spent. -/
theorem min_mul_length_le_totalSpend (cs : Selves) (m : Nat)
    (h : ∀ c ∈ cs, m ≤ c) : m * cs.length ≤ totalSpend cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      have hc  : m ≤ c := h c (List.mem_cons_self c cs)
      have hcs : ∀ x ∈ cs, m ≤ x := fun x hx => h x (List.mem_cons_of_mem c hx)
      have hlen := ih hcs
      calc m * (c :: cs).length
          = m * cs.length + m := by rw [List.length_cons, Nat.mul_succ]
        _ ≤ totalSpend cs + c := Nat.add_le_add hlen hc
        _ = totalSpend (c :: cs) := by rw [totalSpend_cons, Nat.add_comm]

/-- **Lemma 3.1 (sparsity from a budget), division-free form.** With a finite budget
`β` and a positive cost floor `m`, the number of stabilized selves times `m` is at
most `β`. Hence the count is bounded by a constant depending only on `β` and `m` —
independent of the total number of couplings. -/
theorem stab_card_bound (cs : Selves) (m β : Nat)
    (hcost : ∀ c ∈ cs, m ≤ c) (hbudget : totalSpend cs ≤ β) :
    m * cs.length ≤ β :=
  Nat.le_trans (min_mul_length_le_totalSpend cs m hcost) hbudget

/-- **Lemma 3.1, divided form.** `cs.length ≤ β / m` when `m > 0`. -/
theorem stab_card_le_div (cs : Selves) (m β : Nat) (hm : 0 < m)
    (hcost : ∀ c ∈ cs, m ≤ c) (hbudget : totalSpend cs ≤ β) :
    cs.length ≤ β / m := by
  have h := stab_card_bound cs m β hcost hbudget
  rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
  exact h

/-- **Sparsity with stabilization depth ≥ 2.** Because a genuine self requires being
returned to at least twice (`d ≥ 2`, axiom A3), each costs at least `2`, so at most
`β / 2` selves stabilize: the rare-by-construction regime. -/
theorem stab_card_le_half (cs : Selves) (β : Nat)
    (hcost : ∀ c ∈ cs, 2 ≤ c) (hbudget : totalSpend cs ≤ β) :
    cs.length ≤ β / 2 :=
  stab_card_le_div cs 2 β (by decide) hcost hbudget

/-- Every element of `List.replicate n a` equals `a`. -/
private theorem eq_of_mem_replicate {a b : Nat} :
    ∀ {n}, a ∈ List.replicate n b → a = b
  | 0,   h => absurd h (List.not_mem_nil a)
  | _+1, h => by
      rw [List.replicate_succ] at h
      rcases List.mem_cons.1 h with h | h
      · exact h
      · exact eq_of_mem_replicate h

/-- **Lemma 3.2 (collapse without a bound).** Absent a finite budget, the number of
stabilized selves is unbounded: for every `N` there is a valid collection of exactly
`N` selves, each meeting the cost floor `m`. Hence finiteness of the budget is
*necessary* for sparsity — contrast `stab_card_bound`. -/
theorem unbounded_without_budget (m N : Nat) :
    ∃ cs : Selves, (∀ c ∈ cs, m ≤ c) ∧ cs.length = N := by
  refine ⟨List.replicate N m, ?_, ?_⟩
  · intro c hc
    have hcm : c = m := eq_of_mem_replicate hc
    exact hcm ▸ Nat.le_refl m
  · simp

end RelExist
