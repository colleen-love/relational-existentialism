/-
# Sparsity step 2: cost-sharing over a poset of couplings

[03.7](../../docs/archive/03.7-sparsity.md) flags the first gap between the counting lemma and a
theorem about `Cl(𝕋)`: **couplings are not an unstructured set.** They compose and **share** sub-relatings,
so the cost grading is **lax (sub-additive)** — the clean sum `Σ dλ` becomes an inequality over a poset
of couplings, and "sparsity must be re-proved with sharing allowed." This module does that, and the
honest verdict is sharper than the spec's hope.

We model a self's **footprint** as the finite set of relatings it maintains (`Finset α` of atomic
couplings), with the canonical cost = how many distinct relatings the system must hold (cardinality —
the prototypical monotone, sub-additive, modular grading). Sharing = overlapping footprints; the budget
bounds the **actual** spend `(⋃ᵢ Fᵢ).card`, not the naive sum.

* `subadditive_spend_le_sum` — **"sharing only helps" (lowers spend):** for *any* monotone sub-additive
  cost, the spend of the shared footprint is at most the naive per-self sum. The no-sharing case is the
  worst case *for spend*.
* `disjoint_spend_floor` / `disjoint_count_bound` — **no sharing recovers the bound:** pairwise-disjoint
  footprints make the spend exactly the sum, so a per-self floor `m` gives `k·m ≤ spend ≤ β`, i.e.
  `k ≤ β/m` — the original counting bound, now seen as the *disjoint* (worst) case.
* `full_sharing_unbounded` — **but naive sparsity genuinely fails under full sharing:** if every self
  shares one common footprint `S`, then for *every* `N` there is a collection of `≥ N` selves (each
  costing `S.card`) whose spend is just `S.card ≤ β`. The count is unbounded within budget. So
  sharing does **not** merely "help" — it breaks the bound.
* `private_count_bound` — **and exactly what rescues it:** if each self owns a **private** relating (one
  in its footprint and no other's), the count is bounded by the spend, `k ≤ (⋃ Fᵢ).card ≤ β`, *whatever*
  the sharing. So sparsity survives sharing **iff** selves have a positive private footprint.

**The honest correction to the spec.** The spec hoped "the worst case (no sharing) is the set bound and
sharing only helps." Half is right: sharing lowers *spend* (`subadditive_spend_le_sum`). But the count
bound is **not** preserved — full sharing makes selves arbitrarily cheap-to-co-maintain and the carrier
unbounded (`full_sharing_unbounded`). The bound survives precisely under a **positive private floor**
(`private_count_bound`) — the same shape as the depth floor in
[`SparsityPosits`](SparsityPosits.lean): rarity needs an *exclusive* cost per self, not just a cost.
This is the load-bearing refinement step 2 actually requires.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RelExist.SparsitySharing

open Finset

variable {α : Type*} [DecidableEq α] {ι : Type*}

/-- **Sharing only lowers the spend.** For any monotone sub-additive cost `c` (with `c ∅ = 0`), the cost
of the shared footprint `⋃ᵢ Fᵢ` is at most the naive per-self sum `Σᵢ c (Fᵢ)`. So the no-sharing case is
the worst case for spend; sharing can only reduce what the budget must cover. (The canonical cost,
cardinality, is such a `c` — `card_biUnion_le` below.) -/
theorem subadditive_spend_le_sum {c : Finset α → ℕ} (hc0 : c ∅ = 0)
    (hsub : ∀ A B : Finset α, c (A ∪ B) ≤ c A + c B) (s : Finset ι) (F : ι → Finset α) :
    c (s.biUnion F) ≤ ∑ i ∈ s, c (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hc0.le
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (hsub _ _).trans (Nat.add_le_add_left ih _)

/-- The canonical (cardinality) cost is sub-additive: `(⋃ᵢ Fᵢ).card ≤ Σᵢ (Fᵢ).card`. The concrete
instance of `subadditive_spend_le_sum`. -/
theorem card_spend_le_sum {k : ℕ} (F : Fin k → Finset α) :
    (univ.biUnion F).card ≤ ∑ i, (F i).card :=
  Finset.card_biUnion_le

/-- **No sharing recovers the floor.** When footprints are pairwise disjoint, the spend is exactly the
sum, so with a per-self floor `m` the spend is at least `k·m`. -/
theorem disjoint_spend_floor {k : ℕ} (F : Fin k → Finset α) (m : ℕ)
    (hdisj : ∀ i ∈ (univ : Finset (Fin k)), ∀ j ∈ (univ : Finset (Fin k)), i ≠ j →
      Disjoint (F i) (F j))
    (hfloor : ∀ i, m ≤ (F i).card) :
    k * m ≤ (univ.biUnion F).card := by
  have hsum : (univ.biUnion F).card = ∑ i, (F i).card := Finset.card_biUnion hdisj
  have hconst : ∑ _i : Fin k, m = k * m := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
  rw [hsum, ← hconst]
  exact Finset.sum_le_sum (fun i _ => hfloor i)

/-- **The original counting bound as the no-sharing (worst) case.** Pairwise-disjoint footprints, each
costing at least `m`, under spend budget `β`: the number of selves is `≤ β/m` — `Sparsity`'s
`stab_card_le_div`, recovered over a poset of footprints in the disjoint case. -/
theorem disjoint_count_bound {k : ℕ} (F : Fin k → Finset α) (m β : ℕ) (hm : 0 < m)
    (hdisj : ∀ i ∈ (univ : Finset (Fin k)), ∀ j ∈ (univ : Finset (Fin k)), i ≠ j →
      Disjoint (F i) (F j))
    (hfloor : ∀ i, m ≤ (F i).card) (hbudget : (univ.biUnion F).card ≤ β) :
    k ≤ β / m := by
  rw [Nat.le_div_iff_mul_le hm]
  exact (disjoint_spend_floor F m hdisj hfloor).trans hbudget

/-- **Naive sparsity fails under full sharing.** If every self maintains one common footprint `S`, then
for *every* `N` there is a collection of `≥ N` selves — each costing `S.card` — whose total spend is just
`S.card ≤ β`. So the carrier is unbounded within the budget: sharing does not merely "help," it breaks the
count bound. (Contrast `disjoint_count_bound`; the difference is exactly whether footprints overlap.) -/
theorem full_sharing_unbounded (S : Finset α) (β : ℕ) (hβ : S.card ≤ β) (N : ℕ) :
    ∃ (k : ℕ) (F : Fin k → Finset α),
      N ≤ k ∧ (∀ i, (F i).card = S.card) ∧ (univ.biUnion F).card ≤ β := by
  refine ⟨N + 1, fun _ => S, by omega, fun _ => rfl, ?_⟩
  have hbU : (univ.biUnion (fun _ : Fin (N + 1) => S)) = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨0, hx⟩⟩
  rw [hbU]; exact hβ

/-- **What rescues sparsity under arbitrary sharing: a positive private footprint.** If each self owns a
**private** relating — one in its own footprint and no other's — then the count is bounded by the spend,
`k ≤ (⋃ᵢ Fᵢ).card`, *regardless* of how much the rest is shared. The private elements are `k` distinct
points of the shared footprint. Hence under budget, `k ≤ β`. This is the exclusive-cost floor that makes
selves rare even when relatings overlap — the step-2 analogue of the depth floor `d ≥ 2`. -/
theorem private_count_bound {k : ℕ} (F : Fin k → Finset α)
    (priv : Fin k → α) (hmem : ∀ i, priv i ∈ F i)
    (hpriv : ∀ i j, priv i ∈ F j → i = j) :
    k ≤ (univ.biUnion F).card := by
  have hinj : Function.Injective priv := by
    intro i j hij
    apply hpriv i j
    rw [hij]; exact hmem j
  have hsub : (univ.image priv) ⊆ univ.biUnion F := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem i⟩
  calc k = (univ.image priv).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ (univ.biUnion F).card := Finset.card_le_card hsub

/-- **The private-footprint count bound, under budget.** With an exclusive relating per self and spend
budget `β`, the number of selves is `≤ β` — sparsity survives arbitrary sharing exactly because of the
private floor. -/
theorem private_count_bound_budget {k : ℕ} (F : Fin k → Finset α)
    (priv : Fin k → α) (hmem : ∀ i, priv i ∈ F i)
    (hpriv : ∀ i j, priv i ∈ F j → i = j) (β : ℕ) (hbudget : (univ.biUnion F).card ≤ β) :
    k ≤ β :=
  (private_count_bound F priv hmem hpriv).trans hbudget

end RelExist.SparsitySharing
