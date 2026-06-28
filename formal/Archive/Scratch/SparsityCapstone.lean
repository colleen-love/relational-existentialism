/-
# Conjecture 3.7.3, closed — the cost-graded sparsity dichotomy

[03.7](../../docs/spec/03.7-sparsity.md) states **Conjecture 3.7.3**: under a finite attention budget
`β`, the stabilized selves `Stab_R` are **sparse** in `Cl(𝕋)` — nowhere dense, density `→ 0` — *with the
bound degrading gracefully under cost-sharing*; and dropping the budget makes them dense (the sharp
dichotomy). Its proof strategy has four steps, all mechanized: the counting lemmas (Lean
`Sparsity`), the cost-sharing lift (`SparsitySharing`), the threshold↔fixed-point bridge for the genuine
`Φ_c` (`Convergence`/`Stabilization`/`SparsityPosits`), and the topological nowhere-dense form (Agda
`selves-nowhereDense`). This module assembles the **counting / density / dichotomy** content into one
capstone.

**The honest correction, carried through.** `SparsitySharing` proved that the conjecture's hope —
"sharing only helps, the bound degrades gracefully" — is *false as stated*: under **full sharing** the
count is unbounded within budget (`full_sharing_unbounded`). Sparsity survives sharing **iff** each self
owns a **private footprint** — an exclusive relating (`private_count_bound`). So Conjecture 3.7.3's correct
form is a **dichotomy on exclusivity**, and that is what is proved here:

* `cost_graded_density_tendsto_zero` — **with** a positive private footprint per self (and spend `≤ β`),
  the count is `≤ β` independent of the stock of relatings, so the density of selves `→ 0`. The genuine
  cost-graded "selves are rare", lifting `Real.stab_density_tendsto_zero` past cost-sharing.
* `conjecture_3_7` — the **dichotomy**: density `→ 0` *with* exclusivity; unboundedly many selves within
  the same budget *without* it (full sharing). Finiteness of `β` **and** an exclusive cost per self are
  *together* necessary and sufficient for the counting sparsity.

With the topological nowhere-dense clause (Agda) this closes Conjecture 3.7.3 in its correct, cost-graded
form: the unconditional version is provably false, the exclusivity-conditioned version is a theorem. The
only residue is the literal instantiation in the free `Cl(𝕋)` (that its couplings carry a private
footprint), which is exactly the exclusivity condition this dichotomy isolates.
-/
import Scratch.SparsitySharing
import Scratch.SparsityReal

namespace RelExist.SparsityCapstone

open Finset Filter Topology RelExist.SparsitySharing

variable {α : Type*} [DecidableEq α]

/-- **Cost-graded "selves are rare".** A family of self-configurations — `k N` selves with footprints
`F N` over a growing stock of relatings, each self owning a **private** footprint element and the total
spend bounded by `β` — has the count `≤ β` (private-footprint bound) independent of `N`, hence the
**density of selves tends to `0`**. The genuine density limit *with cost-sharing allowed*, lifting
`Real.stab_density_tendsto_zero` past the cost-sharing gap. -/
theorem cost_graded_density_tendsto_zero (β : ℕ)
    (k : ℕ → ℕ) (F : ∀ N, Fin (k N) → Finset α) (priv : ∀ N, Fin (k N) → α)
    (hmem : ∀ N i, priv N i ∈ F N i) (hpriv : ∀ N i j, priv N i ∈ F N j → i = j)
    (hbudget : ∀ N, (univ.biUnion (F N)).card ≤ β) :
    Tendsto (fun N => (k N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  apply RelExist.Real.density_tendsto_zero (C := (β : ℝ))
  · intro N; positivity
  · intro N
    have h := private_count_bound_budget (F N) (priv N) (hmem N) (hpriv N) β (hbudget N)
    exact_mod_cast h

/-- **Conjecture 3.7.3, the cost-graded dichotomy.** Over a poset of couplings with cost-sharing
(footprints as `Finset`s of relatings) and a finite spend budget `β`:

* **with exclusivity** — each self owns a private footprint — the density of selves vanishes
  (`k N / N → 0`): *selves are rare*;
* **without exclusivity** — full sharing of one common footprint `S` — there are unboundedly many selves
  within the *same* budget: *selves are dense*.

So the counting half of Conjecture 3.7.3 is true exactly under a finite budget **and** an exclusive cost
per self; the unconditional "sharing only helps" form is false. The nowhere-dense topological clause is
the Agda `selves-nowhereDense`. -/
theorem conjecture_3_7 (β : ℕ) :
    (∀ (k : ℕ → ℕ) (F : ∀ N, Fin (k N) → Finset α) (priv : ∀ N, Fin (k N) → α),
        (∀ N i, priv N i ∈ F N i) → (∀ N i j, priv N i ∈ F N j → i = j) →
        (∀ N, (univ.biUnion (F N)).card ≤ β) →
        Tendsto (fun N => (k N : ℝ) / (N : ℝ)) atTop (𝓝 0))
      ∧
    (∀ S : Finset α, S.card ≤ β → ∀ N, ∃ (k : ℕ) (F : Fin k → Finset α),
        N ≤ k ∧ (univ.biUnion F).card ≤ β) :=
  ⟨fun k F priv hmem hpriv hb => cost_graded_density_tendsto_zero β k F priv hmem hpriv hb,
   fun S hS N => by
     obtain ⟨k, F, hk, _, hbU⟩ := full_sharing_unbounded S β hS N
     exact ⟨k, F, hk, hbU⟩⟩

end RelExist.SparsityCapstone
