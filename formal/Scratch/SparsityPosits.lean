/-
# Discharging the two sparsity posits — `d ≥ 2` and the valuation `μ`

[`Convergence`](Convergence.lean) closed the "abstract `σ`" costume of the sparsity bridge for the
**depth**: the convergence depth of the genuine `Φ_c` orbit *is* `Loop`'s `StabilizesAt`. It then
flagged two residues as still open ([03.7 step 3](../../docs/spec/03.7-sparsity.md)):

1. **A forced, non-trivial floor `d ≥ 2`** — "a self needs *genuine* return, not a one-off." Supplied
   as a hypothesis everywhere; even the witness `matarN_stabilizesAt` builds `d` in by construction.
2. **A valuation `μ : X → ℕ`** turning lattice standing into a numeric per-return cost `λ` — the
   residue of "read `λ` off the orbit." `selfCost_le_valuationGain` *posits* such a `μ`.

This module discharges both, honestly and to their real limit.

**Posit 1 — `d ≥ 2` is not arbitrary; its meaning and its necessity are theorems.**
`genuine_return_iff` gives `d ≥ 2` exact structural content over the genuine orbit: *given that the
orbit converges at depth `d`,* `2 ≤ d` **iff** neither the seed nor its single return is already a
fixed point (`f a ≠ a ∧ f (f a) ≠ f a`). So "genuine return" is precisely **not-given ∧ not-one-shot**
— the posit becomes a named structural condition, not a number pulled from the air. And the
load-bearing trichotomy pins what each weakening costs: a **positive** floor (`d ≥ 1`, cost `≥ 1`) is
*exactly* the line between a bounded carrier (`bounded_of_positive_floor`) and an unbounded one
(`zero_cost_unbounded` — depth-`0` "given, not achieved" selves are unboundedly many within *any*
budget, so density does not vanish); `d ≥ 2` is the doctrinal strengthening whose meaning
`genuine_return_iff` fixes. `d ≥ 2` is not *derived* from nothing — you can exhibit a self at any depth
— but it is no longer free: it is the structural "genuine return," and `d ≥ 1` is *forced* by the very
rarity the conjecture asserts.

**Posit 2 — for the finite-depth selves sparsity counts, `μ` is constructed, not posited.**
`orbit_strictStep`/`orbit_strict_lt`: under monotone `Φ_c` from a self-reinforcing seed, every genuine
return is a **strict** standing increase (the before-convergence orbit is a strict `<`-chain). Hence
the `d+1` orbit values are distinct, and `exists_orbit_valuation` **builds** the canonical valuation —
the *return index* `μ(Φ^[n] a) = n`, well-defined precisely because the returns are strict — with no
external `μ`. `selfCost_one_le_orbit_gain` then runs `selfCost_le_valuationGain` over *this* `μ`,
realizing the unit per-return cost `λ = 1` intrinsically: the cost `d·1 = d` is the genuine recursion
depth, counted off the orbit.

**The honest limit of posit 2.** What is discharged is the **canonical unit** valuation (count the
genuine returns). A *non-unit* numeric `λ` — a quantitative *amount* of standing per return — for a
**dense** standing lattice (e.g. `α = [0,1]`) genuinely needs a discretizing measure: a dense order has
no `ℕ`-valued strictly-monotone map. So scaling beyond unit cost remains a real modeling choice (it
exists exactly under the ACC/finite-depth condition of [`Stabilization`](Stabilization.lean)), not a
gap papered over. Unit cost — all the counting bound actually uses — is now free.
-/
import Scratch.Convergence
import Scratch.SparsityReal
import RelExist.Sparsity

namespace RelExist.SparsityPosits

open RelExist RelExist.Attention RelExist.Convergence
open Filter Topology

/-! ## Posit 1 — `d ≥ 2` as genuine return: structural meaning -/

universe u
variable {X : Type u}

/-- **`d ≥ 2` is "genuine return" — not-given ∧ not-one-shot.** *Given that the orbit converges at
depth `d`* (its `d`-th iterate is the first fixed point), the depth is at least `2` **iff** neither the
seed `a` is already a self (`f a ≠ a`) nor its single return `f a` is already a self (`f (f a) ≠ f a`).
This is the exact structural content of A3's "a self needs genuine return, not a one-off": the posit
`d ≥ 2` is the named condition *the recursion is neither pre-given nor reached in a single pass*. -/
theorem genuine_return_iff {f : X → X} {a : X} {d : ℕ} (hconv : ConvergesAt f a d) :
    2 ≤ d ↔ f a ≠ a ∧ f (f a) ≠ f a := by
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · simpa using hconv.2 0 (by omega)
    · simpa [Function.iterate_one] using hconv.2 1 (by omega)
  · rintro ⟨hne1, hne2⟩
    by_contra hd
    push_neg at hd
    have : d = 0 ∨ d = 1 := by omega
    rcases this with rfl | rfl
    · exact hne1 (by simpa using hconv.1)
    · exact hne2 (by simpa [Function.iterate_one] using hconv.1)

/-! ## Posit 1 — load-bearing: a positive floor is the line between sparse and dense

The depth floor enters the counting bound only through the **cost floor** `m = selfCost d λ`. A
positive floor bounds the carrier by a constant independent of how many couplings exist; a zero floor
(admitting depth-`0`, "given not achieved", selves) makes it unbounded within any budget. So `d ≥ 1` is
*necessary* for sparsity, and `d ≥ 2` (`genuine_return_iff`) is the doctrinal strengthening. -/

/-- A self of depth `d ≥ 1` with per-return cost `λ ≥ 1` costs at least `1`: the positive floor. -/
theorem one_le_selfCost (d lam : ℕ) (hd : 1 ≤ d) (hlam : 1 ≤ lam) : 1 ≤ selfCost d lam :=
  Nat.le_trans hd (depth_le_selfCost d lam hlam)

/-- **Positive floor ⇒ bounded carrier.** With a positive cost floor `m` and finite budget `β`, the
number of stabilized selves is `≤ β / m` — a constant **independent of how many couplings exist**. This
is the sparse regime; it needs only `m ≥ 1`, i.e. `d ≥ 1`. -/
theorem bounded_of_positive_floor (cs : Selves) (m β : ℕ) (hm : 0 < m)
    (hcost : ∀ c ∈ cs, m ≤ c) (hbudget : totalSpend cs ≤ β) :
    cs.length ≤ β / m :=
  stab_card_le_div cs m β hm hcost hbudget

/-- **Zero floor ⇒ unbounded carrier (density does not vanish).** If depth-`0` "selves" — given, not
achieved, costing `0` — are admitted, then for *every* `N` there is a collection of exactly `N` of them
whose total spend is `≤ β` for *any* budget `β` (including `β = 0`). So the carrier is unbounded under a
finite budget: sparsity *fails*. This is why the floor must be positive — the load `d ≥ 1` carries. -/
theorem zero_cost_unbounded (β N : ℕ) :
    ∃ cs : Selves, (∀ c ∈ cs, c = 0) ∧ totalSpend cs ≤ β ∧ cs.length = N := by
  have hzero : ∀ k, totalSpend (List.replicate k (0 : ℕ)) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, totalSpend_cons, ih]
  refine ⟨List.replicate N 0, ?_, ?_, ?_⟩
  · intro c hc; exact List.eq_of_mem_replicate hc
  · rw [hzero N]; exact Nat.zero_le β
  · simp

/-- **The qualitative rarity needs only a positive floor.** A family of selves each of depth `≥ 1`
(per-return cost `≥ 1`, hence real cost `≥ 1`) under a fixed budget `β` has **vanishing density**: the
stabilized fraction `|Stab N| / N → 0`. The depth floor enters only as "cost `≥ 1`"; `d ≥ 2` is not
needed for density to vanish (it is needed for the sharper constant `β/2` and for the doctrinal reading).
-/
theorem depth_positive_density_zero {ι : Type*} (S : ℕ → Finset ι) (cost : ι → ℝ) (β : ℝ)
    (hcost : ∀ N, ∀ i ∈ S N, (1 : ℝ) ≤ cost i)
    (hbudget : ∀ N, ∑ i ∈ S N, cost i ≤ β) :
    Tendsto (fun N => ((S N).card : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
  RelExist.Real.stab_density_tendsto_zero S cost 1 β one_pos hcost hbudget

/-! ## Posit 2 — the valuation `μ` constructed from the orbit

The before-convergence orbit of a self-reinforcing seed under the monotone `Φ_c` is a **strict**
`<`-chain: each genuine return strictly increases standing. So the orbit values are distinct, and the
canonical valuation — the *return index* — is well-defined. No external `μ` is posited for unit cost. -/

variable {V : Type*} {α : Type*} [CompleteLattice α]

/-- **Every genuine return is a strict standing increase.** Under the monotone co-directed operator
`Φ` from a self-reinforcing seed `a ≤ Φ a`, while `n < d` (before convergence) the orbit *strictly*
ascends: `Φ^[n] a < Φ^[n+1] a`. (`≤` from generativity `orbit_ascending`; `≠` from convergence — the
`n`-th iterate is not yet a fixed point.) -/
theorem orbit_strictStep (Φ : Field V α →o Field V α) {a : Field V α} (h : a ≤ Φ a)
    {d : ℕ} (hconv : ConvergesAt (⇑Φ) a d) {n : ℕ} (hn : n < d) :
    (⇑Φ)^[n] a < (⇑Φ)^[n + 1] a := by
  refine lt_of_le_of_ne (orbit_ascending Φ h n) ?_
  intro heq
  exact hconv.2 n hn ((Function.iterate_succ_apply' (⇑Φ) n a).symm.trans heq.symm)

/-- **The before-convergence orbit is a strict chain.** For `n < m ≤ d`, `Φ^[n] a < Φ^[m] a`: genuine
returns never repeat a standing, so the `d+1` orbit values are distinct. -/
theorem orbit_strict_lt (Φ : Field V α →o Field V α) {a : Field V α} (h : a ≤ Φ a)
    {d : ℕ} (hconv : ConvergesAt (⇑Φ) a d) :
    ∀ {n m : ℕ}, n < m → m ≤ d → (⇑Φ)^[n] a < (⇑Φ)^[m] a := by
  have key : ∀ k, 0 < k → ∀ n, n + k ≤ d → (⇑Φ)^[n] a < (⇑Φ)^[n + k] a := by
    intro k
    induction k with
    | zero => intro hk; exact (Nat.lt_irrefl 0 hk).elim
    | succ k ih =>
      intro _ n hnk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; simpa using orbit_strictStep Φ h hconv (show n < d by omega)
      · have h1 := ih hkpos n (by omega)
        have h2 := orbit_strictStep Φ h hconv (show n + k < d by omega)
        have hlt := lt_trans h1 h2
        have he : n + (k + 1) = n + k + 1 := by omega
        rw [he]; exact hlt
  intro n m hnm hmd
  have hm : m = n + (m - n) := by omega
  rw [hm]
  exact key (m - n) (by omega) n (by omega)

/-- **The canonical valuation, constructed.** For a finite-depth genuine self (monotone `Φ`,
self-reinforcing seed, orbit converging at depth `d`), the *return index* `μ(Φ^[n] a) = n` is a
genuine total valuation `Field V α → ℕ` — well-defined precisely because the returns are strict
(`orbit_strict_lt`), so the orbit points are distinct and the index is recoverable. This *discharges*
the posited `μ` for the selves sparsity counts: it is the orbit's own recursion counter, not an
external imposition. -/
theorem exists_orbit_valuation (Φ : Field V α →o Field V α) {a : Field V α} (h : a ≤ Φ a)
    {d : ℕ} (hconv : ConvergesAt (⇑Φ) a d) :
    ∃ μ : Field V α → ℕ, ∀ n, n ≤ d → μ ((⇑Φ)^[n] a) = n := by
  set idx : Fin (d + 1) → Field V α := fun i => (⇑Φ)^[i.val] a with hidx
  have hidx_strict : StrictMono idx := by
    intro i j hij
    exact orbit_strict_lt Φ h hconv hij (Nat.lt_succ_iff.mp j.isLt)
  have hidx_inj : Function.Injective idx := hidx_strict.injective
  refine ⟨fun x => (Function.invFun idx x).val, ?_⟩
  intro n hn
  have hmem : (⇑Φ)^[n] a = idx ⟨n, by omega⟩ := rfl
  rw [hmem]
  show (Function.invFun idx (idx ⟨n, by omega⟩)).val = n
  rw [Function.leftInverse_invFun hidx_inj ⟨n, by omega⟩]

/-- **Unit per-return cost, realized off the orbit.** Running `selfCost_le_valuationGain` over the
constructed return-index valuation: the self's cost `selfCost d 1 = d` is bounded by the standing
gained over the orbit. The unit cost `λ = 1` is intrinsic — one genuine (strict) return — so for
finite-depth selves the cost is the recursion depth itself, with no posited `μ`. -/
theorem selfCost_one_le_orbit_gain (Φ : Field V α →o Field V α) {a : Field V α} (h : a ≤ Φ a)
    {d : ℕ} (hconv : ConvergesAt (⇑Φ) a d) :
    ∃ μ : Field V α → ℕ, selfCost d 1 ≤ μ ((⇑Φ)^[d] a) - μ a := by
  obtain ⟨μ, hμ⟩ := exists_orbit_valuation Φ h hconv
  refine ⟨μ, ?_⟩
  apply selfCost_le_valuationGain (⇑Φ) a μ d 1
  intro n hn
  rw [hμ n (by omega), hμ (n + 1) (by omega)]

end RelExist.SparsityPosits
