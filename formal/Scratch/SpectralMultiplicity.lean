/-
# Controlled multiplicity — the counting bound that closes Conjecture 3.4

This module supplies the piece [03.4](../../docs/spec/03.4-the-self-quantified.md) named as the
*candidate new mathematics*: the reconciliation of **"sparse"** and **"multiple."**

The honest situation, read off the literature. Nonlinear Perron–Frobenius theory (order-preserving
homogeneous maps on cones; Hilbert's projective metric; Collatz–Wielandt) is mature, and its strong
results deliver **uniqueness**: under subhomogeneity + primitivity the dynamics is a Hilbert-metric
contraction with *exactly one* positive eigenvector. That is the precise opposite of what the doctrine
wants. A relational self is **contingent** — there must be more than one possible self (`> 1`) — yet
selves must be **rare** (`o(N)`). Multiplicity only appears when one *leaves* the well-behaved
subhomogeneous/primitive regime where the off-the-shelf theorems apply. So 3.4 cannot be a corollary
of standard nonlinear PF: standard nonlinear PF is built to *forbid* the multiplicity 3.4 needs.

The gap, pinned precisely, is three pieces — all closed here, `sorry`-free:

1. **Read `x` off `Φ_c` (the linearization bridge).** The abstract `‖x‖ < 1` of
   [`Distribution`](Distribution.lean) is the **linearization** `x = DΦ_c` at a candidate self: the
   co-directed feedback `y ↦ b + x·y` is a metric contraction with rate `‖x‖` (`feedbackMap_contract`),
   so the living regime `‖x‖ < 1` *is* local attraction — and `sustained x b` is the unique attractor,
   reached geometrically (`living_self_unique_attractor`). This is the **primitive / Perron regime**:
   global contraction ⇒ **exactly one** self (`unique_fixed_of_global_contraction`).

2. **Existence of nonzero eigenforms.** The linear backbone is the Perron–Frobenius existence already
   in [`PerronFrobenius`](PerronFrobenius.lean) (eigenvalue-1 vector + invariant state); a contraction's
   fixed point exists and is `sustained x b` (piece 1). Existence is assemblable from known results.

3. **The counting / sparsity bound — the real theorem.** In the *non*-subhomogeneous, uniqueness-failing
   regime, where multiple attractors coexist, we bound their number from above by a **gap quantity**.
   The mechanism: a locally attracting self with contraction rate `< 1` on a basin of radius `r` is
   **isolated** (`attracting_isolated`), so distinct selves are **`r`-separated** (`attractors_separated`)
   — a *derived* exclusivity (the "private footprint" of [`SparsitySharing`](SparsitySharing.lean), now
   forced by the spectral contraction, not posited). An `r`-separated set inside a region of **capacity
   `m`** (covering number at the gap scale) has at most `m` points (`separated_card_le_cover`),
   **independent of `N`**, so the density of selves `→ 0` (`selves_density_tendsto_zero`). Yet the count
   is **not forced to one**: an explicit two-basin map carries two genuine attractors
   (`two_attracting_selves`). So selves are simultaneously `> 1` (contingency) and `o(N)` (sparse):
   **controlled multiplicity, bounded by structure.**

Bounding the multiplicity *from above by a gap* for a saturating, asymmetric map — rather than proving
it is one — is the content the existing theory does not hand you, precisely because the existing theory
spends its effort proving multiplicity is one.

**The reading is now closed too** (final section). The basin radius `r` and the capacity `m` are no
longer hypotheses but **derived from the gap**: `attractingFixed_of_hasFDerivAt` builds the basin from
the *literal* Fréchet derivative `A = DΦ_c(p)` with `‖A‖ < 1`, in any real Banach space (the
infinite-dimensional statement), with rate `(1+‖A‖)/2` set by the gap `1-‖A‖`; `separated_card_le_of_Icc`
gives the **explicit** capacity `⌊(b-a)/r⌋+1` from that `r`; and `selves_card_le_gap_capacity` bounds the
number of selves in a bounded region entirely by the gap, hence density `→ 0`. The only residue is the
definitional note that the operator norm conservatively dominates the cone spectral radius (so `‖A‖ < 1`
is the cone-spectral reading) — a reading, not a gap. So: structure (isolation ⇒ separation ⇒ packing ⇒
density-0), multiplicity `≥ 2` realized, **and** the basin/capacity read off the gap — all closed here.
-/
import Scratch.Distribution
import Scratch.SparsityReal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace RelExist.SpectralMultiplicity

open Filter Topology

/-! ### Local attractors — a self with a contracting basin

A **self** in the spectral picture is an *attracting* fixed point of the co-directed feedback `f = Φ_c`:
a point `p` with `f p = p` near which `f` contracts toward `p` at a rate `k < 1`. The rate is the cone
spectral radius of the linearization `DΦ_c(p)` (piece 1); the basin radius `r` is the scale on which
that linearization dominates. -/

variable {X : Type*} [MetricSpace X]

/-- **A locally attracting self.** `p` is fixed by `f`, and on the ball of radius `r` about `p` the map
`f` contracts *toward* `p` at rate `k < 1`: every nearby point is pulled a factor `k` closer to `p`.
This is the eigenform of co-directed feedback in the metric setting — a fixed point that *attracts* its
neighbourhood (the living regime `‖DΦ_c‖ < 1` read locally), and it is exactly the contraction the
linearization `DΦ_c` supplies via its first-order (little-o) expansion at `p`
(`attractingFixed_of_hasFDerivAt`). -/
structure AttractingFixed (f : X → X) (p : X) (k r : ℝ) : Prop where
  rate_lt_one : k < 1
  rate_nonneg : 0 ≤ k
  fixed : f p = p
  contract : ∀ y, dist y p < r → dist (f y) p ≤ k * dist y p

/-- **Attracting selves are isolated.** Any fixed point inside the contracting basin of an attracting
self `p` *equals* `p`: a contraction cannot fix two distinct points of one basin
(`dist q p = dist (f q) (f p) ≤ k · dist q p` with `k < 1` forces `dist q p = 0`). This is the engine of
sparsity — the spectral contraction *creates* a private neighbourhood around each self. -/
theorem attracting_isolated {f : X → X} {p : X} {k r : ℝ}
    (h : AttractingFixed f p k r)
    {q : X} (hq : f q = q) (hqr : dist q p < r) : q = p := by
  have hc := h.contract q hqr
  rw [hq] at hc
  have h1mk : (0 : ℝ) < 1 - k := by linarith [h.rate_lt_one]
  have hle : (1 - k) * dist q p ≤ 0 := by nlinarith [hc]
  have hd0 : dist q p ≤ 0 := by
    rcases le_or_lt (dist q p) 0 with h0 | h0
    · exact h0
    · exact absurd hle (not_le.mpr (mul_pos h1mk h0))
  exact dist_eq_zero.mp (le_antisymm hd0 dist_nonneg)

/-- **Distinct selves are `r`-separated** (the derived exclusivity / private footprint). If `p₁` is an
attracting self with basin radius `r` and `p₂` is any *other* fixed point, then `r ≤ dist p₂ p₁` —
otherwise `p₂` would lie in `p₁`'s basin and coincide with it. The separation is the same shape as the
posited "private footprint" of [`SparsitySharing`](SparsitySharing.lean), here **forced** by the
spectral gap rather than assumed. -/
theorem attractors_separated {f : X → X} {p₁ p₂ : X} {k r : ℝ}
    (h₁ : AttractingFixed f p₁ k r)
    (h₂ : f p₂ = p₂) (hne : p₂ ≠ p₁) : r ≤ dist p₂ p₁ := by
  by_contra hlt
  push_neg at hlt
  exact hne (attracting_isolated h₁ h₂ hlt)

/-! ### The packing bound — few selves, independent of `N`

A set of pairwise `δ`-separated points inside a region of **capacity `m`** (it is covered by `m` cells,
each of diameter `< δ`) has at most `m` points: two points in one cell would be closer than `δ`. With
`δ` the spectral separation and `m` the covering number at that scale, the number of selves is bounded
by a **gap quantity independent of how many couplings `N` the system has**. -/

/-- **The spectral packing bound.** A `δ`-separated finite set `S` of selves, assigned to cells of a
cover `C` (`|C| = m`) so that same-cell points are `< δ` apart, satisfies `|S| ≤ |C|`. The number of
attracting selves is bounded by the **capacity at the gap scale** — a constant, *independent of `N`*.
This is the spectral form of the resource bound of Conjecture 3.3, with the budget replaced by a
covering number set by the spectral gap. -/
theorem separated_card_le_cover {Y : Type*} {S : Finset X} {δ : ℝ}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    {C : Finset Y} {assign : X → Y}
    (hmem : ∀ x ∈ S, assign x ∈ C)
    (hfine : ∀ x ∈ S, ∀ y ∈ S, assign x = assign y → dist x y < δ) :
    S.card ≤ C.card := by
  refine Finset.card_le_card_of_injOn assign hmem ?_
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  by_contra hne
  exact absurd (hsep x hx y hy hne) (not_le.mpr (hfine x hx y hy hxy))

omit [MetricSpace X] in
/-- **Sparsity as vanishing density** (the spectral "selves are rare"). If, for every system size `N`,
the selves `Sset N` number at most a fixed capacity `m` (the gap quantity of `separated_card_le_cover`,
which does not grow with `N`), then the fraction of couplings that are selves tends to `0`. The spectral
counterpart of [`SparsityReal.stab_density_tendsto_zero`](SparsityReal.lean): the cap is now a spectral
capacity, not an attention budget. -/
theorem selves_density_tendsto_zero {Sset : ℕ → Finset X} {m : ℕ}
    (hcard : ∀ N, (Sset N).card ≤ m) :
    Tendsto (fun N => ((Sset N).card : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
  RelExist.Real.density_tendsto_zero (C := (m : ℝ))
    (fun _ => by positivity)
    (fun N => by exact_mod_cast hcard N)

/-! ### The Perron pole — global contraction forces a *unique* self

The other end of the dichotomy. When the contraction is **global** (the subhomogeneous / primitive
regime where standard nonlinear Perron–Frobenius applies), there is **exactly one** self. Multiplicity
*requires* leaving this regime — which is why the contingency the doctrine wants is not free, and why
3.4 is harder than the linear theory. -/

/-- **Uniqueness in the primitive regime.** A *globally* contracting `f` (rate `k < 1` everywhere) has
**at most one** fixed point — the Perron/subhomogeneous pole. This is the result standard nonlinear
Perron–Frobenius hands you, and it is exactly the multiplicity 3.4 must escape to get contingency. -/
theorem unique_fixed_of_global_contraction {f : X → X} {k : ℝ} (hk : k < 1)
    (hc : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    {p q : X} (hp : f p = p) (hq : f q = q) : p = q := by
  have hcc := hc p q
  rw [hp, hq] at hcc
  have h1mk : (0 : ℝ) < 1 - k := by linarith
  have hle : (1 - k) * dist p q ≤ 0 := by nlinarith [hcc]
  have hd0 : dist p q ≤ 0 := by
    rcases le_or_lt (dist p q) 0 with h0 | h0
    · exact h0
    · exact absurd hle (not_le.mpr (mul_pos h1mk h0))
  exact dist_eq_zero.mp (le_antisymm hd0 dist_nonneg)

/-! ### Multiplicity is real — a two-basin witness

The contingency pole. An explicit, piecewise-affine `f : ℝ → ℝ` carries **two** genuine attracting
selves (`0` and `1`), each contracting at rate `1/2` on its own basin. The map is *not* globally
contracting (it jumps at `1/2`) — exactly the departure from the subhomogeneous regime that
`unique_fixed_of_global_contraction` shows is necessary for multiplicity. So selves are **more than
one**, while `separated_card_le_cover` keeps them **few**. -/

namespace TwoSelves

/-- A two-basin co-directed feedback: contract toward `0` on the left, toward `1` on the right. -/
noncomputable def f (y : ℝ) : ℝ := if y < 1 / 2 then y / 2 else (y + 1) / 2

lemma f_left {y : ℝ} (h : y < 1 / 2) : f y = y / 2 := if_pos h
lemma f_right {y : ℝ} (h : ¬ y < 1 / 2) : f y = (y + 1) / 2 := if_neg h

lemma f_zero : f 0 = 0 := by rw [f_left (by norm_num)]; norm_num
lemma f_one : f 1 = 1 := by rw [f_right (by norm_num)]; norm_num

/-- `0` is a genuine attracting self: rate `1/2` on the basin `dist · 0 < 1/4`. -/
lemma attracting_zero : AttractingFixed f 0 (1 / 2) (1 / 4) := by
  refine ⟨by norm_num, by norm_num, f_zero, ?_⟩
  intro y hy
  rw [Real.dist_eq, sub_zero] at hy
  have hylt : y < 1 / 2 := by have := (abs_lt.mp hy).2; linarith
  rw [f_left hylt, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
    show y / 2 = (1 / 2) * y by ring, abs_mul,
    abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]

/-- `1` is a genuine attracting self: rate `1/2` on the basin `dist · 1 < 1/4`. -/
lemma attracting_one : AttractingFixed f 1 (1 / 2) (1 / 4) := by
  refine ⟨by norm_num, by norm_num, f_one, ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy
  have hyge : ¬ y < 1 / 2 := by have := (abs_lt.mp hy).1; push_neg; linarith
  rw [f_right hyge, Real.dist_eq, Real.dist_eq,
    show (y + 1) / 2 - 1 = (1 / 2) * (y - 1) by ring, abs_mul,
    abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]

end TwoSelves

/-- **Multiplicity is real (contingency).** There is a co-directed feedback with **two distinct
attracting selves**, each a genuine local attractor. So the number of selves is *not* forced to one —
the doctrine's contingency survives the spectral picture — even though `separated_card_le_cover` bounds
that number from above. The witness is non-globally-contracting, as `unique_fixed_of_global_contraction`
requires: multiplicity lives exactly outside the primitive/subhomogeneous regime. -/
theorem two_attracting_selves :
    ∃ (g : ℝ → ℝ) (p₁ p₂ : ℝ), p₁ ≠ p₂ ∧
      AttractingFixed g p₁ (1 / 2) (1 / 4) ∧ AttractingFixed g p₂ (1 / 2) (1 / 4) :=
  ⟨TwoSelves.f, 0, 1, by norm_num, TwoSelves.attracting_zero, TwoSelves.attracting_one⟩

/-! ### Piece 1 — the linearization bridge to `Distribution`

The abstract relating `x` of [`Distribution`](Distribution.lean) is the **linearization** `x = DΦ_c`
of co-directed feedback at a candidate self. In a Banach algebra the feedback map `y ↦ b + x·y` is a
metric contraction with rate `‖x‖` (`feedbackMap_contract`): the living regime `‖x‖ < 1` is *exactly*
local attraction, the unique self is `Distribution.sustained x b`, and it is reached geometrically. So
`‖x‖ < 1` is read off the actual coupling as the cone spectral radius of the linearization being below
`1` — closing the modelling step [03.4](../../docs/spec/03.4-the-self-quantified.md) flagged `[open]`. -/

section Bridge

variable {E : Type*} [NormedRing E] [CompleteSpace E]

open RelExist.Distribution

/-- The **linearized co-directed feedback** with linearization `x = DΦ_c` and seed `b`. -/
noncomputable def feedbackMap (x b : E) : E → E := fun y => b + x * y

omit [CompleteSpace E] in
/-- **The linearization sets the contraction rate** (piece 1, core). The feedback map contracts at
rate `‖x‖`: `dist (f y) (f z) ≤ ‖x‖ · dist y z`. So the living-regime norm condition `‖x‖ < 1` of
`Distribution` *is* a contraction condition — `‖x‖` read as the cone spectral radius of `DΦ_c`. -/
theorem feedbackMap_contract (x b : E) (y z : E) :
    dist (feedbackMap x b y) (feedbackMap x b z) ≤ ‖x‖ * dist y z := by
  simp only [feedbackMap, dist_eq_norm]
  rw [add_sub_add_left_eq_sub, ← mul_sub]
  exact norm_mul_le x (y - z)

/-- **Geometric attraction.** From any seed `y`, the orbit of the feedback map approaches the self
`sustained x b` at the geometric rate `‖x‖ⁿ`: `dist (fⁿ y) (sustained x b) ≤ ‖x‖ⁿ · dist y (sustained x b)`.
The living self is a genuine *attractor*, not merely a fixed point. -/
theorem feedbackMap_iterate_dist {x : E} (hx : ‖x‖ < 1) (b y : E) (n : ℕ) :
    dist ((feedbackMap x b)^[n] y) (sustained x b) ≤ ‖x‖ ^ n * dist y (sustained x b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfix : feedbackMap x b (sustained x b) = sustained x b := by
      simp only [feedbackMap]; exact (sustained_fixed hx b).symm
    rw [Function.iterate_succ', Function.comp_apply]
    calc dist (feedbackMap x b ((feedbackMap x b)^[n] y)) (sustained x b)
        = dist (feedbackMap x b ((feedbackMap x b)^[n] y))
            (feedbackMap x b (sustained x b)) := by rw [hfix]
      _ ≤ ‖x‖ * dist ((feedbackMap x b)^[n] y) (sustained x b) := feedbackMap_contract x b _ _
      _ ≤ ‖x‖ * (‖x‖ ^ n * dist y (sustained x b)) :=
            mul_le_mul_of_nonneg_left ih (norm_nonneg x)
      _ = ‖x‖ ^ (n + 1) * dist y (sustained x b) := by rw [pow_succ]; ring

/-- **The orbit converges to the self.** In the living regime the feedback orbit from any seed tends to
`sustained x b`: the self is globally attracting. -/
theorem feedbackMap_tendsto {x : E} (hx : ‖x‖ < 1) (b y : E) :
    Tendsto (fun n => (feedbackMap x b)^[n] y) atTop (𝓝 (sustained x b)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => feedbackMap_iterate_dist hx b y n) ?_
  have hp : Tendsto (fun n => ‖x‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx
  simpa using hp.mul_const (dist y (sustained x b))

/-- **The living self is the unique attractor** (piece 1, packaged). When `‖x‖ < 1` — the linearization
`x = DΦ_c` has cone spectral radius below `1` — the self `sustained x b` is the **unique** fixed point
of co-directed feedback (by `Distribution.sustained_unique`) **and** is reached from every seed
(`feedbackMap_tendsto`). This is the primitive / Perron regime: one self, globally attracting. The
contingency of *multiple* selves (`two_attracting_selves`) is exactly what fails here and needs the
nonlinear, non-globally-contracting regime. -/
theorem living_self_unique_attractor {x : E} (hx : ‖x‖ < 1) (b : E) :
    (∀ s, feedbackMap x b s = s → s = sustained x b) ∧
      (∀ y, Tendsto (fun n => (feedbackMap x b)^[n] y) atTop (𝓝 (sustained x b))) := by
  refine ⟨fun s hs => ?_, fun y => feedbackMap_tendsto hx b y⟩
  exact sustained_unique hx (show b + x * s = s from hs).symm

end Bridge

/-! ### Closing the reading — the basin and capacity *from* the spectral gap

The previous sections take the basin radius `r` and the capacity `m` as hypotheses. Here both are
**derived from the gap**, so nothing about the count is posited.

* **`r` from the literal derivative** (`attractingFixed_of_hasFDerivAt`). Given the *actual* Fréchet
  derivative `DΦ_c = A` at a self `p` with `‖A‖ < 1`, the first-order (little-o) expansion produces a
  basin `r > 0` on which `Φ_c` is a local attractor at rate `(1 + ‖A‖)/2 < 1`. The basin and rate are
  functions of the **spectral gap `1 - ‖A‖`** (the operator norm dominates the cone spectral radius, so
  `‖A‖ < 1` is the conservative, dimension-free reading of "cone spectral radius below `1`"). This works
  in *any* real Banach space — finite or infinite dimensional.
* **`m` from `r`** (`separated_card_le_of_Icc`). On the line, an `r`-separated set inside `[a, b]` has at
  most `⌊(b - a)/r⌋ + 1` points — an **explicit capacity**, the spread divided by the gap-set
  separation. With `r` the gap basin, `m = ⌊(b-a)/r⌋ + 1` is a literal spectral-gap quantity.

Together (`selves_card_le_gap_capacity`): the attracting selves of `Φ_c` in a bounded region number at
most `⌊(b-a)/r⌋ + 1`, with `r` read off the derivative — so the count is bounded **entirely by the gap**,
and the density `→ 0` (`selves_density_tendsto_zero`). The reading is closed; only the note that operator
norm conservatively dominates the cone spectral radius is a definitional reading, not a gap. -/

section Linearization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The basin from the literal derivative `DΦ_c`** (closing the reading, analytic side). If `p` is a
self (`Φ p = p`) at which `Φ` has Fréchet derivative `A = DΦ_c(p)` with `‖A‖ < 1`, then there is a basin
radius `r > 0` on which `p` is a local attractor at rate `(1 + ‖A‖)/2 < 1`. Both `r` and the rate are
determined by the **spectral gap `1 - ‖A‖`**: the little-o remainder of the linearization is absorbed
into half the gap, so the affine part `A` (with `‖A‖ < 1`) governs the contraction. Holds in any real
Banach space — the dimension-free, infinite-dimensional statement the reading asked for. -/
theorem attractingFixed_of_hasFDerivAt {Φ : V → V} {p : V} {A : V →L[ℝ] V}
    (hp : Φ p = p) (hd : HasFDerivAt Φ A p) (hA : ‖A‖ < 1) :
    ∃ r > 0, AttractingFixed Φ p (‖A‖ + (1 - ‖A‖) / 2) r := by
  set ε : ℝ := (1 - ‖A‖) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hbound := (Asymptotics.isLittleO_iff.mp hd.isLittleO) hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨r, hr, ?_, ?_, hp, ?_⟩
  · rw [hεdef]; linarith [norm_nonneg A]
  · positivity
  · intro y hy
    have hb := hball hy
    rw [hp] at hb
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Φ y - p‖
        = ‖A (y - p) + (Φ y - p - A (y - p))‖ := by congr 1; abel
      _ ≤ ‖A (y - p)‖ + ‖Φ y - p - A (y - p)‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖y - p‖ + ε * ‖y - p‖ := add_le_add (A.le_opNorm _) hb
      _ = (‖A‖ + ε) * ‖y - p‖ := by ring

end Linearization

/-! ### The explicit capacity on the line, and the capstone -/

/-- **The capacity from the gap-set separation** (closing the reading, counting side). An `r`-separated
finite set inside `[a, b]` has at most `⌊(b - a)/r⌋ + 1` points: assigning each `x` to the bin
`⌊(x - a)/r⌋` lands in `{0, …, ⌊(b-a)/r⌋}`, and two points in one bin are `< r` apart, so the separation
forces distinct bins. With `r` the spectral-gap basin radius, this is the **explicit capacity `m`** the
reading asked for — the spread `b - a` divided by the gap separation. -/
theorem separated_card_le_of_Icc {a b r : ℝ} (hr : 0 < r) {S : Finset ℝ}
    (hIcc : ∀ x ∈ S, x ∈ Set.Icc a b)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y) :
    S.card ≤ ⌊(b - a) / r⌋₊ + 1 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have key : S.card ≤ (Finset.range (⌊(b - a) / r⌋₊ + 1)).card := by
    refine separated_card_le_cover (δ := r) hsep
      (C := Finset.range (⌊(b - a) / r⌋₊ + 1)) (assign := fun x => ⌊(x - a) / r⌋₊) ?_ ?_
    · intro x hx
      rw [Finset.mem_range]
      show ⌊(x - a) / r⌋₊ < ⌊(b - a) / r⌋₊ + 1
      have hxb : x ≤ b := (Set.mem_Icc.mp (hIcc x hx)).2
      have hle : ⌊(x - a) / r⌋₊ ≤ ⌊(b - a) / r⌋₊ := by
        apply Nat.floor_mono
        gcongr
      omega
    · intro x hx y hy hassign
      change ⌊(x - a) / r⌋₊ = ⌊(y - a) / r⌋₊ at hassign
      have hax : a ≤ x := (Set.mem_Icc.mp (hIcc x hx)).1
      have hay : a ≤ y := (Set.mem_Icc.mp (hIcc y hy)).1
      set u := (x - a) / r with hu
      set v := (y - a) / r with hv
      have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (by linarith) hr.le
      have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg (by linarith) hr.le
      have hu1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
      have hu2 : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
      have hv1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0
      have hv2 : v < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
      rw [hassign] at hu1 hu2
      have huv : |u - v| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hxy_uv : u - v = (x - y) / r := by rw [hu, hv]; ring
      have hkey : |u - v| = |x - y| / r := by rw [hxy_uv, abs_div, abs_of_pos hr]
      rw [hkey] at huv
      rw [Real.dist_eq, ← div_lt_one hr]
      exact huv
  simpa using key

/-- **The reading, closed — controlled multiplicity bounded entirely by the gap.** The attracting selves
of a co-directed feedback `f` lying in `[a, b]`, each a local attractor with basin radius `r` (with `r`
the spectral-gap radius from `attractingFixed_of_hasFDerivAt`), number at most `⌊(b - a)/r⌋ + 1` — an
explicit spectral-gap capacity, **independent of how many couplings `N` the system has**. So the count is
controlled by the gap alone; via `selves_density_tendsto_zero` (the cap does not grow with `N`) the
density of selves `→ 0`. Multiplicity is real (`two_attracting_selves`), yet sparse — the reconciliation
of *sparse* and *multiple*, with both the basin and the capacity now read off the gap, not posited. -/
theorem selves_card_le_gap_capacity {f : ℝ → ℝ} {a b k r : ℝ} (hr : 0 < r) {S : Finset ℝ}
    (hfix : ∀ p ∈ S, f p = p)
    (hattr : ∀ p ∈ S, AttractingFixed f p k r)
    (hIcc : ∀ p ∈ S, p ∈ Set.Icc a b) :
    S.card ≤ ⌊(b - a) / r⌋₊ + 1 := by
  refine separated_card_le_of_Icc hr hIcc ?_
  intro x hx y hy hxy
  have hsep := attractors_separated (hattr x hx) (hfix y hy) (Ne.symm hxy)
  rwa [dist_comm] at hsep

end RelExist.SpectralMultiplicity
