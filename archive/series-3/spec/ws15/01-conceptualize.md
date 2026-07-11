# WS15 — Phase 1: Conceptualize

## What is at stake, mathematically

Two separate deficits, one workstream because they share machinery.

**Deficit 1 (structure).** The development has a convergence theory for attention *weights* on a fixed finite support (`FlooredSimplex`, `mutT`, the selection-map hierarchy, and the carrier-support convergence theorem at `ℵ₀`), and it has a carrier whose states are in bijection with their own `< κ` unfoldings (`lambek`). But no construction sends a weight vector back into the carrier: the output of the dynamics never becomes a *state*. The missing object is a map `(state, attention, threshold) → state` — a self-model former — such that theorems about the dynamics become theorems about carrier elements. Non-trivial because the map must land in the carrier (a `< κ` smallness and a nonemptiness obligation), must interact correctly with the unique fixed points supplied by the convergence theorems, and must have provable fixed-point structure of its own.

**Deficit 2 (dynamics landscape).** The convergence results are band-conditional (`2(1−μ) < μ·u_min`, i.e. `μ > μ⋆`) for the linear replicator, while the multistability counterexamples live in a *different* family (frequency-dependent coordination, `coordIndF`), currently established only on `μ ∈ (0, 3/8]` against a uniqueness result on `(1/2, 1]`. Three precise gaps: (i) is the linear family's band *necessary*, or a method artifact? (ii) what happens on the coordination family's sliver `μ ∈ (3/8, 1/2)`? (iii) is there any positive orbit-level statement in the small-μ regime, where only fixed-point-level facts (`ws5_no_delta`) exist? Non-trivial because (i) and (ii) require exact fixed-point counts, not Lipschitz estimates — the Banach method cannot answer either.

Ambient theory throughout: Lean 4 + Mathlib at the repo pin; classical logic; the `Cofix`/QPF terminal coalgebra of the `< κ` powerset functor at `κ₀ = ℵ₀` for candidates A1–A3, A6–A7 (functor `F = P_{ℵ₀}`; no monad or distributive law at stake); bare real analysis on `[0,1]` and finite simplices for A4–A5. Upstream interface assumed: `lambek`-derived state-former (`mkState`, `str_mkState`, `mkState_str`, `mkState_inj` — exported by the reification workstream), `SelfSupport`, `selfSupportFintype`, `FlooredSimplex`, `mutT`, `SelectionMap`/`SelectionLipschitz`, the carrier-support convergence theorem, `coordIndF`, `coordFix`, the `μ ≤ 3/8` multistability and `μ > 1/2` uniqueness theorems.

---

## A1 — The self-model former

**Object.** For `u` a state of the `ℵ₀`-carrier, `w` a floored attention vector on `SelfSupport u`, and threshold `θ`, the θ-attended sub-support is a subset of the (finite) support; by the state-former it *is* a state.

```lean
def attended (u : (νPk κ₀).X) (w : FlooredSimplex (SelfSupport κ₀ u) μ unif)
    (θ : ℝ) : Set (νPk κ₀).X :=
  Subtype.val '' {r : SelfSupport κ₀ u | θ ≤ w.1 r}

lemma attended_small … : Cardinal.mk ↥(attended u w θ) < κ₀
lemma attended_nonempty (hθ : θ ≤ 1 / Fintype.card (SelfSupport κ₀ u)) … :
    (attended u w θ).Nonempty

noncomputable def selfModel (u w θ) (h : (attended u w θ).Nonempty) : (νPk κ₀).X :=
  mkState ⟨attended u w θ, attended_small …⟩
```

**Strategy.** Smallness: subset of the support, which is `< ℵ₀` by the carrier's own bound. Nonemptiness: the entries of `w` sum to 1 over `n = card (SelfSupport u)` points, so some entry is `≥ 1/n` (average/pigeonhole: `Finset.exists_le_of_sum_le` shape); any `θ ≤ 1/n` admits it. No uniformity assumption on `unif` is needed for this.

**Companion theorems (the point of the construction):**

```lean
theorem ws15_omega_fixed (θ) (hθ : θ ≤ 1) (w) : selfModel Ω w θ … = Ω
-- Ω's support is {Ω}; any probability vector on a singleton is the point mass 1;
-- θ ≤ 1 keeps the single point attended; mkState_str closes.
theorem ws15_selfModel_eq_iff (u w θ h) :
    selfModel u w θ h = u ↔ attended u w θ = ((νPk κ₀).str u).1
-- mkState_inj + mkState_str: the self-model IS the object iff attention θ-covers
-- the entire support.
theorem ws15_selfModel_ne (u w θ h)
    (hmiss : ∃ r : SelfSupport κ₀ u, w.1 r < θ) : selfModel u w θ h ≠ u
-- contrapositive of eq_iff: a single sub-threshold successor makes the
-- self-model a *different* state — a strictly partial image.
```

**Success:** all four; the dynamics' output re-enters the carrier, with `Ω` a fixed point and properness exactly characterized. **Failure:** `attended_nonempty` false as stated would mean the average argument miscarries (arithmetic error, not mathematical obstruction — the fallback threshold is `θ ≤ μ · min unif`, which the floor makes trivially admissible); a genuine failure mode is only definitional: if `FlooredSimplex`'s carrier field is not literally a function on `SelfSupport` (subtype plumbing), `attended` is re-typed, not abandoned.

**Trade-off.** Everything downstream (A2, A3, A7) consumes this; it is the mandatory node. Cost is small; the only real content is the pigeonhole lemma and the `mkState` interface.

## A2 — Properness of the self-model view (cheap corollary)

```lean
theorem ws15_selfModel_view_proper (u w θ h) :
    ∃ v : (νPk κ₀).X, v ∉ ((νPk κ₀).str (selfModel u w θ h)).1
```

**Strategy.** The self-model's unfolding is the attended set, of cardinality `< ℵ₀ ≤ #carrier` (the carrier lower bound); a set smaller than the type misses a point. **Success/failure:** immediate transfer; failure not expected. **Trade-off:** two lines given A1; include for the record, schedule last.

## A3 — The settled self-model

**Object.** Compose A1 with the carrier-support convergence theorem: under its hypothesis package (nonexpansive selection on `u`'s own support), attention has a *unique* fixed point `p★`; the settled self-model of `u` is `selfModel u p★ θ`.

```lean
noncomputable def settledSelfModel (u : (νPk κ₀).X) (…convergence package…) (θ) : (νPk κ₀).X
theorem ws15_settled_unique (u …) :
    ∃! v : (νPk κ₀).X, ∃ p, (isFixedPt p ∧ v = selfModel u p θ …)
theorem ws15_settled_omega … : settledSelfModel Ω … θ = Ω
```

**Strategy.** Uniqueness is inherited verbatim from the `∃!` of the convergence theorem; the map from fixed attention to state is a function, so the composite is unique. `Ω`'s case composes with A1's fixed-point theorem. **Success:** a canonical, dynamics-determined state assigned to every state satisfying the package. **Failure:** none mathematical; the risk is only that the convergence theorem's hypothesis bundle (selection map + Lipschitz witness + `L ≤ 1`) is heavy to thread — if the bundle resists clean packaging, ship the theorem with the hypotheses inline and flag the interface for refactor. **Trade-off:** the payoff item that makes A1 more than a definition; cost small once A1 lands.

## A4 — Linear family: global uniqueness and convergence for **all** μ (band-freeness)

**Object.** The 2-strategy mean-field map of the linear replicator with mutation, `linIndF c₁ c₂ μ x := (1−μ) · (c₁x)/(c₁x + c₂(1−x)) + μ/2` on `[0,1]`, `c₁, c₂ > 0`. Claim: for every `μ ∈ (0,1]` the fixed point is **unique** and **globally attracting** — the contraction band `μ > μ⋆` of the Lipschitz method is an artifact of the method, not a phase boundary.

```lean
noncomputable def linIndF (c₁ c₂ μ x : ℝ) : ℝ :=
  (1 - μ) * (c₁ * x / (c₁ * x + c₂ * (1 - x))) + μ / 2
theorem ws15_lin_unique (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃! x, x ∈ Set.Icc (0:ℝ) 1 ∧ linIndF c₁ c₂ μ x = x
theorem ws15_lin_global (… same …) (x₀) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    Filter.Tendsto (fun n => (linIndF c₁ c₂ μ)^[n] x₀) Filter.atTop (nhds xFix)
```

**Strategy.** Uniqueness: on `[0,1]` the denominator `D(x) = c₁x + c₂(1−x)` is positive; the fixed-point equation clears to a **quadratic** `N(x) := (1−μ)c₁x + (μ/2)D(x) − xD(x) = 0` with `N(0) = (μ/2)c₂ > 0` and `N(1) = −(μ/2)c₁ < 0`. IVT gives existence. Uniqueness: if the leading coefficient `c₂ − c₁` vanishes, `N` is linear — done; otherwise a quadratic with both roots in `(0,1)` has `N(0) = a·r₁r₂` and `N(1) = a(1−r₁)(1−r₂)` of the *same* sign, contradicting `N(0)N(1) < 0` — so exactly one root lies in `(0,1)`. Pure polynomial sign arithmetic, `nlinarith`-shaped. Global convergence: `linIndF` is strictly increasing on `[0,1]` (cross-multiplied derivative-free inequality: `x < y → linIndF x < linIndF y` reduces to `c₁c₂(y−x) > 0`); a strictly increasing self-map of `[0,1]` with unique fixed point `p` has `f(x) > x` on `[0,p)` and `f(x) < x` on `(p,1]` (sign of `N`), so orbits are monotone and bounded, converge by monotone convergence, and the limit is a fixed point by continuity, hence `p`.

**Success:** both theorems; the linear family is proved to have **no** multistability at any μ — the necessity question (i) is answered *negatively*, and the necessity phenomena in the development become exclusive to the frequency-dependent family. **Failure conditions, pre-registered:** if a second interior root is exhibited (the sign argument would have to be wrong — not expected), the reportable outcome inverts to a linear-family multistability witness; if the convergence half's topology plumbing (monotone convergence + continuity at the pin) exceeds budget, uniqueness ships alone and convergence is declared Partial with the monotone-orbit lemma stated. **Trade-off:** self-contained scalar analysis, no carrier dependence; the highest information-per-line item in the workstream — it *removes* a conjectured phenomenon rather than adding a theorem about one family more.

## A5 — Coordination family: exact fixed-point count, closing the sliver

**Object.** For `coordIndF μ x = (1−μ)·x²/(x²+(1−x)²) + μ/2`: the fixed-point equation on `[0,1]` clears (positive denominator `D(x) = 2x² − 2x + 1 ≥ 1/2`) to the cubic `2x³ − 3x² + (1+μ)x − μ/2 = 0`, which **factors exactly**:

```
2x³ − 3x² + (1+μ)x − μ/2 = (x − 1/2)(2x² − 2x + μ)
```

so the fixed points are `1/2` and `(1 ± √(1−2μ))/2` — real and distinct from `1/2` **iff μ < 1/2**.

```lean
lemma ws15_coord_cubic_factor (μ x : ℝ) :
    2*x^3 - 3*x^2 + (1+μ)*x - μ/2 = (x - 1/2) * (2*x^2 - 2*x + μ)   -- ring
theorem ws15_multistable_below_half (hμ0 : 0 < μ) (hμ : μ < 1/2) :
    ∃ x₁ x₂ x₃, x₁ ≠ x₂ ∧ x₂ ≠ x₃ ∧ x₁ ≠ x₃ ∧
      (∀ i ∈ [x₁,x₂,x₃], i ∈ Set.Icc (0:ℝ) 1 ∧ coordIndF μ i = i)
theorem ws15_coord_unique_ge_half (hμ : 1/2 ≤ μ) (hμ1 : μ ≤ 1) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x → x = 1/2
theorem ws15_multistable_iff (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x ∧ x ≠ 1/2) ↔ μ < 1/2
```

**Strategy.** The factorization is a `ring` identity. Below `1/2`: side roots `x± = (1 ± √(1−2μ))/2` with `0 < 1−2μ`, hence `√(1−2μ) ∈ (0,1)` and `x± ∈ (0,1)`; verify `coordIndF μ x± = x±` by clearing `D(x±) > 0` and citing the factorization with `2x±² − 2x± + μ = 0` (`Real.sq_sqrt` arithmetic). Floor-compatibility of the roots (`x± ≥ μ/2` and `1 − x± ≥ μ/2`) reduces to `√(1−2μ) ≤ 1−μ`, i.e. `1−2μ ≤ (1−μ)²`, i.e. `μ² ≥ 0`. At or above `1/2`: the quadratic factor has no real root other than possibly the double point, so the cubic's only root in `[0,1]` is `1/2` — sign argument on `2x²−2x+μ ≥ μ − 1/2 ≥ 0` with equality analysis. Lifting scalar fixed points to simplex fixed points reuses the existing reconstruction lemma (`coordFix`) exactly as the `μ ≤ 3/8` theorem did.

**Success:** the sliver `(3/8, 1/2)` closes in the multistable direction, and combined with the ≥ 1/2 side the count is exact for **all** μ: the bifurcation threshold is precisely `1/2`, by root-counting rather than estimate. **Failure conditions:** the factorization is machine-checkable, so failure can only come from (a) `coordFix`'s hypothesis shape not matching the side roots — fallback: prove a widened reconstruction lemma locally; (b) `√`-arithmetic budget — fallback: ship `ws15_multistable_below_half` for the closed sliver only (`3/8 < μ < 1/2`), which is the missing interval, and leave the unified iff as an assembly of citations. **Trade-off:** with A4 this completes the per-family landscape: uniqueness-always (linear) vs threshold-at-1/2 (coordination), both exact.

## A6 — Orbit-level floor: positivity along trajectories, all μ

**Object.** Extend the fixed-point-level positivity fact (`ws5_no_delta`: no vertex/delta fixed point at any `μ > 0`) to *orbits and their limit points*: every iterate of the mutation step keeps every coordinate `≥ μ·unif r`, hence every ω-limit point does too — no trajectory collapses toward a vertex, at any μ, in particular in the small-μ regime where no convergence theorem applies.

```lean
theorem ws15_orbit_floor (μ hμ0 hμ1 unif hn hs sel) (w : FlooredSimplex S μ unif) (n : ℕ) (r : S) :
    μ * unif r ≤ ((mutT μ hμ0.le hμ1 unif hn hs sel)^[n] w).1 r
theorem ws15_omega_limit_floor (… w …) (p : S → ℝ)
    (hp : MapClusterPt p Filter.atTop (fun n => ((mutT …)^[n] w).1)) (r : S) :
    μ * unif r ≤ p r
```

**Strategy.** `mutT` endomaps the floored simplex (its codomain should already be `FlooredSimplex`; if so the first theorem is definitional unfolding of the subtype invariant plus induction on `n`). Limit points: the constraint set `{v | ∀ r, μ·unif r ≤ v r}` is closed; cluster points of a sequence in a closed set lie in it (`le_of_tendsto` per coordinate along the subsequence filter). **Success:** the first orbit-level theorem in the regime below every band. **Failure:** only if `mutT`'s Lean type does *not* preserve the floor (then the floor-preservation lemma is the actual content — prove it from the definition: convex combination of a simplex point with `μ·unif`); pre-registered as a re-scoping, not a failure. **Trade-off:** small cost; modest but genuine — it is the only candidate that says anything positive for every μ.

## A7 — Structurally sourced fitness (demonstration)

**Object.** Instantiate the selection machinery with fitness read off the *carrier's own structure*: `c r := card (str r).1 + 1` (out-degree plus one, on a state's finite support at `ℵ₀`), so the dynamics' exogenous fitness parameter becomes endogenous.

```lean
noncomputable def structFitness (u) : SelfSupport κ₀ u → ℝ :=
  fun r => (Fintype.card ((νPk κ₀).str r.val).1 : ℝ) + 1
theorem ws15_struct_fitness_pos (u) : ∀ r, 0 < structFitness u r
theorem ws15_struct_replicator_converges (u) (μ …) (hband : …) :
    ∃! p : FlooredSimplex (SelfSupport κ₀ u) μ unif, …  -- linear replicator with
                                                        -- c := structFitness u
```

**Strategy.** Positivity by `Nat.cast_nonneg` + 1; the convergence theorem is the existing banded linear-replicator theorem applied at `c := structFitness u` on the carrier support (the `Fintype` instance already exists). **Success:** the fitness input is a function of the coalgebra structure — closing the "exogenous `c`" gap by exhibition. **Failure:** none mathematical (pure instantiation); the pre-registered honesty condition is that the theorem *inherits the band* — it must be stated with the band hypothesis visible, and with A4 available the band can be discharged on the 2-element-support case only; no claim beyond that. **Trade-off:** cheap, demonstration-grade; include in the second wave.

---

## Trade-offs across candidates

A1 is the mandatory node and the only genuinely *new* construction; A3 is its payoff and inherits uniqueness for free; A2 and A7 are cheap corollaries riding A1 and existing machinery. A4 and A5 are independent of the carrier entirely and jointly convert the dynamics landscape from "bands here, counterexamples there" into two exact per-family statements — A4 subtracts a phenomenon (no linear multistability, ever), A5 pins a threshold (coordination bifurcates at exactly 1/2). A6 is the only candidate speaking below all bands, at orbit level. Nothing here needs a monad, a distributive law, or any functor beyond `P_{ℵ₀}`; the heaviest risks are Mathlib plumbing (A4's convergence topology, A5's `√` arithmetic), both with shipped-Partial fallbacks pre-registered.
