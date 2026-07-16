# WS15 — Phase 2: Design

## Triage (decidable on paper, per candidate)

| # | Candidate | Paper-decidable? | New math? | Risk | Lean cost | Consumers | Verdict |
|---|---|---|---|---|---|---|---|
| A1 | self-model former + Ω-fixed + eq-iff + properness-by-threshold | yes (pigeonhole + `mkState` interface; every step named) | no | low (subtype plumbing) | M | A2, A3, A7 | **select, wave 1** |
| A2 | self-model view misses a state | yes (carrier lower bound transfer) | no | none | XS | prose | **select, wave 2** |
| A3 | settled self-model (unique, dynamics-determined state per state) | yes (composition of `∃!` with a function) | no | low (hypothesis-bundle threading) | S | headline bundle | **select, wave 1** |
| A4 | linear family: unique fixed point + global convergence, all μ | yes — uniqueness fully (quadratic sign argument, both cases written); convergence decidable modulo standard monotone-convergence plumbing | no (elementary, but *new to the development*: removes a conjectured phenomenon) | medium (topology plumbing on the convergence half) | M/L | ledger, A7 note | **select, wave 1; convergence half pre-registered Partial** |
| A5 | coordination family: exact count via cubic factorization, sliver closed, threshold = 1/2 | yes (the factorization is a `ring` identity; side-root arithmetic checked on paper including floor bounds `√(1−2μ) ≤ 1−μ`) | no (but new: converts estimate-based landscape to root-count) | medium (`√` arithmetic volume; `coordFix` interface) | M | ledger | **select, wave 1** |
| A6 | orbit floor + ω-limit floor | yes (invariance + closedness) | no | low | S | ledger (small-μ regime) | **select, wave 1** |
| A7 | structural fitness instantiation | yes (pure instantiation) | no | none | XS | prose | **select, wave 2** |

Decision: wave **1 = {A1, A3, A4, A5, A6}**, wave **2 = {A2, A7}**. All seven selected — the workstream has no discard because Phase 1 already discarded at generation (no speculative candidates were emitted). Bundle name: `ws15_constitutive_attention`.

**Hard ordering constraint:** A1 consumes `mkState`/`str_mkState`/`mkState_str`/`mkState_inj` from the reification workstream (WS13 Block 0). WS13 must land first, or — pre-registered fallback — this file inlines a private `destEquivPk`-derived state-former with a deduplication note obligating a cleanup pass when WS13 merges. A4/A5/A6 have no carrier dependence and can execute in parallel with WS13 regardless.

---

## Proof architecture

**File:** `series-03/formal/ws15.lean`, namespace `Series03.WS15`, `import ws10, ws13` (ws10 transitively supplies ws5–ws9: `FlooredSimplex`, `mutT`, `SelectionMap`, `SelectionLipschitz`, `SelfSupport`, `selfSupportFintype`, the carrier-support convergence theorem, `coordIndF`, `coordFix`, the `≤ 3/8` multistability and `> 1/2` uniqueness theorems, `carrier_card_ge`; ws13 supplies the state-former). Scalar blocks (4, 5) are carrier-free and sit in their own section so they compile before the carrier blocks if WS13 is pending.

### Block 1 — the attended set (A1 support lemmas)

```lean
variable (u : (νPk κ₀).X) {μ : ℝ} {unif : SelfSupport κ₀ u → ℝ}

def attended (w : FlooredSimplex (SelfSupport κ₀ u) μ unif) (θ : ℝ) :
    Set (νPk κ₀).X := Subtype.val '' {r | θ ≤ w.1 r}

lemma attended_subset_support (w θ) : attended u w θ ⊆ ((νPk κ₀).str u).1
lemma attended_small (w θ) : Cardinal.mk ↥(attended u w θ) < κ₀
-- mk_le_mk_of_subset + the carrier's own bound ((νPk κ₀).str u).2
lemma exists_ge_avg (w : FlooredSimplex …) :
    ∃ r, (1 : ℝ) / Fintype.card (SelfSupport κ₀ u) ≤ w.1 r
-- pigeonhole from ∑ w = 1: if all entries < 1/n then ∑ < n · (1/n) = 1;
-- Finset.sum_lt_sum_of_nonempty; nonemptiness of the support index from hs
-- (a sum equal to 1 over an empty type is 0) — reuse the nonempty-instance
-- derivation already written inside the O6 proof (gap note 1: it is inline
-- there, not a lemma; extract it here as `selfSupport_nonempty` and offer
-- it upstream rather than copying).
lemma attended_nonempty (w) {θ} (hθ : θ ≤ 1 / Fintype.card (SelfSupport κ₀ u)) :
    (attended u w θ).Nonempty
```

Gap note 2: `FlooredSimplex` is a subtype whose first component is the weight function; confirm field name (`.1` vs named projection) at execute — every lemma above touches it.

### Block 2 — the self-model and its fixed-point structure (A1, A2)

```lean
noncomputable def selfModel (w θ) (h : (attended u w θ).Nonempty) : (νPk κ₀).X :=
  mkState ⟨attended u w θ, attended_small u w θ⟩

@[simp] lemma str_selfModel (w θ h) :
    ((νPk κ₀).str (selfModel u w θ h)).1 = attended u w θ   -- str_mkState

theorem ws15_selfModel_eq_iff (w θ h) :
    selfModel u w θ h = u ↔ attended u w θ = ((νPk κ₀).str u).1
-- (→) congrArg str + str_selfModel; (←) Subtype.ext then mkState_str.
theorem ws15_selfModel_ne (w θ h) (r) (hr : w.1 r < θ) : selfModel u w θ h ≠ u
-- r.val is in the support but not attended (θ-test fails); sets differ at r.val.
theorem ws15_omega_fixed {θ} (hθ : θ ≤ 1) (w) (h) : selfModel Ω w θ h = Ω
-- support of Ω is {Ω}; the simplex over a one-point type is {1}; 1 ≥ θ attends
-- the point; attended = {Ω} = str Ω; eq_iff closes. Gap note 3: the support-of-Ω
-- fact should exist near omegaCoalg (ws1) — locate the exact simp-form before
-- writing; if only the coalgebra-level fact exists, derive the carrier-level
-- image along the terminal hom first (one lemma, `str_omega_carrier`).
theorem ws15_selfModel_view_proper (w θ h) :
    ∃ v, v ∉ ((νPk κ₀).str (selfModel u w θ h)).1        -- A2
-- attended is finite; carrier is infinite (carrier_card_ge at ℵ₀);
-- a finite subset of an infinite type misses a point.
```

### Block 3 — the settled self-model (A3)

The convergence package is threaded as hypotheses, matching the O6 theorem verbatim so the `∃!` can be consumed without adaptation:

```lean
theorem ws15_settled (u μ hμ0 hμ1 unif hn hs sel sl hL) {θ}
    (hθ : θ ≤ 1 / Fintype.card (SelfSupport κ₀ u)) :
    ∃! v : (νPk κ₀).X, ∃ p : FlooredSimplex (SelfSupport κ₀ u) μ unif,
      mutT μ hμ0.le hμ1 unif hn hs sel p = p ∧
      ∃ h, v = selfModel u p θ h
```

Proof plan: destructure the O6 `∃!` into `⟨p★, hfix, huniq⟩`; existence with `p := p★`, `h := attended_nonempty …`; uniqueness: any `(v, p, hp, h, rfl)` has `p = p★` by `huniq`, then `v` is determined because `selfModel` is a function of `p` (nonemptiness proofs are propositionally irrelevant — `Subsingleton (Nonempty _)`; gap note 4: the `∃ h, v = …` shape is chosen precisely so proof-irrelevance closes uniqueness without `HEq` friction; if it still frictions, restate with `attended_nonempty` supplied definitionally instead of existentially). Corollary `ws15_settled_omega` composes with `ws15_omega_fixed`.

### Block 4 — linear family, exact landscape (A4; carrier-free section)

```lean
noncomputable def linIndF (c₁ c₂ μ x : ℝ) : ℝ :=
  (1 - μ) * (c₁ * x / (c₁ * x + c₂ * (1 - x))) + μ / 2
noncomputable def linN (c₁ c₂ μ x : ℝ) : ℝ :=      -- the cleared numerator
  (1 - μ) * c₁ * x + μ / 2 * (c₁ * x + c₂ * (1 - x)) - x * (c₁ * x + c₂ * (1 - x))
```

Lemma ladder:

```lean
lemma linD_pos (hc₁ hc₂) {x} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 < c₁*x + c₂*(1-x)
lemma linFix_iff_N (hc₁ hc₂ hx) : linIndF c₁ c₂ μ x = x ↔ linN c₁ c₂ μ x = 0
  -- field_simp against linD_pos
lemma linN_zero (…) : linN c₁ c₂ μ 0 = μ/2 * c₂        -- > 0
lemma linN_one (…)  : linN c₁ c₂ μ 1 = -(μ/2) * c₁     -- < 0
theorem ws15_lin_exists (…) : ∃ x ∈ Set.Icc (0:ℝ) 1, linIndF c₁ c₂ μ x = x
  -- intermediate_value_Icc on the continuous linN (continuity: polynomial)
theorem ws15_lin_unique (hc₁ hc₂ hμ0 hμ1) :
    ∃! x, x ∈ Set.Icc (0:ℝ) 1 ∧ linIndF c₁ c₂ μ x = x
```

Uniqueness proof plan (the one subtle block): suppose `p ≠ q` are two interior fixed points (endpoints excluded by `linN_zero/one ≠ 0`). `linN` is a quadratic in `x` with leading coefficient `a = c₂ − c₁`. Case `a = 0`: `linN` is affine with two roots, hence identically zero, contradicting `linN 0 ≠ 0`. Case `a ≠ 0`: with roots `p, q`, `linN x = a(x−p)(x−q)` (obtain by `Polynomial` factorization or — leaner — by direct algebra: define `a(x−p)(x−q)` and prove equality via three-point interpolation `nlinarith`; gap note 5: pre-commit to the *non-`Polynomial`* route: from `linN p = 0`, `linN q = 0`, expand `linN x − a(x−p)(x−q)` as a linear function vanishing at two distinct points, hence zero — pure `ring_nf`/`linarith` over the coefficients, no `Polynomial` API). Then `linN 0 = a·p·q` and `linN 1 = a(1−p)(1−q)` with `p, q ∈ (0,1)` have the same sign — contradicting `linN_zero > 0 > linN_one`.

Convergence half:

```lean
lemma linIndF_strictMono (hc₁ hc₂ hμ0 hμ1') :        -- hμ1' : μ < 1 needed here;
    StrictMonoOn (linIndF c₁ c₂ μ) (Set.Icc 0 1)     -- at μ = 1 the map is constant
                                                     -- and convergence is one step
-- x < y → linIndF x < linIndF y reduces (field_simp, positivity of both
-- denominators) to (1−μ)·c₁·c₂·(y−x) > 0.
lemma lin_maps_into (…) : Set.MapsTo (linIndF c₁ c₂ μ) (Set.Icc 0 1) (Set.Icc 0 1)
lemma lin_above_below (…) :  -- sign of linN off the fixed point
    (∀ x ∈ Set.Ico 0 p, x < linIndF c₁ c₂ μ x) ∧ (∀ x ∈ Set.Ioc p 1, linIndF c₁ c₂ μ x < x)
theorem ws15_lin_global (…) (x₀) (hx₀) :
    Filter.Tendsto (fun n => (linIndF c₁ c₂ μ)^[n] x₀) Filter.atTop (nhds p)
```

Convergence proof plan: for `x₀ < p` the orbit is strictly increasing (`lin_above_below`) and bounded above by `p` (strict mono keeps order with the fixed point); `tendsto_atTop_ciSup` for monotone bounded sequences gives a limit `L ≤ p`; continuity of `linIndF` at `L` (`ContinuousOn` from `linD_pos`) makes `L` a fixed point; uniqueness forces `L = p`. Mirror case above; `x₀ = p` trivial; `μ = 1` case: `linIndF = 1/2 + const` — constant map, orbit is eventually constant. **Pre-registered Partial (from triage and the BR):** if the monotone-limit-is-fixed-point plumbing exceeds budget at the pin, `ws15_lin_unique` ships alone; `lin_above_below` still ships (it is the mathematical content of attraction); the `Tendsto` statement is declared Partial with its two supporting lemmas in place. The uniqueness theorem alone already discharges the landscape claim (no linear multistability at any μ).

### Block 5 — coordination family, exact count (A5; carrier-free section)

```lean
lemma coord_cubic_factor (μ x : ℝ) :
    2*x^3 - 3*x^2 + (1+μ)*x - μ/2 = (x - 1/2) * (2*x^2 - 2*x + μ) := by ring
lemma coordD_pos (x : ℝ) : (0:ℝ) < x^2 + (1-x)^2 ∨ … -- ≥ 1/2 on ℝ; nlinarith
lemma coordFix_iff_cubic {μ x} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    coordIndF μ x = x ↔ 2*x^3 - 3*x^2 + (1+μ)*x - μ/2 = 0   -- field_simp
noncomputable def xPlus (μ : ℝ) : ℝ := (1 + Real.sqrt (1 - 2*μ)) / 2
noncomputable def xMinus (μ : ℝ) : ℝ := (1 - Real.sqrt (1 - 2*μ)) / 2
```

Side-root ladder (all `Real.sq_sqrt`-driven, hypotheses `0 < μ`, `μ < 1/2` throughout):

```lean
lemma sqrt_mem : Real.sqrt (1 - 2*μ) ∈ Set.Ioo (0:ℝ) 1
lemma xPM_mem : xPlus μ ∈ Set.Ioo (1/2 : ℝ) 1 ∧ xMinus μ ∈ Set.Ioo (0:ℝ) (1/2)
lemma xPM_quad : 2*(xPlus μ)^2 - 2*(xPlus μ) + μ = 0 ∧ (same for xMinus)
lemma xPM_floor : μ/2 ≤ xMinus μ ∧ xPlus μ ≤ 1 - μ/2
-- both reduce to √(1−2μ) ≤ 1−μ, i.e. 1−2μ ≤ (1−μ)², i.e. 0 ≤ μ²:
-- Real.sqrt_le_left-style via Real.sqrt_le_sqrt of the squared inequality,
-- legitimate since 1−μ ≥ 0.
theorem ws15_multistable_below_half (hμ0 : 0 < μ) (hμ : μ < 1/2) :
    -- three distinct fixed points of coordIndF in Icc 0 1: xMinus, 1/2, xPlus
theorem ws15_coord_unique_ge_half (hμ : 1/2 ≤ μ) (hμ1 : μ ≤ 1) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x → x = 1/2
-- cubic = 0 → (x−1/2)(2x²−2x+μ) = 0; second factor = 2(x−1/2)² + (μ−1/2) + …:
-- rewrite 2x²−2x+μ = 2(x−1/2)² + (μ − 1/2) ≥ 0 with equality iff x = 1/2 ∧ μ = 1/2;
-- either way x = 1/2.
theorem ws15_multistable_iff (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∃ x ∈ Set.Icc (0:ℝ) 1, coordIndF μ x = x ∧ x ≠ 1/2) ↔ μ < 1/2
```

Simplex lift: reuse `coordFix` exactly as `ws9_multistable_interval` does — gap note 6: `coordFix`'s hypotheses (read at execute: `hμ0`, `hμ1`, two bounds on `x`, and the scalar fixed-point equation) must be fed `xPM_mem` + `xPM_floor`; the `≤ 3/8` proof is the template — copy its invocation shape, swapping the root witnesses. If `coordFix` demands bounds in the closed floor form (`μ/2 ≤ x ≤ 1−μ/2`), `xPM_floor` supplies them directly; that is why the floor lemma is in the mandatory ladder rather than optional.

**Ledger note carried into the report phase:** together with the existing `> 1/2` uniqueness theorem, the count is exact at every `μ ∈ (0,1]`; the `≤ 3/8` interval theorem becomes a corollary of `ws15_multistable_below_half` and should be marked superseded-but-retained (no deletion of proved results).

### Block 6 — orbit floor (A6)

```lean
theorem ws15_orbit_floor (μ hμ0 hμ1 unif hn hs sel)
    (w : FlooredSimplex S μ unif) (n : ℕ) (r : S) :
    μ * unif r ≤ (((mutT μ hμ0.le hμ1 unif hn hs sel)^[n] w) : FlooredSimplex S μ unif).1 r
-- if mutT's codomain is FlooredSimplex (expected from its use in the ∃! theorems),
-- this is Function.iterate_succ' + the subtype invariant of the n-th iterate:
-- induction is over n with *no analytic content*.
theorem ws15_omega_limit_floor (…) (p : S → ℝ)
    (hp : MapClusterPt p atTop (fun n => ((mutT …)^[n] w).1)) (r : S) :
    μ * unif r ≤ p r
-- the set {v | μ·unif r ≤ v r} is closed (isClosed_le of continuous coordinates);
-- cluster points of a sequence eventually (here: always) in a closed set belong
-- to it: hp.frequently + closure characterization, per coordinate.
```

Gap note 7: confirm `mutT`'s codomain at execute. If it is the raw function type with the invariant proved separately, the invariance lemma `mutT_mem_floored` becomes the first item of this block (its proof: `mutT` is the convex combination `(1−μ)·sel(w) + μ·unif`-shaped map; the floor term contributes `μ·unif r` directly, the selection term is nonneg) — this re-scoping was pre-registered in the BR and does not change the two theorem statements.

### Block 7 — wave 2 (A2 already in Block 2; A7)

```lean
noncomputable def structFitness (u) : SelfSupport κ₀ u → ℝ :=
  fun r => (Fintype.card ((νPk κ₀).str r.val).1 : ℝ) + 1
theorem ws15_struct_fitness_pos (u r) : 0 < structFitness u r
theorem ws15_struct_replicator_converges (u μ …) (hband : 2*(1-μ) < μ * uMin unif) :
    ∃! p : FlooredSimplex (SelfSupport κ₀ u) μ unif, …
-- instantiation of the banded linear-replicator theorem at c := structFitness u
-- on the carrier support; Fintype instance is selfSupportFintype.
```

Honesty condition (pre-registered): the band hypothesis stays visible in the statement; the accompanying comment cites Block 4's uniqueness as the reason the band is *not* believed necessary, without claiming the banded theorem's convergence off-band (that transfer — Banach off, monotone on — is only proved in the 2-point scalar reduction, Block 4, and the note must say exactly that).

## Headline bundle

```lean
structure WS15Bundle where               -- all fields proofs; no status tags
  omega_fixed      : …                   -- ws15_omega_fixed
  selfModel_eq_iff : …
  settled          : …                   -- ws15_settled
  lin_unique       : …                   -- ws15_lin_unique
  coord_iff        : …                   -- ws15_multistable_iff
  orbit_floor      : …                   -- ws15_omega_limit_floor
theorem ws15_constitutive_attention : WS15Bundle := …
```

Per the bundle discipline: proof fields only; if A4's convergence half lands it is *added* as a field, and if it goes Partial it is **absent**, not tagged — the Partial is recorded in the report document, never in the record type.

## Dependencies and ordering

```
Blocks 4, 5, 6 (scalar/simplex; carrier-free) ── executable immediately, parallel
Blocks 1–3, 7 ── after WS13 Block 0 merges (or inline fallback with cleanup note)
Wave 2 (A2 statement in Block 2 ships with it; A7 in Block 7) ── last
```

Upstream theorems consumed, by name: `mkState`/`str_mkState`/`mkState_str`/`mkState_inj` (ws13); `SelfSupport`, `selfSupportFintype`, carrier-support convergence `∃!` (ws10 / O6); `FlooredSimplex`, `mutT`, `SelectionMap`, `SelectionLipschitz`, `uMin`, banded linear-replicator convergence (ws7/ws8); `coordIndF`, `coordFix`, `≤ 3/8` multistability (superseded), `> 1/2` uniqueness (ws9/ws10); `carrier_card_ge` (ws10). Exports offered: `selfModel` and its fixed-point lemmas (any later self-reference work), the exact per-family landscape (summaries), `ws15_omega_limit_floor` (any later ergodic work).

## Risk register

1. **WS13 ordering** — hard dependency for Blocks 1–3, 7; inline-fallback pre-registered; scalar blocks unaffected.
2. **A4 convergence plumbing** — the one triage-flagged Partial; uniqueness half is safe and independently sufficient for the landscape claim.
3. **`coordFix` interface shape** (gap note 6) — template invocation exists; worst case is a locally proved widened reconstruction lemma.
4. **`√` arithmetic volume in Block 5** — bounded: four lemmas, all reducible to squared inequalities with `1−μ ≥ 0` side conditions.
5. **`mutT` codomain** (gap note 7) — re-scoping pre-registered; statements unchanged.
6. **Proof-irrelevance friction in `ws15_settled`** (gap note 4) — statement shaped to avoid `HEq`; fallback restatement named.
7. **Ω support form** (gap note 3) — one bridging lemma if the carrier-level simp-form is missing.
