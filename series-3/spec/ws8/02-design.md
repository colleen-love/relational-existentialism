# Triage and Design: Selected Candidates per Obligation

## Part 0 — Triage protocol (decidable on paper)

Each candidate is scored on six checks, every one settleable without running Lean, by inspection of the imported artifact. A candidate **passes triage** iff it is not `DEAD` on any check and has no `FATAL` risk with no fallback. The framing decision (Part 2) is taken *after* triage (Part 1) and only among passing candidates.

The six checks:

- **T1 — Well-typed against real API.** Does the signature reference only symbols that exist, or symbols whose definitions are supplied by the design itself? `PHANTOM` = depends on a symbol that neither exists nor is constructible from what exists.
- **T2 — Upstream sufficiency.** Are the imported theorems it leans on strong enough as stated (not merely morally)? `GAP` = needs an upstream lemma in a form not proved.
- **T3 — Truth on paper.** Can the proposition's truth-value be decided by a finite hand-argument on a fixed witness? `T` (true), `F` (false), `OPEN` (genuinely undecided by inspection).
- **T4 — Proof-length class.** `TRIVIAL` (one lemma), `SHORT` (≤ ~5 lemmas, no new analysis), `MEDIUM` (new construction, bounded), `HARD` (open analytic/combinatorial core).
- **T5 — Criterion coupling.** Does success actually discharge (or advance to a valid terminal outcome) the charter criterion the obligation blocks? `ON` / `OFF-TARGET` / `RELOCATES`.
- **T6 — Failure disposition.** If it fails, is the failure itself a valid §5 outcome (impossibility/characterization), or dead loss? `VALID-NEG` / `DEGRADES` / `LOSS`.

---

## Part 1 — Triage tables

### Obligation A — weighted weak-pullback preservation (`WQPreservesWeakPullback`)

| Cand | T1 type | T2 upstream | T3 truth | T4 length | T5 coupling | T6 failure | Verdict |
|---|---|---|---|---|---|---|---|
| **A1** full divisible | OK | `PkRel_comp_le` shape reusable; `weight_split` only splits `w ≤ a` | **OPEN, leaning F** (residual runs out when middle mass `< 1`) | HARD | ON | VALID-NEG (→A5) | **at-risk** |
| **A2** normalized subfunctor | OK | needs `Normalized` a subcoalgebra of `Cofix W_Q` — not proved | **OPEN** (subcoalgebra closure unknown) | MEDIUM | ON *iff* T2 holds | DEGRADES | hold |
| **A3** lax `≤`-lifting | OK | monotonicity only (`mul_mono_right` exists) | **T** | SHORT | **OFF-TARGET** (lax bisim coarsens) | DEGRADES | reject-for-(iv) |
| **A4** idempotent boundary | OK | `PkRel_comp_le` ports verbatim under `⊓` | **T** (idempotent ⇒ `Pk` proof lifts) | SHORT | partial (boundary only) | VALID-NEG | **PASS** |
| **A5** impossibility | OK | fixed diamond witness; `ws4_quantitative_witness` for non-idem | **OPEN, leaning T** (dual of A1) | MEDIUM | ON (as §5 success) | — (is the neg) | **PASS** |

Paper-decisive fact: in Łₙ, `1 = ⊤`, so `a * ⊤ = a`; `tensor_section a w` requires `w ≤ a`. A composite edge weight through a middle `y` whose outgoing mass exceeds `a` cannot be split. Hence A1's *pointwise* split is fine but the *global* assembly fails exactly when the middle is non-normalized — this is not a proof gap, it is a structural obstruction, so A1's truth-value genuinely leans false and A5 leans true. **Selection: A4 (cheap boundary, certainly true) + A5 (the live impossibility). A1 held as the thing A5 refutes; A2 is the fallback if A5 turns out false.**

### Obligation B — canonicity of the weak law

| Cand | T1 | T2 | T3 | T4 | T5 | T6 | Verdict |
|---|---|---|---|---|---|---|---|
| **B1** `=` uniqueness | OK | `destEquiv : Equiv`, `alg` closed-form | **T** (`dest` injective ⇒ `pentagon` determines `alg`) | TRIVIAL | ON | VALID-NEG (→B4) | **PASS (subsumed by B2)** |
| **B2** `∃!` universal prop | OK | `alg_pentagon`, `alg_unit`, `destEquiv` all present | **T** | SHORT | ON | DEGRADES to `∃` (already have) | **PASS** |
| **B3** graded persistence | needs `wq_reduces_to_pk` (step 16) — **PHANTOM** | Bool-reduction unproved | OPEN | HARD | ON (the actual ratification) | DEGRADES | hold (gated on step 16) |
| **B4** family exists | OK | needs 2 distinct laws | **F** (B2 shows uniqueness ⇒ no family) | — | — | — | reject (B2 true ⇒ B4 false) |

Paper-decisive fact: `alg hreg t = (destEquiv κ).symm (pkJoin hreg (PkMap κ (νPk κ).str t))` and `destEquiv` is a Mathlib `Equiv` (from `wqLambek`/`Lambek`), hence injective. Any two laws sharing the `pentagon` field `str (alg t) = pkJoin (PkMap str t)` satisfy `destEquiv (alg t) = destEquiv (alg' t)`, so `alg = alg'`. B1/B2 are true by a one-line injectivity argument. **Selection: B2 (dominant — gives `∃!`, can only improve on existing `∃`). B3 is the downstream target but is genuinely blocked on `wq_reduces_to_pk`; it is scheduled after that, not now.**

### Obligation C — convergence (Lemma B: `SelectionLipschitz` with `(1−μ)·L_R μ < 1`)

| Cand | T1 | T2 | T3 | T4 | T5 | T6 | Verdict |
|---|---|---|---|---|---|---|---|
| **C1** replicator, μ-threshold | needs `replicatorField` (self-supply) | `ws7_mutation_contracts`, `ws7_attention_fixed_point` present | **OPEN** (Jacobian norm vs `1/(1−μ)` — real analysis) | HARD | ON | VALID-NEG (→C5) | at-risk |
| **C2** softmax, unconditional | needs `softmaxField` (self-supply) | same Banach scaffold | **OPEN, leaning T** (softmax Lip `= β·diam/2`, tunable) | MEDIUM | RELOCATES (model swap) | DEGRADES | **PASS** |
| **C3** interior margin | needs margin lemma | Banach scaffold | **OPEN** (ε–μ self-consistency) | HARD | ON (floor=margin story) | DEGRADES | hold |
| **C4** Cesàro/compactness | needs Markov–Kakutani import | `FlooredSimplex` compact-convex + `mutT` total (present) | **T** (Schauder/Brouwer on compact convex) | MEDIUM | weak (existence only) | — | **PASS** |
| **C5** impossibility card≥3 | needs RPS witness | fixed `Fin 3` field | **OPEN, leaning T for pure replicator** | MEDIUM | ON (as §5 success) | — | **PASS** |

Paper-verdict: C is the one obligation with **no upstream lever that forces the truth-value** — the contraction constant is an analytic fact about `replicatorField` that inspection cannot settle. Triage therefore *cannot* select a single positive; it selects the **guaranteed floor C4** (compact convex ⇒ a fixed point always exists, Schauder — true on paper) plus **C2** (the cleanest tunable positive) and records **C5** as the matched impossibility. **Selection: C4 (certain existence) as the deliverable floor + C2 (tunable unique attractor). C1/C5 forked later on one Jacobian-norm computation.**

### Obligation D — general branching (`GeneralBranching`)

| Cand | T1 | T2 | T3 | T4 | T5 | T6 | Verdict |
|---|---|---|---|---|---|---|---|
| **D1** `¬GeneralBranching` + subcarrier | OK | `ws2_nondegenerate` gives `∅`,`Ω`; `Ω={Ω}` deg 1 | **T for the ¬**; subcarrier part OPEN | ¬: TRIVIAL / sub: MEDIUM | documents unachievability | — | **PASS (¬ half)** |
| **D2** `alg`-relative branching | OK | `alg_pentagon` = `⋃ str x` present | **T** (union of ≥2 distinct-successor members) | SHORT | **ON (exactly what WS3 uses)** | DEGRADES | **PASS** |
| **D3** cardinal branching family | needs `corec` seeds (self-supply) | `Cofix.corec`, terminality present | **T** | MEDIUM | overshoots (feeds vii too) | VALID-NEG | hold |

Paper-decisive fact: `Ω = {Ω}` has out-degree exactly 1 and lies in `νPk` (constructed in ws1), and `∅` lies in `νPk` (image of `emptyCoalg`) with out-degree 0. Both refute `∀ x, out-degree ≥ 2`. So `GeneralBranching` is **false on paper**, and the honest content is `alg`-relative (D2): from `str (alg t) = ⋃_{x∈t} str x`, if `t` has two members with distinct successors then `alg t` has out-degree ≥ 2. **Selection: D2 (tight fit to WS3's `alg_nontrivial` need) + D1's negative half (proves the universal form is unachievable — required for honesty).**

### Obligation E — substantive standpoint (criterion vi)

| Cand | T1 | T2 | T3 | T4 | T5 | T6 | Verdict |
|---|---|---|---|---|---|---|---|
| **E1** positioned internal views | needs `Standpoint`/`view` (self-supply) | `endo_eq_id` only kills *global* endo-view | **OPEN, leaning T** (based spans escape `endo_eq_id`) | MEDIUM | ON (positive half of vi) | DEGRADES (span vacuity) | **PASS** |
| **E2** no terminal standpoint | OK | `ws6_no_maximal` `<κ`-bound argument ports | **T** (`#νPk ≥ κ` ⇒ no `<κ` state sees all) | SHORT | **ON (negative half of vi, the intended reading)** | VALID-NEG | **PASS** |
| **E3** common ambient category | needs pointed-set host (self-supply) | Mathlib `HasZeroObject` on `Type*_*` | **OPEN** (faithfulness vs coalgebra transport) | HARD | resolves WS1↔WS6 split | VALID-NEG (split forced) | hold |
| **E4** relocate to attention | OK | `ws5_carrier_incomplete` present | **T** | SHORT | **RELOCATES** (dynamical, not structural vi) | — | fallback |

Paper-decisive fact: `ws6_no_maximal` already proves no state has all others as successors, using `κ ≤ #(νPk κ).X` against the `< κ` support bound. E2 ("no state observes all states surjectively") is the *same* argument with `IsMaximal` replaced by surjective-observer — true on paper by porting `Cardinal.mk_le_of_injective` + support-bound. E1's positive half is not killed by `endo_eq_id` (which only forces the unique *global endo* view to be `id`; a based partial span is not an endo-map). **Selection: E2 (cheap, on-target negative half of vi) + E1 (the positive half — genuine positioned views). Together they give both faces of "every genuine view is internal, none is from nowhere."**

---

## Part 2 — Framing decision, collapsed

| Obligation | Selected candidate(s) | Framing (how the criterion is cashed out) | Terminal outcome guaranteed |
|---|---|---|---|
| **A** weak-pullback | **A5** primary, **A4** boundary, A2 fallback | Prove *no* weighted weak-pullback preservation for non-idempotent divisible `Q` (impossibility); prove it *holds* for idempotent `Q` (boundary) | §5 Impossibility (quantitative composition inherently non-strict) **or**, if A5 false, A2 partial |
| **B** canonicity | **B2** now; **B3** after step-16 | Weak law is the *unique* map satisfying EM unit+multiplication, via `dest`-injectivity | `∃!` (canonical law); degrades to existing `∃` |
| **C** convergence | **C4** floor + **C2** attractor; C1/C5 forked | Some invariant point always exists (compact convex); a unique attractor exists for tunable-temperature selection | Fixed point always (C4); unique attractor (C2) or impossibility (C5) |
| **D** branching | **D2** + **D1**-neg | Branching that `alg` *creates from ≥2-inputs* (what non-triviality needs); universal form proved false | `alg`-relative floor discharged; universal refuted |
| **E** standpoint (vi) | **E2** + **E1** | No `<κ`-state surjectively observes all (no view from nowhere) **and** distinct bases give distinct positioned partial views | Negative half (E2) certain; positive half (E1) if spans escape vacuity |

Selection principle applied uniformly: take the **triage-certain member** of each matched pair as the deliverable floor (A4, B2, C4, D2/D1-neg, E2), then pursue the **live unknown** whose resolution is a valid terminal outcome in either direction (A5, C2/C5, E1).

---

## Part 3 — Full mathematical designs

Notation and imports common to all: `κ : Cardinal.{u}`, `hreg : κ.IsRegular`, `hinf : ℵ₀ ≤ κ`. Carrier `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩` (ws1/ws2), weighted carrier `νWQ Q κ = ⟨Cofix (WQObj Q κ), Cofix.dest⟩` (ws4). `destEquiv κ : (νPk κ).X ≃ PkObj κ (νPk κ).X` (ws3). All designs preserve axiom discipline: only `propext`/`Classical.choice`/`Quot.sound`, verified by `#print axioms` on each top theorem.

---

### Design A — A5 (impossibility) with A4 (boundary)

**Goal A5.**
```lean
theorem ws4_no_quantitative_grading (n : ℕ) (hn : 2 ≤ n) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    ¬ WQPreservesWeakPullback (Luk n) κ
```

**Proof architecture.** Fixed finite diamond, then a marginal-inconsistency computation using non-idempotence.

Construction (all objects `< κ` since finite):
- `X := PUnit`, `Z := PUnit`, `Y := Bool` (two middles `y₀,y₁`).
- `R : X → Y → Prop := fun _ _ => True`; `S : Y → Z → Prop := fun _ _ => True`.
- Witness `w : WQObj (Luk n) κ {p : X×Z // (R∘S) p.1 p.2}` on the single pair `(⋆,⋆)`, weight `a := ⟨n-1, _⟩` (the non-idempotent element, `a⊗a ≠ a` by `ws4_quantitative_witness`).
- `s := WQMap Prod.fst w` (weight `a` on `⋆ : X`), `u := WQMap Prod.snd w` (weight `a` on `⋆ : Z`).

Lemmas to prove (all finite/`omega`-decidable on `Luk n`):
1. `lemma diamond_hyp : WQRel (relComp R S) s u` — from `w` directly (`⟨w, rfl, rfl⟩`).
2. `lemma middle_forces : ∀ t : WQObj (Luk n) κ Bool, (WQMap (fun _ => ⋆) t = s) → (t.1 y₀ ⊔ t.1 y₁ = a)` — the `Y→X` and `Y→Z` pushforwards are sups over the fibre, so both marginals equal `⨆_{y} t.1 y = a`.
3. `lemma split_needs_product : WQRel R s t → ∀ y, t.1 y ≤ a` and `WQRel S t u → ∀ y, t.1 y ≤ a`, and the *joint* reconstruction of the composite requires `t.1 y₀ ⊗ (\text{leg}) = a` for the fibre — but with two middles the composite weight on `(⋆,⋆)` reassembled through `t` is `⨆_y (\text{into } y) ⊗ (\text{out of } y)`, and each factor `≤ a` with `⊗` truncated forces `(\text{into})⊗(\text{out}) ≤ a⊗a < a` when both legs are `a`.
4. **Contradiction core** `lemma no_reassembly : ⨆_{y∈{y₀,y₁}} (t.1 y ⊗ t.1 y) < a` whenever `t.1 y₀ ⊔ t.1 y₁ = a` and `a` non-idempotent. On `Luk n`: `t.1 y ⊗ t.1 y = 2·(t.1 y) ⊖ n`; maximized at `t.1 y = a = n-1` giving `2(n-1)⊖n = n-2 < n-1 = a`. Pure `omega`.

Assembly: `WQPreservesWeakPullback` would yield such a `t` with both marginals `a`; lemma 4 shows the composite it induces is `< a`, but `diamond_hyp` requires it `= a`. Contradiction. `exact absurd … (lt_irrefl _)`.

**Definitions needed:** none beyond the diamond (all inline `Fin`/`Bool`). **No new class.**

**Upstream dependencies (imported, used as-is):**
- `WQObj`, `WQMap`, `WQMap_val`, `WQRel`, `WQPreservesWeakPullback` (ws4 §3–Layer C).
- `Luk n`, its `GoodQuantale`/`DivisibleQuantale` instances, `mul_val`, `ws4_quantitative_witness` (ws4 §2.3).
- `pushQ`/sup-projection simp lemmas (ws4 §3).

**Goal A4 (boundary).**
```lean
theorem wqA4_preserves_of_idempotent (Q : Type u) [DivisibleQuantale Q]
    (hidem : ∀ a : Q, a * a = a) (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    WQPreservesWeakPullback Q κ
```
**Architecture.** Port `PkRel_comp_le` (ws2) with weights. The pullback carrier `M = {(iR,iS) // mid iR = mid iS}` and its `< κ` bound (`Cardinal.mul_lt_of_lt hinf`) are reused unchanged. The weight on `M` is `wM(iR,iS) := wR(iR) ⊓ wS(iS)` (idempotent `⊗ = ⊓`). Marginal correctness: `⨆_{iS} (wR(iR) ⊓ wS(iS)) = wR(iR) ⊓ (⨆_{iS} wS(iS)) = wR(iR) ⊓ 1 = wR(iR)` using `tensor_sSup` + idempotence + the middle-fibre sup `= 1`. Two `Subtype.ext`/`le_antisymm` legs, structurally identical to `PkRel_comp_le`.

**Upstream:** `PkRel_comp_le` architecture (ws2, as template), `Cardinal.mul_lt_of_lt`, `tensor_sSup`, `WQMap`.

**Success condition.** A5: the `¬` is proved from the diamond. A4: both marginal legs equal. **Failure disposition.** If A5's lemma 4 fails (some non-idempotent `Q` *does* reassemble), then A5 is false, A1 is true, and effort transfers to completing A1's global assembly (the residuation `sSup {b | a*b ≤ w}` becomes the `wM`); A4 stands regardless as the idempotent boundary.

---

### Design B — B2 (canonicity as `∃!`)

**Goal.**
```lean
theorem ws3_weak_law_canonical (hreg : κ.IsRegular) :
    ∃! f : PkObj κ (νPk κ).X → (νPk κ).X,
      (∀ x, f (pkPure hreg.aleph0_le x) = x) ∧
      (∀ t, (νPk κ).str (f t) = pkJoin hreg (PkMap κ (νPk κ).str t))
```

**Proof architecture.** Two components.

*Existence.* `refine ⟨alg hreg, ⟨alg_unit hreg, alg_pentagon hreg⟩, ?_⟩` — the constructed `alg` from ws3 already inhabits both fields (`alg_unit`, `alg_pentagon` are imported theorems).

*Uniqueness.* Suppose `g` satisfies the multiplication field `∀ t, (νPk κ).str (g t) = pkJoin hreg (PkMap κ (νPk κ).str t)`. Then for all `t`:
```
(destEquiv κ) (g t) = (νPk κ).str (g t)            -- destEquiv = str on the carrier
                    = pkJoin hreg (PkMap κ (νPk κ).str t)   -- g's field
                    = (νPk κ).str (alg hreg t)              -- alg's field
                    = (destEquiv κ) (alg hreg t)
```
so `(destEquiv κ) (g t) = (destEquiv κ) (alg hreg t)`, and `destEquiv κ` injective (it is an `Equiv`) gives `g t = alg hreg t`; `funext`.

**Lemmas needed:**
1. `lemma destEquiv_eq_str : ∀ x, (destEquiv κ) x = (νPk κ).str x` — should be definitional or one `rfl`/`simp` from `destEquiv`'s definition `Equiv.ofBijective (νPk κ).str …`.
2. Reuse `alg_unit`, `alg_pentagon` verbatim.

**Definitions needed:** none. This is a pure consequence of existing ws3 material.

**Upstream dependencies:**
- `alg`, `alg_unit`, `alg_pentagon`, `destEquiv`, `pkJoin`, `pkPure`, `PkMap` (ws3).
- `Equiv.injective` (Mathlib).
- Lambek bijectivity underlying `destEquiv` (ws1/ws2 `νPk_terminal` → `wqLambek`-analogue).

**Success condition.** `ExistsUnique` discharged; downstream may cite "the canonical weak law." **Failure disposition.** Cannot fail below existing state: if uniqueness somehow breaks (it will not, `destEquiv` is a genuine `Equiv`), the existence half is still exactly the current ws3 `∃`. This is why B2 dominates B1.

*Scheduling note.* B3 (graded persistence, the actual WS4 ratification) has the identical uniqueness skeleton with `destEquiv` replaced by the `wqLambek`-derived `Equiv.ofBijective (νWQ Q κ).str`, **plus** a transport along `wq_reduces_to_pk`. The transport is blocked until step-16 is proved, so B3 is a two-line change to this design *after* that lands — recorded, not attempted now.

---

### Design C — C4 (compactness floor) + C2 (softmax attractor)

**Goal C4.**
```lean
theorem ws7_attention_has_fixed_point (S : Type u) [Fintype S] [Nonempty S]
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) [Nonempty (FlooredSimplex S μ unif)] :
    ∃ w : FlooredSimplex S μ unif,
      mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel w = w
```

**Proof architecture.** Brouwer/Schauder on the floored simplex.
1. `FlooredSimplex S μ unif` is a nonempty compact convex subset of the finite-dim `S → ℝ`: convex (intersection of half-spaces `μ·unif r ≤ w r` and hyperplane `∑ = 1`), closed (already an instance), bounded (subset of the standard simplex), hence compact in `ℝ^S`.
2. `mutT` is continuous (affine: `(1−μ)·sel.R + μ·unif`; need `sel.R` continuous — add as a field to `SelectionMap` or a hypothesis `hcont : Continuous sel.R`).
3. Apply Mathlib's Brouwer fixed-point (`isCompact_convex ... → Continuous f → MapsTo f s s → ∃ x ∈ s, f x = x`), i.e. `Convex.exists_fixedPoint` / the Schauder wrapper.

**Lemmas needed:**
1. `lemma flooredSimplex_convex : Convex ℝ {w | (∀ r, μ*unif r ≤ w r) ∧ ∑ r, w r = 1}` — convex-inter-halfspaces.
2. `lemma flooredSimplex_compact` — closed (have it) + bounded ⇒ compact (`Metric.isCompact_of_isClosed_isBounded` in finite dim).
3. `mutT` continuity from `SelectionMap` continuity field.
4. `MapsTo` = `mutationStep_maps_into` (imported).

**New definition:** extend `SelectionMap` with `cont : Continuous R` (or thread as hypothesis).

**Upstream:** `FlooredSimplex`, `mutT`, `mutationStep_maps_into` (ws7); Mathlib Brouwer (`exists_fixedPoint_of_isCompact_isConvex` family), finite-dim compactness.

**Success:** a fixed point always exists (no contraction premise). **Failure disposition:** essentially cannot fail; delivers existence, *not* uniqueness/attraction — so it is the floor, not the whole target.

**Goal C2 (unique attractor, tunable).**
```lean
def softmaxSel (S : Type u) [Fintype S] (β : ℝ) (f : S → ℝ) (unif : S → ℝ) : SelectionMap S unif
-- R w r := softmax(β·f)_r  (independent of w — a constant map — or barycentric mix)

theorem ws7_softmax_converges (S : Type u) [Fintype S] [Nonempty S]
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hu_nonneg : ∀ r, 0 ≤ unif r) (hu_sum : ∑ r, unif r = 1)
    (β : ℝ) (hβ : 0 < β) (f : S → ℝ)
    (hsmall : β * (Finset.sup' _ _ f - Finset.inf' _ _ f) / 2 < 1 / (1 - μ))
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! w : FlooredSimplex S μ unif,
      mutT μ (le_of_lt hμ0) hμ1 unif hu_nonneg hu_sum (softmaxSel S β f unif) w = w
```

**Architecture.** Instantiate the existing Banach scaffold. Provide a `SelectionLipschitz` for `softmaxSel` with `L_R μ := β·diam(f)/2` (softmax Jacobian operator-norm bound, a standard inequality: `‖∇ softmax_β‖_∞ ≤ β/2`). Then `(1−μ)·L_R μ < 1` is exactly `hsmall`. Feed `ws7_mutation_contracts` then `ws7_attention_fixed_point` (both imported) to get `∃!`.

**Lemmas needed:**
1. `lemma softmax_lipschitz : dist (softmax β f) (softmax β g) ≤ (β/2)·dist f g` — from `softmax` gradient bound; the hard analytic lemma, but *bounded and standard* (MEDIUM, not open).
2. `softmaxSel` well-formed `SelectionMap` (nonneg, sum-one: softmax is a probability vector) — direct.
3. `SelectionLipschitz` instance with `L_R := fun _ => β·diam/2`.

**Upstream:** `SelectionMap`, `SelectionLipschitz`, `mutationStep`, `ws7_mutation_contracts`, `ws7_attention_fixed_point`, `ws5_attention_converges` (ws7/ws5). Mathlib: `Real.exp`, softmax if present else define; finite `Finset.sup'`.

**Success:** unique attracting fixed point for small `β·diam`. **Failure disposition:** if `softmax_lipschitz` needs `β` so large that `hsmall` fails for the fitness of interest, degrades to C4's mere existence; if softmax is rejected as off-model, this is a declared substitution (RELOCATES). C1 vs C5 (the pure replicator) is settled by one computation: the replicator Jacobian norm at the interior rest point — if `< 1/(1−μ)` for admissible μ, C1 holds; if the RPS field gives purely imaginary eigenvalues forcing norm `≥ 1/(1−μ)`, C5 holds. That computation is the single open analytic node.

---

### Design D — D2 (`alg`-relative branching) + D1-neg (universal refuted)

**Goal D1-neg.**
```lean
theorem ws7_general_branching_false (hinf : ℵ₀ ≤ κ) : ¬ GeneralBranching κ
```
**Architecture.** Exhibit a state of out-degree `< 2`. The empty state: let `e := (νPk_terminal κ (emptyCoalg hinf)).1 PUnit.unit`, whose `str` is `∅` (as in `ws2_nondegenerate`'s proof), out-degree `0`. `GeneralBranching` claims `∃ y z ∈ ∅, y ≠ z` — refuted by `Set.not_mem_empty`. One `obtain … ; exact`.

**Upstream:** `emptyCoalg`, `νPk_terminal`, and the `str e = ∅` computation reused from `ws2_nondegenerate` (ws2).

**Goal D2.**
```lean
def IVBranching (hreg : κ.IsRegular) : Prop :=
  ∀ t : PkObj κ (νPk κ).X,
    (∃ x₁ ∈ t.1, ∃ x₂ ∈ t.1, (νPk κ).str x₁ ≠ (νPk κ).str x₂) →
      ∃ y z, y ∈ ((νPk κ).str (alg hreg t)).1 ∧ z ∈ ((νPk κ).str (alg hreg t)).1 ∧ y ≠ z

theorem ws7_iv_branching (hreg : κ.IsRegular) : IVBranching hreg
```
**Architecture.** From `alg_pentagon`: `(νPk κ).str (alg hreg t) = pkJoin hreg (PkMap κ (νPk κ).str t)`, whose members are `⋃_{x∈t} ((νPk κ).str x).1` (`mem_pkJoin`). Given `x₁,x₂ ∈ t` with `str x₁ ≠ str x₂`, the two successor sets differ, so their union contains two distinct points (pick `y ∈ str x₁ \ str x₂` or symmetric; if one is empty use a point of the other and a point forcing inequality). Careful case split on which successor set is larger; in the degenerate case where both are singletons `{y}≠{z}` the witnesses are `y,z` directly.

**Lemmas needed:**
1. `lemma distinct_succ_gives_two : str x₁ ≠ str x₂ → ∃ y z, y ∈ (⋃…) ∧ z ∈ (⋃…) ∧ y ≠ z` — set-theoretic, from `Set.ext_iff` failing.
2. `mem_pkJoin` (imported).

**Upstream:** `alg`, `alg_pentagon`, `pkJoin`, `mem_pkJoin`, `PkMap` (ws3); feeds `alg_nontrivial` (ws3) — this design *supplies the general branching hypothesis* `alg_nontrivial` was proved only for concrete witnesses under.

**Success:** `IVBranching` proved; WS3's non-triviality upgrades from concrete to `≥2-input-general`. `GeneralBranching` proved false, documenting the universal form is unachievable. **Failure disposition:** lemma 1 fails only if two states with distinct `str` can have identical successor-union with everything else — impossible since `str` distinct means the sets differ (bisim=identity, `ws2_bisim_eq`). So D2 is robust; if it somehow failed it would contradict `ws2_bisim_eq`, signaling upstream error, not a D2 defect.

---

### Design E — E2 (no view from nowhere) + E1 (positioned views)

**Goal E2.**
```lean
theorem ws6_no_global_observer (hcard : κ ≤ Cardinal.mk (νPk κ).X) (obs : (νPk κ).X) :
    ¬ Function.Surjective (fun x : (νPk κ).X =>
        (⟨x, sorry⟩ : ↥((νPk κ).str obs).1))   -- schematic; realized below
```
realized concretely as: no observer's successor set surjects onto the carrier.
```lean
theorem ws6_no_global_observer (hcard : κ ≤ Cardinal.mk (νPk κ).X) (obs : (νPk κ).X) :
    ¬ ∃ f : ↥((νPk κ).str obs).1 → (νPk κ).X, Function.Surjective f
```
**Architecture.** Identical shape to `ws6_no_maximal`. A surjection from `((νPk κ).str obs).1` (a `< κ` set, by `.2`) onto `(νPk κ).X` would give `#(νPk κ).X ≤ #((νPk κ).str obs).1 < κ`, contradicting `κ ≤ #(νPk κ).X`. Use `Cardinal.mk_le_of_surjective` then `lt_of_le_of_lt … ((νPk κ).str obs).2`.

**Lemmas needed:** none new — clone `ws6_no_maximal`'s three lines with `mk_le_of_surjective` in place of `mk_le_of_injective`.

**Upstream:** `νPk`, the `< κ` support bound `((νPk κ).str u).2` (ws1/ws2), `Cardinal.mk_le_of_surjective` (Mathlib). `hcard` is `ws6`'s standing `κ ≤ #(νPk κ).X`.

**Goal E1 (positive half).**
```lean
structure Standpoint (κ : Cardinal.{u}) where
  base : (νPk κ).X
  view : (νPk κ).X → Prop
  local' : ∀ y, view y ↔ y ∈ ((νPk κ).str base).1   -- sees exactly base's relations
  partial' : ¬ Function.Surjective (fun _ : {y // view y} => (rfl : True → True))  -- positioned: not all-seeing

theorem ws6_substantive_standpoints (hinf : ℵ₀ ≤ κ)
    (hcard : κ ≤ Cardinal.mk (νPk κ).X)
    (b₁ b₂ : (νPk κ).X) (hb : (νPk κ).str b₁ ≠ (νPk κ).str b₂) :
    ∃ sp₁ sp₂ : Standpoint κ, sp₁.base = b₁ ∧ sp₂.base = b₂ ∧ sp₁.view ≠ sp₂.view
```
**Architecture.** A standpoint's `view` is the membership predicate of its base's successor set (a local section indexed by `base`). Distinct bases with distinct `str` give distinct `view` predicates (`local'` ties `view` to `str base`, and `str b₁ ≠ str b₂` ⇒ the predicates differ on some `y`). `partial'` (non-surjective/positioned) follows from E2: no base's view sees all states. Existence of `b₁,b₂` with distinct `str` is `ws2_nondegenerate` (`∅` vs `Ω`).

**Lemmas needed:**
1. `lemma view_determines_str : (∀ y, view y ↔ y ∈ (str b).1) → view = (· ∈ (str b).1)` — funext/propext.
2. Distinct-`str` ⇒ distinct predicate — from set extensionality.
3. `partial'` via `ws6_no_global_observer` (E2).

**Upstream:** `ws2_nondegenerate`, `ws2_bisim_eq` (distinct str = distinct states), the `< κ` bound, and E2 above.

**Success:** E2 gives the "no view from nowhere" negative (the intended reading of vi); E1 gives genuinely distinct positioned partial views (the "every genuine view is internal, indexed by its holder" positive). Together they discharge vi with content, replacing the vacuity of `ws6_standpoint_vacuous`. **Failure disposition:** E2 cannot fail given `hcard` (which ws6 already assumes). E1 fails only if `view` is forced constant despite distinct bases — impossible once `view` is *defined* as the base's successor-membership and bases have distinct `str` (guaranteed by `ws2_nondegenerate` + `ws2_bisim_eq`). If one insists vi must be *structural at the terminal object with no base index*, both reduce to the honest `ws6_standpoint_vacuous` and the outcome is E4 (relocation to attention) — a declared substitution.

---

## Part 4 — Consolidated upstream-dependency matrix

| Design | Imports (theorems/defs used as-is) | New defs introduced | New nontrivial lemmas | Open node it depends on |
|---|---|---|---|---|
| A5 | `WQObj`,`WQMap`,`WQRel`,`WQPreservesWeakPullback`,`Luk`+instances,`ws4_quantitative_witness`,`mul_val` | diamond (inline) | `no_reassembly` (omega) | none |
| A4 | `PkRel_comp_le`(template),`Cardinal.mul_lt_of_lt`,`tensor_sSup`,`WQMap` | `wM := ⊓` | 2 marginal legs | none |
| B2 | `alg`,`alg_unit`,`alg_pentagon`,`destEquiv`,`pkJoin`,`pkPure`,`Equiv.injective` | none | `destEquiv_eq_str` | none |
| B3 (later) | B2 skeleton + `νWQ` Lambek `Equiv` | none | transport | **`wq_reduces_to_pk` (step 16)** |
| C4 | `FlooredSimplex`,`mutT`,`mutationStep_maps_into`, Mathlib Brouwer, fin-dim compactness | `SelectionMap.cont` | convex, compact | none |
| C2 | `SelectionMap`,`SelectionLipschitz`,`ws7_mutation_contracts`,`ws7_attention_fixed_point`,`ws5_attention_converges` | `softmaxSel` | `softmax_lipschitz` (bounded, standard) | none (C1/C5 fork = 1 Jacobian calc) |
| D1-neg | `emptyCoalg`,`νPk_terminal`,`str e = ∅` | none | none | none |
| D2 | `alg`,`alg_pentagon`,`pkJoin`,`mem_pkJoin`,`PkMap`,`ws2_bisim_eq` | `IVBranching` | `distinct_succ_gives_two` | none |
| E2 | `νPk`,`< κ` bound,`Cardinal.mk_le_of_surjective`,`ws6` `hcard` | none | (clone `ws6_no_maximal`) | none |
| E1 | `ws2_nondegenerate`,`ws2_bisim_eq`,`< κ` bound, E2 | `Standpoint` | `view_determines_str` | none |

Every selected design except B3 has **no dependency on an open node** — each rests only on already-proved upstream theorems plus self-contained new lemmas. B3 is deliberately deferred behind the single open step-16 reduction. The one genuinely open analytic node in the whole selection is the C1/C5 fork (replicator Jacobian norm), quarantined so that C4+C2 deliver a valid terminal outcome regardless of how it resolves.
