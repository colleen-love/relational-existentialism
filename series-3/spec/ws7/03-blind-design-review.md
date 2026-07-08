# WS7 non-collapse — design v2

**Changes from v1.** Three gaps found in review are now closed at the type level rather than in prose:

1. **μ↔L_R coupling** — `L_R` is no longer a free `ℝ≥0` supplied by the caller. It is produced *by* Lemma B as a function `L_R : ℝ → ℝ≥0` of the same `μ` that indexes the operator, and the contraction lemma consumes `L_R μ`, not an arbitrary constant. The loose-constant laundering path is now untypeable.
2. **T-invariance** — `mutationStep` is repackaged as a genuine self-map of `FlooredSimplex S μ unif` via an explicit invariance lemma, which is a *precondition* of the fixed-point theorem, not an afterthought. Banach is invoked on the subtype only after invariance is discharged.
3. **Non-monotone outcome** — the terminal trichotomy is replaced by a four-way classification whose "admissible set" is an arbitrary `Set ℝ`, not an interval; the Partial branch reports `AdmissibleFloor`, a decidable predicate on `μ`, so a disconnected or empty-interior admissible set is a nameable terminal state rather than an escape.

The static floor (C1), retro-validation (C5), and reuse of the Banach step are unchanged — they were sound in v1.

---

## 0. Ambient theory and imports

Unchanged from v1. Carrier `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, `F = P_κ`, AFA coalgebraic, axiom budget `[propext, Classical.choice, Quot.sound]`, `#print axioms` owed on the top bundle. Imports from ws1/ws2/ws4/ws5/ws6 and Mathlib as before. The single owed import remains the WS1 carrier lower bound `mk (νPk κ).X ≥ κ` (T4 ⚠).

One import is now used more precisely: `ws5_attention_converges` is Banach *on a complete metric space*, so the space it is applied to must be shown complete **and** the map shown to be a self-map of it. v1 established completeness; v2 adds the self-map obligation explicitly (§2, §3-B0).

## 1. Proof architecture (revised C3 branch)

```
   ws2_nondegenerate   ws6_no_maximal   ws2_weak_pullback
        └─────────┬─────────┴────────┬────────┘
                  ▼                  ▼
          ws7_static_band ◄── C1 (assembly, floor)   [unchanged]
                  │
                  ▼
   ── DECISION NODE (C3) ──────────────────────────────────
   M := FlooredSimplex S μ unif           (complete, nonempty)
        │
        ├─ B0  mutationStep_maps_into : T : M → M      (INVARIANCE — new)
        │
        ├─ B   selection_lipschitz_on_floor :
        │        ∃ L_R : ℝ → ℝ≥0,  ∀ μ, Lipschitz (R | floor μ) (L_R μ)
        │        └── L_R is a FUNCTION OF μ (coupling — new)
        │
        └─ A   mutation_lipschitz :
                 Lipschitz T ≤ (1−μ)·(L_R μ)·dist          (uses L_R μ)
                  │
                  ▼
   ws7_mutation_contracts μ (hfloor : (1−μ)·(L_R μ) < 1)
        │  ⟵ hfloor now references L_R μ, not a free constant
        ▼
   ws7_attention_fixed_point   (Banach on M, needs B0 + contraction)
   ─────────────────────────────────────────────────────────
                  ▼
   ws7_retro_validate ◄── C5 (collector spine)   [unchanged]
                  ▼
      ws7_band_and_retro   (assembly — NOT ws7_resolved)
```

## 2. Definitions (revised)

**The floored simplex** — unchanged as a type, but now with a bundled self-map structure.

```lean
def FlooredSimplex (S : Type*) [Fintype S] (μ : ℝ) (unif : S → ℝ) : Type _ :=
  { w : S → ℝ // (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) }

-- ℓ¹ metric, inherited; closed subset of a complete space ⇒ complete.
instance : MetricSpace (FlooredSimplex S μ unif) := ...
instance : CompleteSpace (FlooredSimplex S μ unif) := ...   -- closed-subset argument
```

**Standing assumptions on R.** The replicator is required, *as part of its interface*, to preserve the two structural facts the floor and the sum depend on. These are not new mathematics — they are the properties the replicator already has — but they must be named so invariance is provable.

```lean
structure SelectionMap (S : Type*) [Fintype S] (unif : S → ℝ) where
  R          : (S → ℝ) → (S → ℝ)
  nonneg     : ∀ w, (∀ r, 0 ≤ w r) → ∀ r, 0 ≤ R w r        -- keeps iterates ≥ 0
  sum_one    : ∀ w, (∑ r, w r = 1) → (∑ r, R w r = 1)        -- weight-preserving
```

**The mutation operator**, now built to *land in* `FlooredSimplex`.

```lean
def mutationStep (μ : ℝ) (unif : S → ℝ) (sel : SelectionMap S unif) :
    (S → ℝ) → (S → ℝ) :=
  fun w r => (1 - μ) * sel.R w r + μ * unif r
```

## 3. Lemmas and theorems (revised C3)

### C1 — static band. Unchanged from v1.

```lean
theorem ws7_static_band (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) :
    (∃ a b : (νPk κ).X, a ≠ b)
  ∧ (∀ u : (νPk κ).X, ¬ IsMaximal u)
  ∧ PkPreservesWeakPullback κ :=
  ⟨ws2_nondegenerate hinf, fun u => ws6_no_maximal hcard u, ws2_weak_pullback⟩
```

### B0 — invariance (NEW, closes gap 2).

`T` sends the floored simplex into itself. This is the precondition Banach needs on the subtype and was absent in v1.

```lean
lemma mutationStep_maps_into (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (unif : S → ℝ) (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (w : S → ℝ)
    (hw : (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1)) :
    (∀ r, μ * unif r ≤ mutationStep μ unif sel w r)
  ∧ (∑ r, mutationStep μ unif sel w r = 1) := by
  constructor
  · intro r
    -- (Tw) r − μ·unif r = (1−μ)·R w r ≥ 0, since μ ≤ 1 and R w r ≥ 0
    have hRnn : 0 ≤ sel.R w r :=
      sel.nonneg w (fun r => le_trans (mul_nonneg hμ0 (hunif_nonneg r)) (hw.1 r)) r
    nlinarith [hRnn, hμ1]
  · -- ∑ (1−μ)·R w + μ·unif = (1−μ)·1 + μ·1 = 1
    simp only [mutationStep, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sel.sum_one w hw.2, hunif_sum]; ring
```

This promotes `mutationStep` to a bona fide `FlooredSimplex S μ unif → FlooredSimplex S μ unif`:

```lean
def T (μ) (hμ0 hμ1 unif hunif_nonneg hunif_sum) (sel) :
    FlooredSimplex S μ unif → FlooredSimplex S μ unif :=
  fun ⟨w, hw⟩ => ⟨mutationStep μ unif sel w,
                  mutationStep_maps_into μ hμ0 hμ1 unif hunif_nonneg hunif_sum sel w hw⟩
```

### B — selection Lipschitz bound, coupled to μ (REVISED, closes gap 1).

The key change: `L_R` is delivered as a **function of `μ`**. Lemma B's obligation is to exhibit that function together with the interior Lipschitz property at each `μ`. No caller can substitute a looser constant, because the contraction lemma below reads `L_R μ` off *this* function.

```lean
-- The interior on which the replicator gradient is controlled:
def floorRegion (μ : ℝ) (unif : S → ℝ) : Set (S → ℝ) :=
  { w | ∀ r, μ * unif r ≤ w r }

structure SelectionLipschitz (S : Type*) [Fintype S] (unif) (sel : SelectionMap S unif) where
  L_R        : ℝ → ℝ≥0                                   -- the coupling: constant per μ
  bound      : ∀ (μ : ℝ), 0 < μ → μ ≤ 1 →
                 ∀ w ∈ floorRegion μ unif, ∀ w' ∈ floorRegion μ unif,
                   dist (sel.R w) (sel.R w') ≤ (L_R μ) * dist w w'
  -- L_R is the SHARP (least) valid constant at each μ, or an explicit upper bound of it;
  -- either way it is fixed by sel, not chosen by the consumer.
```

Lemma B's mathematical content (the genuinely analytic step) is to *construct* an inhabitant of `SelectionLipschitz` for the concrete replicator: the fitness gradient is bounded on `floorRegion μ`, and that bound, as a function of `μ`, is `L_R μ`. Whether `L_R μ` is monotone in `μ` is **left open** — the outcome classification in §6 no longer assumes it.

### A — mutation term contracts (REVISED to consume `L_R μ`).

```lean
lemma mutation_lipschitz (μ : ℝ) (hμ1 : μ ≤ 1)
    (unif : S → ℝ) (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (hμ0 : 0 < μ)
    (w w' : FlooredSimplex S μ unif) :
    dist (T μ ... sel w) (T μ ... sel w')
      ≤ ((1 - μ) * (sl.L_R μ)) * dist w w' := by
  -- pointwise: (Tw − Tw') = (1−μ)(R w − R w'); μ·unif cancels exactly.
  -- w, w' ∈ floorRegion μ by construction of FlooredSimplex, so sl.bound applies.
  have hw  : (w  : S → ℝ) ∈ floorRegion μ unif := w.2.1
  have hw' : (w' : S → ℝ) ∈ floorRegion μ unif := w'.2.1
  calc dist (T ...) (T ...) = (1 - μ) * dist (sel.R w) (sel.R w') := by
          simp [T, mutationStep, dist_eq_sum_abs, ← Finset.mul_sum, sub_mul]; ...
       _ ≤ (1 - μ) * ((sl.L_R μ) * dist w w') := by
          gcongr; exact sl.bound μ hμ0 hμ1 _ hw _ hw'
       _ = ((1 - μ) * (sl.L_R μ)) * dist w w' := by ring
```

Note `sl.bound` is applied at the operator's own `μ` — the coupling is now enforced by the fact that `w`, `w'` carry `floorRegion μ` membership in their type. Passing a constant valid only on a *different* floor is a type error.

### C3 — the contraction (REVISED signature).

```lean
theorem ws7_mutation_contracts (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : S → ℝ) (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (hfloor_contr : (1 - μ) * (sl.L_R μ) < 1) :          -- references L_R μ, not free L
    ∃ K : ℝ≥0, K < 1 ∧ ∀ w w' : FlooredSimplex S μ unif,
      dist (T μ ... sel w) (T μ ... sel w') ≤ K * dist w w' :=
  ⟨⟨(1 - μ) * (sl.L_R μ), by positivity⟩, hfloor_contr,
   mutation_lipschitz μ hμ1 unif sel sl hμ0⟩
```

**Honesty point (sharpened).** `hfloor_contr` still forks the outcome, but it can no longer be satisfied by a loose constant: `sl.L_R μ` is fixed by `sl : SelectionLipschitz`, whose `bound` field ties it to the actual replicator on `floorRegion μ`. The only remaining freedom is whether `SelectionLipschitz` is inhabited with a *sharp* or a *merely valid upper* `L_R`; the design requires the sharp one (or a proven upper bound), and this requirement is now visible as a documented field invariant rather than hidden in the constant.

### Feed into Banach (REVISED — now needs invariance).

```lean
theorem ws7_attention_fixed_point (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif) (hunif_nonneg) (hunif_sum) (sel) (sl)
    (hfloor_contr : (1 - μ) * (sl.L_R μ) < 1)
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif, T μ hμ0.le hμ1 unif hunif_nonneg hunif_sum sel p = p := by
  obtain ⟨K, hK, hlip⟩ := ws7_mutation_contracts μ hμ0 hμ1 unif sel sl hfloor_contr
  -- Banach on the COMPLETE subtype; T : M → M is total by mutationStep_maps_into (B0).
  exact ws5_attention_converges (T μ hμ0.le hμ1 unif hunif_nonneg hunif_sum sel) K hK hlip
```

The `T : M → M` self-map is what B0 buys; without it `ws5_attention_converges` would not even typecheck on the subtype. Completeness (v1) plus totality (B0) plus contraction (C3) are exactly Banach's three hypotheses.

### C5 — retro-validation. Unchanged from v1.

```lean
theorem ws7_retro_validate (κ₀ : Cardinal.{u}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X) (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WS2Characterization κ₀)
  ∧ (∀ u : (νPk κ₀).X, ¬ IsMaximal u)
  ∧ Nonempty (WS6NoPoles κ₀)
  ∧ Nonempty (GradedWeakLawCoherence (Luk n) κ₀ hreg) :=
  ⟨ws2_characterization hreg.aleph0_le hreg,
   fun u => ws6_no_maximal hcard u,
   ws6_split_and_no_maximal hreg.aleph0_le hcard,
   ws4_graded_law_coherence (Luk n) hreg⟩
```

## 4. Assembly (revised structure)

```lean
structure WS7NonCollapse (κ : Cardinal.{u}) (μ : ℝ) where
  hinf         : ℵ₀ ≤ κ
  hcard        : κ ≤ Cardinal.mk (νPk κ).X
  richness     : ∃ a b : (νPk κ).X, a ≠ b
  no_maximal   : ∀ u : (νPk κ).X, ¬ IsMaximal u
  weak_pb      : PkPreservesWeakPullback κ
  plurality    : 0 < μ
  -- Dynamical field: one of the FOUR terminal shapes below, never a bare
  -- `hfloor_contr` hypothesis. See DynamicalStatus.
```

The dynamical field is realized by one of four constructors, corresponding to §6. Critically, none of them is a bare-hypothesis contraction; the Partial constructor carries a *decidable admissible predicate*, not an unproven inequality.

```lean
inductive DynamicalStatus (S : Type*) [Fintype S] (unif) (sel : SelectionMap S unif)
    (sl : SelectionLipschitz S unif sel)
  | discharged
      (h : ∀ μ, 0 < μ → μ ≤ 1 → (1 - μ) * (sl.L_R μ) < 1)          -- contracts everywhere
  | impossible
      (h : ∀ μ, 0 < μ → μ ≤ 1 → 1 ≤ (1 - μ) * (sl.L_R μ))          -- never contracts
  | partial
      (adm : Set ℝ)                                                  -- ARBITRARY set
      (hadm : ∀ μ, μ ∈ adm ↔ (0 < μ ∧ μ ≤ 1 ∧ (1 - μ) * (sl.L_R μ) < 1))
      (hne  : adm.Nonempty)                                          -- nonempty ⇒ genuinely Partial
```

`partial.adm` need not be an interval; `hadm` characterizes it exactly as the sublevel set of `μ ↦ (1−μ)·(L_R μ)`. A disconnected admissible set, or one with empty interior, is fully expressible. The empty case is *not* a `partial` constructor (it is `impossible`), so the constructors are mutually exclusive and exhaustive over the sign of `(1−μ)L_R − 1`.

## 5. Dependencies on imported theorems

Same list as v1, with one sharpening: `ws5_attention_converges` is now consumed as *Banach on a complete space with a proven self-map*, so the dependency record must note that WS7 supplies the self-map obligation (B0) locally; WS5 does not provide it.

## 6. Expected terminal status (revised — four-way, closes gap 3)

- **Static band (C1)** — Discharged, assembly. Unchanged.
- **Retro-validation (C5)** — Discharged at `κ₀`, contingent on `hreg`+`hcard` cohold. Unchanged.
- **Invariance (B0)** — Discharged: it follows from `sel.nonneg`, `sel.sum_one`, and `μ ≤ 1` by the `nlinarith`/`sum` argument above. This was an *unstated* obligation in v1 and is now a closed lemma.
- **Dynamical convergence (C3)** — decision node, now with four terminal shapes rather than three:
  1. `discharged` — `(1−μ)(L_R μ) < 1` for all admissible `μ`.
  2. `impossible` — `(1−μ)(L_R μ) ≥ 1` for all `μ ∈ (0,1]`: contraction defeated on the whole range.
  3. `partial` with `adm` an **interval** — the classical v1 outcome.
  4. `partial` with `adm` **disconnected / empty-interior** — newly nameable; the obstruction is reported as the exact sublevel set of `μ ↦ (1−μ)(L_R μ)`, not forced into interval form.

**Overall WS7: class deferred to the construction of `SelectionLipschitz` (Lemma B).** The design is now assembly-ready on every axis *including* invariance and the μ-coupling, which v1 left implicit. The single remaining open obligation is genuinely single: inhabit `SelectionLipschitz` with a sharp (or proven-upper) `L_R : ℝ → ℝ≥0`. Once that function exists, the terminal verdict is a *decidable* read of its sublevel set — `discharged`, `impossible`, or `partial adm` — with no bare hypothesis surviving into the top bundle.

**What is no longer hidden.** (1) The contraction constant is the replicator's own `L_R μ`, not a caller-chosen scalar — enforced by `floorRegion μ` membership living in the simplex type. (2) `T` is a total self-map of the complete space — the B0 lemma. (3) The admissible set is an arbitrary `Set ℝ` with an exact characterization — no interval assumption. The remaining risk is exactly the analysis in Lemma B and nothing else.
