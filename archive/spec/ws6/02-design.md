# WS6 — Triage and Design

## Part 1 — Paper-decidable triage

Each candidate scored on predicates decidable by inspection, using only the WS1/WS2/WS3 artifacts already verified and Mathlib's known contents. The decisive axes: is it dischargeable now without unproved category-theoretic input, does it stay on the built carrier (preserving the upstream identity theory), and does it capture a genuine facet of the obligation rather than a vacuous or relabeled surrogate.

**Triage predicates (Yes / No / Partial, each decidable without running Lean):**

- **T1 — Dischargeable on paper?** Completable with Mathlib + WS1/WS2 lemmas, no unproved analytic or category-construction input.
- **T2 — Carrier-preserving?** Stays on `νPk κ = Cofix (PkObj κ)`; does not re-base the carrier into a new category and force re-proof of the identity theory.
- **T3 — On-target?** Captures a genuine facet of no-poles/no-outside, not a vacuous or merely relative surrogate.
- **T4 — Upstream-grounded?** Consumes a load-bearing WS1/WS2 fact (`str`/Lambek/`bisim_eq`/`nondegenerate`), rather than floating free.
- **T5 — `(F,κ)`-robust?** Survives WS4's `W_Q` enrichment and WS7's bound choice (no functor-specific branching or carrier-cardinality premise).
- **T6 — Non-degeneracy safe?** Does not risk collapsing the ≥2 non-bisimilar states (`ws2_nondegenerate`).
- **T7 — Cost in Lean.** Low / Med / High.
- **Outcome class** (per §5 vocabulary): Discharged / Impossibility-proved / Partial / (off-target).

| | T1 dischargeable | T2 carrier-preserving | T3 on-target | T4 grounded | T5 (F,κ)-robust | T6 non-degen safe | T7 cost | Class |
|---|---|---|---|---|---|---|---|---|
| **F1** absolute zero in `Set_*` | **No** (needs full re-proof in new cat.) | **No** | Yes | Partial | No | **No** (poles-merge risk) | High | at-risk Partial/Failed |
| **F2** no-maximal, diagonal | **Yes** | **Yes** | Yes (one facet) | **Yes** (support bound) | **Yes** (if diagonal route) | Yes | Low | **Discharged** |
| **F3** empty standpoint | Partial (position-free premise ad hoc) | Yes | Yes (one facet) | Yes (`bisim_eq`) | Yes | Yes | Med | Partial |
| **F4** cohabitation / split | Partial→**Yes on neg. disjunct** | Yes (neg. disjunct) | **Yes (the hazard itself)** | **Yes** (`nondegenerate`) | Yes | Yes (it *proves* the tension) | Med | **Impossibility-proved** (neg. disjunct) |
| **F5** relative zero in slice | Yes | Yes | **Partial** (misses "everything" pole) | Yes | Yes | Yes | Low | Partial-by-construction |

**Reading the table.** F1 fails T1/T2/T6 simultaneously: it is the one framing that both requires re-basing the carrier and directly courts the poles-merge collapse — highest cost, lowest certainty, dropped as a primary (it survives only as the *failed attempt* that motivates F4's negative disjunct). F5 passes everything cheap but fails T3 to Partial: a relative/fibrewise zero does not capture the "everything" pole, so it is a declared substitution, not a discharge. F3 is on-target and carrier-preserving but its load-bearing "position-free" side condition is not paper-decidable as non-ad-hoc — it stays Partial pending a clean formalization. F2 and F4 pass every decidable predicate at Low/Med cost.

**The pole-coincidence facet is the charter's actual WS6 hazard**, and the triage says something sharp about it: F1 (the only *positive* route to absolute coincidence) fails T1/T2/T6, while F4's *negative* disjunct passes T1/T4/T6 and yields Impossibility-proved. So the triage does not merely rank framings — it predicts the *direction* of the result: absolute pole coincidence resolves as a **provable split**, not a construction.

**Collapsed decision.** A composite dictated by the triage, not chosen for elegance: **F2 (no-maximal) Discharged + F4-negative (pole split) Impossibility-proved as the primary deliverable**, with F3 and F5 routed as secondary/Partial contributions to the standpoint and relative-bottom facets. F4's negative disjunct is selected as the **lead candidate for full design** because it resolves the highest-risk facet and its class (Impossibility-proved) is a §5 success; F2 rides alongside as a cheap independent Discharge feeding F4's wall premise.

**Selected object for full design: F4's negative disjunct — the pole-coincidence split, `ws6_poles_split` — with F2's `ws6_no_maximal` as its consumed sub-lemma.**

---

## Part 2 — Full mathematical design

### 2.0 Ambient theory and imports

Carrier: `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra from WS1/WS2. `F = P_κ`. No monad `T`, no distributive law `λ` — poles-coincidence is a question about the *ambient category's distinguished objects*, not about composition. AFA modeled coalgebraically. Axiom budget `[propext, Classical.choice, Quot.sound]`.

The result is a **negative** theorem: any category with a zero object into which the carrier embeds faithfully (as a functor sending the ≥2 non-bisimilar states to distinct objects and coalgebra structure to genuine maps) must, via the zero object's null morphisms, identify those states — contradicting non-degeneracy. Hence no such faithful embedding exists: the pole-coincidence object and the groundless carrier cannot cohabit one category under a faithful, structure-preserving embedding. This is exactly the charter's "declare the split," proved.

Imported, cited as established and axiom-free:

- from **ws1**: `PkObj`, `PkMap`, `Coalg`, `IsTerminalCoalg`, `hom_unique`, `endo_eq_id`, `lambek`, `emptyCoalg`, `mk_empty_lt`, `mk_singleton_lt`, `omegaCoalg`. The load-bearing facts are `lambek` (surjectivity of `str`, for the no-maximal wall) and `hom_unique` (for the standpoint constancy).
- from **ws2**: `νPk`, `νPk_terminal`, `ws2_bisim_eq`, `ws2_nondegenerate`, `diagBisim`. **`ws2_nondegenerate` is the single load-bearing fact for the split** (it supplies the ≥2 distinct states the zero object would have to merge); `ws2_bisim_eq` grounds F3.
- from **Mathlib**: `CategoryTheory.Limits.HasZeroObject`, `CategoryTheory.Limits.HasZeroMorphisms`, `IsZero`, `Function.cantor_surjective` (for F2's diagonal), `CategoryTheory.Functor`, `Faithful`.

### 2.1 Proof architecture (dependency graph)

```
   ws2_nondegenerate (ws2)        HasZeroObject / zero morphisms (Mathlib)
        │ (≥2 states a≠b)                    │ (null map factors through 0)
        └──────────────┬──────────────────────┘
                       ▼
             ws6_poles_split   ← F4-neg, IMPOSSIBILITY-PROVED (the hazard)
             (no faithful structure-preserving embedding into a
              zero-object category)
                       ▲
                       │ consumes as wall premise
   lambek (ws1) ── ws6_no_maximal ← F2, DISCHARGED, (F,κ)-robust
   (str surjective    (diagonal, no carrier-cardinality fact)
    onto <κ subsets)
                       │
   ws2_bisim_eq (ws2) ─┴── ws6_empty_standpoint ← F3, PARTIAL
                            (bisim-invariant position-free ⇒ constant)
                       │
   emptyCoalg (ws1) ── ws6_relative_bottom ← F5, PARTIAL-by-construction
                            (empty-observation state as relative zero)
                       ▼
             WS6NoPoles   ← assembly, named ws6_split_and_no_maximal
                            (NOT ws6_resolved — coincidence is the split,
                             not a constructed zero object)
```

Two spines close fully: the F2 no-maximal wall (Discharged) and the F4 split (Impossibility-proved). F3 and F5 attach as Partial fields. The assembly is named to prevent the Impossibility from being read as a positive construction of the coincidence.

### 2.2 Definitions needed

**Faithful structure-preserving embedding (F4).** The object at stake is a functor from the carrier's coalgebra data into a candidate ambient category `C`, required to be injective on the ≥2 distinguished states and to send the coalgebra's distinctness to non-equal morphisms. The minimal faithful witness needed for the contradiction is: an injection on objects together with the demand that distinct states receive morphisms not both factoring through zero.

```lean
/-- A carrier embedding into an ambient category `C`: injective on states, with
    the empty-observation and self-singleton states landing on objects joined by
    a morphism. The zero object, if present, would force that morphism null. -/
structure CarrierEmbedding (κ : Cardinal.{u}) (C : Type v) [Category.{w} C] where
  obj    : (νPk κ).X → C
  inj    : Function.Injective obj
  hom    : ∀ x y, obj x ⟶ obj y                     -- carrier is "connected" as a graph
  hom_ne : ∀ {x y}, x ≠ y → ¬ IsIso (hom x y) ∨ obj x ≠ obj y  -- distinctness reflected
```

(The precise `hom_ne` shape is tuned in proof; the essential content is that a zero object collapses `hom x y` to the null morphism, which combined with `inj` and a zero-object retraction forces `x = y`.)

**No-maximal predicate (F2).** A maximal/universal state observes the entire carrier.

```lean
def IsMaximal (u : (νPk κ).X) : Prop := ∀ v : (νPk κ).X, v ∈ ((νPk κ).str u).1
```

**Position-free bisimulation-invariant view (F3).** A global predicate invariant under bisimilarity (hence, by `ws2_bisim_eq`, under equality — so the content is carried by a second invariance: under the corec-image reparametrization, modeled here as invariance under *all* endo-coalgebra maps, which by `endo_eq_id` is again just identity — this is exactly why the standpoint is empty).

```lean
def PositionFree (obs : (νPk κ).X → Prop) : Prop :=
  ∀ (h : (νPk κ).X → (νPk κ).X),
    (∀ x, (νPk κ).str (h x) = PkMap κ h ((νPk κ).str x)) → ∀ x, obs (h x) = obs x
```

**Relative bottom (F5).** The empty-observation state.

```lean
noncomputable def bottomState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (emptyCoalg hinf)).choose PUnit.unit
```

### 2.3 Lemmas and theorems

**F2 — no maximal element (Discharged, `(F,κ)`-robust).**

```lean
theorem ws6_no_maximal (u : (νPk κ).X) : ¬ IsMaximal u
```

Proof strategy (diagonal, cardinality-free). Suppose `u` is maximal: `str u` contains every state. Then the assignment `v ↦ (predicate "v ∉ str⁻¹-diagonal")` builds a state not in `str u` by the Lawvere/Cantor route — concretely, use that `str u` is a `< κ`-bounded set while a maximal `u` would make `str u = univ`, and `mk (νPk κ).X`-into-`str u` cannot be surjective onto its own power via `Function.cantor_surjective`. The robust form: maximality gives a surjection-like map from the support onto predicates on the support (each state, being in `str u`, is itself a `< κ`-set of states), and the diagonal on *that* — same shape as `ws5_carrier_incomplete` — contradicts. Consumes only the support bound, no lower bound on `mk (νPk κ).X`. **Success:** proved via the diagonal route with no carrier-cardinality premise. **Failure (c):** if the diagonal cannot be closed without a cardinality lower bound, the result degrades to "no-maximal by fiat of `κ`" — still true, but not robust; documented as the fallback.

**F4 — the pole-coincidence split (Impossibility-proved, the primary).**

```lean
theorem ws6_poles_split (hinf : ℵ₀ ≤ κ) (C : Type v) [Category.{w} C]
    [Limits.HasZeroObject C] [Limits.HasZeroMorphisms C]
    (E : CarrierEmbedding κ C) : False
```

Proof strategy. Obtain `a ≠ b` from `ws2_nondegenerate`. In `C` with a zero object `0`, every hom-set has a null morphism factoring through `0`, and the zero object is both initial and terminal — so for the embedded objects there is a unique map to and from `0`, making all parallel structure collapse to the null. Show `E.hom a b` and its would-be inverse are forced through `0`, so `E.obj a ≅ E.obj b`; combined with `E.inj` and `E.hom_ne (h : a ≠ b)`, derive the contradiction `a = b`. The mathematical content: a zero object supplies a *global* null through which distinctions dissolve, which is incompatible with the carrier's non-degeneracy being *reflected* faithfully. **Success:** `False` derived for arbitrary such `C` — i.e. no zero-object category faithfully hosts the carrier's distinctions; the coincidence and the carrier provably split. This is the charter's "declare the split," as a theorem. **Failure mode:** if `CarrierEmbedding` is too weak (e.g. `hom_ne` vacuous) the theorem is vacuously true and says nothing — the design must certify `CarrierEmbedding` is *inhabited for `Set`* (where there is no zero object, so vacuously) yet *non-vacuous in intent*, i.e. the structure genuinely reflects `a ≠ b`. Guarded by an inhabitation lemma below.

**Non-vacuity guard for F4.**

```lean
theorem ws6_embedding_nonvacuous (hinf : ℵ₀ ≤ κ) :
    ∃ (C : Type u) (_ : Category.{u} C), Nonempty (CarrierEmbedding κ C)
```

Proof: instantiate `C = Type u` (or the carrier's own discrete/graph category) where the embedding is the identity-on-states with `hom x y` the canonical carrier relation; `hom_ne` holds because `ws2_nondegenerate` gives genuinely distinct objects. This certifies `ws6_poles_split` is not vacuously true — the embedding exists in a *non*-zero-object category, and the theorem says precisely that adding a zero object breaks it.

**F3 — empty standpoint (Partial).**

```lean
theorem ws6_empty_standpoint (obs : (νPk κ).X → Prop) (h : PositionFree obs) :
    (∀ u, obs u) ∨ (∀ u, ¬ obs u)
```

Proof strategy. `PositionFree` quantifies over all endo-coalgebra maps `h`; by `endo_eq_id` (ws1) every such `h` is `id`, so `PositionFree` as stated reduces to a tautology — **this is the precise obstruction**: the position-free constraint collapses to vacuity under terminality, so the theorem as written is not informative. The honest Partial: state it, prove the vacuous reduction, and flag that a *content-bearing* external standpoint needs a genuinely larger class of "views" (e.g. spans out of non-terminal coalgebras) not available on the terminal carrier alone. **Failure (vacuity):** documented, not hidden — F3 is Partial by construction, obstruction = "no non-trivial position-free map exists to quantify over, by `endo_eq_id`."

**F5 — relative bottom (Partial-by-construction).**

```lean
theorem ws6_relative_bottom (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (bottomState hinf)).1 = (∅ : Set (νPk κ).X) ∧
    Nonempty (Bisim (νPk κ) (fun a b => a = b))
```

Proof: the empty-observation state has empty structure (from `emptyCoalg`'s naturality, as in ws2/ws3), and `diagBisim` certifies the carrier's identity theory is untouched. This gives the bottom pole relatively; the "everything" pole is explicitly *not* delivered (that is the split of F4). **Partial:** captures only the bottom, obstruction routed to F4.

### 2.4 The assembly

```lean
structure WS6NoPoles (κ : Cardinal.{u}) where
  no_maximal    : ∀ u : (νPk κ).X, ¬ IsMaximal u
  poles_split   : ∀ (C : Type u) [Category.{u} C] [Limits.HasZeroObject C]
                    [Limits.HasZeroMorphisms C], CarrierEmbedding κ C → False
  standpoint    : ∀ obs, PositionFree obs → (∀ u, obs u) ∨ (∀ u, ¬ obs u)
  rel_bottom    : ((νPk κ).str (bottomState hinf_field)).1 = ∅   -- hinf carried

theorem ws6_split_and_no_maximal (hinf : ℵ₀ ≤ κ) : Nonempty (WS6NoPoles κ)
```

Named `ws6_split_and_no_maximal`, **not** `ws6_resolved` and **not** `ws6_zero_object`: the pole-coincidence facet is delivered as an *impossibility* (the split), so a name implying a constructed zero object would launder the negative result into a false positive. This transplants the WS4/WS5 naming discipline.

### 2.5 Dependencies on imported theorems (explicit)

- `ws2_nondegenerate` → sole load-bearing input to `ws6_poles_split` (the ≥2 states the zero object must merge). If WS7 later changes `(F,κ)` and non-degeneracy needs re-proof, `ws6_poles_split` must be re-ratified — this is the WS6→WS7 coupling, flagged.
- `lambek` (ws1) → the no-maximal wall's surjectivity-of-`str` handle (F2 route i fallback); the preferred diagonal route (F2 route ii) needs only the `PkObj` support bound, making F2 `(F,κ)`-robust and *independent* of the `(F,κ)` ratification.
- `endo_eq_id` (ws1) → the F3 vacuity reduction; this is what makes F3 Partial rather than Discharged.
- `emptyCoalg`, `diagBisim` (ws1/ws2) → F5 relative bottom.
- Mathlib `HasZeroObject`/`HasZeroMorphisms`/`IsZero` → the abstract zero-object machinery for F4; no custom category is constructed, so no re-proof of the identity theory is incurred (this is why F4 passes T2 where F1 failed).

**Expected terminal status:** WS6 **Partial (split)** — `ws6_no_maximal` Discharged and `(F,κ)`-robust; `ws6_poles_split` Impossibility-proved (the pole-coincidence hazard resolves as a provable split, confirming the charter's suspicion that coincidence-object and carrier are different objects in different categories); `ws6_empty_standpoint` and `ws6_relative_bottom` Partial with obstructions made precise (F3's vacuity via `endo_eq_id`, F5's missing "everything" pole routed to the F4 split). The single most informative finding: the zero-object coincidence the charter hoped might realize "atom = everything" *cannot* cohabit the groundless carrier faithfully — a sharp negative that is a §5 success, not a shortfall.
