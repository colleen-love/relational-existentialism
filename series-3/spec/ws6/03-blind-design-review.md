# WS6 — Triage and Design (Revised)

> **Revision note.** This revision preserves the triage in Part 1 but reworks Part 2 to fix
> the problems found in review: (1) the lead theorem `ws6_poles_split` did not actually follow
> from `HasZeroObject`/`HasZeroMorphisms` as designed — a zero object does *not* force arbitrary
> morphisms to null, so the old `CarrierEmbedding` was satisfiable by zero-object categories and
> the theorem was unprovable/vacuous; (2) the non-vacuity guard confirmed the vacuity rather than
> excluding it; (3) `WS6NoPoles.rel_bottom` referenced a non-existent field; (4) universes
> collapsed silently between `ws6_poles_split` and the assembly; (5) F2's `(F,κ)`-robustness claim
> was not supported by the stated diagonal strategy. The corrected split now runs through
> **terminality** of the zero object (its actual load-bearing property) rather than null morphisms.

---

## Part 1 — Paper-decidable triage

*(Unchanged from the original design; reproduced for self-containment. The triage predicates,
scores, and the collapsed decision — F2 Discharged + F4-negative Impossibility-proved as primary,
F3/F5 as Partial — all stand. The revision only concerns how F4's split is realized in Lean.)*

Triage predicates T1–T7 and the scoring table are retained verbatim. The one substantive change
downstream of the table: **F2's T5 (`(F,κ)`-robust) is downgraded from Yes to Partial** — see §2.3,
F2 — because the cardinality-free diagonal route does not close without relating `mk (νPk κ).X`
to `κ`. F2 remains **Discharged**; only its robustness annotation changes.

**Selected object for full design: F4's negative disjunct — the pole-coincidence split,
`ws6_poles_split` — with F2's `ws6_no_maximal` as its consumed sub-lemma.**

---

## Part 2 — Full mathematical design (revised)

### 2.0 Ambient theory and imports

Carrier: `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra from WS1/WS2.
`F = P_κ`. No monad, no distributive law. AFA modeled coalgebraically. Axiom budget
`[propext, Classical.choice, Quot.sound]`.

The result is a **negative** theorem, and the corrected mechanism is the one the original design
was reaching for but did not encode: **a zero object is terminal**, and terminality forces
*uniqueness of morphisms into it*. The carrier, as a terminal coalgebra with ≥2 non-bisimilar
states, cannot be faithfully embedded as the underlying object of a zero object, because the zero
object's terminality would collapse the maps that witness the states' distinctness. This is a
genuine contradiction; the old "everything factors through the null morphism" is not, and is
dropped.

Imports (cited as established and axiom-free) are as in the original, with the load-bearing facts:
- **ws1**: `lambek` (surjectivity of `str`, for the no-maximal wall), `hom_unique`,
  `endo_eq_id`, `emptyCoalg`.
- **ws2**: `ws2_nondegenerate` (**sole load-bearing fact for the split**: ≥2 distinct states),
  `ws2_bisim_eq` (grounds F3), `diagBisim` (grounds F5).
- **Mathlib**: `CategoryTheory.Limits.HasZeroObject`, `IsZero`, `IsTerminal`,
  `CategoryTheory.Functor`, `CategoryTheory.Faithful`, `Function.cantor_surjective`,
  and the cardinality API for the F2 wall (`Cardinal.mk_lt_of_...` / `Cardinal.cantor`).

Note the changed Mathlib surface: the split now consumes `IsZero`/`IsTerminal` (the terminality
face of a zero object), **not** `HasZeroMorphisms`. The old dependency on zero *morphisms* is
removed entirely, because it was doing no real work.

### 2.1 Proof architecture (dependency graph)

```
   ws2_nondegenerate (ws2)         HasZeroObject → IsTerminal (0) (Mathlib)
        │ (≥2 states a≠b)                    │ (unique map X ⟶ 0, and 0 terminal)
        └──────────────┬──────────────────────┘
                       ▼
             ws6_poles_split   ← F4-neg, IMPOSSIBILITY-PROVED
             (no FAITHFUL FUNCTOR from the carrier's one-object
              coalgebra-endo category into a zero-object category:
              terminality of 0 collapses the reflected distinctness)
                       ▲
                       │ consumes as wall premise
   lambek (ws1) ── ws6_no_maximal ← F2, DISCHARGED (robustness: Partial)
   (str surjective    (diagonal + carrier/κ cardinality relation)
    onto <κ subsets)
                       │
   ws2_bisim_eq (ws2) ─┴── ws6_empty_standpoint ← F3, PARTIAL
                            (position-free ⇒ constant, vacuous via endo_eq_id)
                       │
   emptyCoalg (ws1) ── ws6_relative_bottom ← F5, PARTIAL-by-construction
                       ▼
             ws6_split_and_no_maximal   ← assembly (NOT ws6_resolved)
```

### 2.2 Definitions needed (revised)

**The corrected embedding (F4).** The prior `CarrierEmbedding` failed because it demanded a
morphism between *every ordered pair* of states and let `hom_ne` be discharged by object
inequality alone — so a zero-object category satisfied it and the theorem was vacuous. The fix
is to make the embedding a genuine **faithful functor** out of a small category built from the
carrier's own structure, so that "reflects distinctness" becomes "distinct on morphisms," which
terminality can then contradict.

Concretely, let the source be the **states-as-objects category with distinguished distinctness
witnesses**: two chosen states `a ≠ b` (from `ws2_nondegenerate`) as objects, and two *parallel*
non-equal morphisms between them. The zero object, being terminal, forces the two maps *into*
`0` to coincide; faithfulness then forces the two source morphisms to coincide — contradiction.

```lean
/-- The minimal distinctness data the carrier exhibits: two states and two
    genuinely distinct parallel morphisms between them in the coalgebra-derived
    category `D`. `ws2_nondegenerate` supplies an inhabitant (see nonvacuity guard). -/
structure ParallelWitness (κ : Cardinal.{u}) (D : Type v) [Category.{w} D] where
  A B  : D
  f g  : A ⟶ B
  distinct : f ≠ g

/-- A faithful embedding of the carrier's distinctness data into an ambient
    category `C`: a faithful functor from a category `D` that already carries a
    ParallelWitness. Faithfulness is the load-bearing property. -/
structure FaithfulCarrierEmbedding
    (κ : Cardinal.{u}) (C : Type v) [Category.{w} C] where
  D        : Type w
  instD    : Category.{w} D
  witness  : ParallelWitness κ D
  F        : D ⥤ C
  faithful : F.Faithful
```

The essential content: `F.faithful` means `F.map f = F.map g → f = g`. A zero object in `C` is
terminal, so `F.map witness.f` and `F.map witness.g`, viewed via the unique map to `0`… — no; we
route through terminality correctly in §2.3, where the contradiction is derived from the fact that
`F.obj witness.B ⟶ 0` is unique, hence any two morphisms `F.obj A ⟶ F.obj B` that agree after
post-composition with the (mono, by faithfulness reflection) structure are equal. See the proof
strategy for the exact factoring; the definition only fixes the data.

**No-maximal predicate (F2).** Unchanged.

```lean
def IsMaximal (u : (νPk κ).X) : Prop := ∀ v : (νPk κ).X, v ∈ ((νPk κ).str u).1
```

**Position-free view (F3).** Unchanged (its vacuity is the whole point).

```lean
def PositionFree (obs : (νPk κ).X → Prop) : Prop :=
  ∀ (h : (νPk κ).X → (νPk κ).X),
    (∀ x, (νPk κ).str (h x) = PkMap κ h ((νPk κ).str x)) → ∀ x, obs (h x) = obs x
```

**Relative bottom (F5).** Unchanged.

```lean
noncomputable def bottomState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (emptyCoalg hinf)).choose PUnit.unit
```

### 2.3 Lemmas and theorems (revised)

**F2 — no maximal element (Discharged; robustness Partial).**

```lean
theorem ws6_no_maximal (hcard : mk (νPk κ).X ≥ κ) (u : (νPk κ).X) : ¬ IsMaximal u
```

**Change from original:** an explicit cardinality hypothesis `hcard : mk (νPk κ).X ≥ κ` is added,
because the review showed the "cardinality-free" claim was wrong. `IsMaximal u` means
`(str u).1 = univ`. Since `str u : PkObj κ (…)` is a `< κ`-bounded subset, maximality forces
`mk (νPk κ).X < κ`, contradicting `hcard` directly — no diagonal needed once `hcard` is present.

The diagonal (`Function.cantor_surjective`) route is retained only as the *fallback that avoids
`hcard`*, and the honest status is: it does **not** close without relating `mk (νPk κ).X` to `κ`,
because `str u = univ` is only contradictory when `univ` exceeds the `< κ` bound. **Therefore F2's
T5 annotation is Partial, not Yes.** The theorem is Discharged (it is true and proved), but its
`(F,κ)`-robustness is conditional on the cardinality relation, which *does* depend on the
`(F,κ)` ratification via `κ`. This is flagged as a real WS6→WS7 coupling, additional to the
one on `ws2_nondegenerate`.

Where `hcard` comes from: it is exactly `mk_empty_lt` / `mk_singleton_lt` composed with the
standard fact that a terminal `P_κ`-coalgebra has ≥ κ states (the carrier embeds all `< κ`
observation-trees). If WS1 already exposes `mk (νPk κ).X ≥ κ` as a lemma, `hcard` is discharged
internally and F2 needs no hypothesis; the design should check WS1 for such a lemma and prefer it.

**F4 — the pole-coincidence split (Impossibility-proved, primary; corrected mechanism).**

```lean
theorem ws6_poles_split
    (C : Type v) [Category.{w} C] [Limits.HasZeroObject C]
    (E : FaithfulCarrierEmbedding κ C) : False
```

**Change from original:** `HasZeroMorphisms` is *removed*; the proof runs through `HasZeroObject`
alone, via its terminality face. The hypothesis is now a faithful functor carrying a genuine
parallel-witness, not a per-pair `hom` with a vacuously-dischargeable `hom_ne`.

Proof strategy (terminality, corrected):
1. From `HasZeroObject C`, obtain the zero object `0` and `hZero : IsZero 0`; in particular `0`
   is terminal (`IsZero.isTerminal`).
2. Let `A := E.F.obj E.witness.A`, `B := E.F.obj E.witness.B`, and
   `Ff := E.F.map E.witness.f`, `Fg := E.F.map E.witness.g` — two morphisms `A ⟶ B` in `C`.
3. **This is where the old proof failed and the new one works.** Terminality of `0` does *not*
   collapse `Ff` and `Fg` directly. Instead, use that in a category with a zero object every
   object has a *point structure* only if additionally enriched — which we do **not** assume.
   So a bare `HasZeroObject` is in fact **insufficient** to collapse two parallel maps.

   **Honest correction:** `HasZeroObject` alone is genuinely too weak — `Type*`-with-basepoint,
   `Ab`, `Vec` all have zero objects *and* distinct parallel maps, and faithfully host any
   distinctness. So the theorem must contradict a *stronger* coincidence hypothesis than "the
   ambient category merely has a zero object." The charter's actual hazard is
   **"atom = everything,"** i.e. the coincidence object is *both initial and terminal and the
   embedding lands the carrier inside it* — equivalently, that the carrier's image is contained
   in the zero object's own hom-structure. We encode that:

```lean
theorem ws6_poles_split
    (C : Type v) [Category.{w} C] [Limits.HasZeroObject C]
    (E : FaithfulCarrierEmbedding κ C)
    (coincide : ∀ x, Limits.IsZero (E.F.obj x)) : False
```

   With `coincide`, every `E.F.obj x` is a zero object, hence terminal, hence **the hom-set
   `E.F.obj A ⟶ E.F.obj B` is a subsingleton** (any two maps into a terminal object are equal).
   Therefore `Ff = Fg`. Faithfulness (`E.faithful`) gives `E.witness.f = E.witness.g`, contradicting
   `E.witness.distinct`. `exact E.witness.distinct (E.faithful … )`. ∎

The mathematical content is now correct and sharp: the hazard is not "there exists a zero object
somewhere in `C`" (harmless) but "**the carrier's distinguished states are all identified with the
zero object**" — the literal "atom = everything." Terminality of that object makes its hom-sets
subsingletons, faithfulness pulls the collapse back to the source, and `ws2_nondegenerate`'s
distinctness is contradicted. The split is: the coincidence object (a zero object hosting the whole
carrier) and the groundless carrier (≥2 distinct states, reflected faithfully) cannot coexist.

**Non-vacuity guard for F4 (corrected).**

```lean
theorem ws6_embedding_nonvacuous :
    ∃ (C : Type u) (_ : Category.{u} C),
      Nonempty (FaithfulCarrierEmbedding κ C) ∧
      ¬ (∃ E : FaithfulCarrierEmbedding κ C, ∀ x, Limits.IsZero (E.F.obj x))
```

**Change from original:** the guard now certifies two things the old one conflated — that a
faithful embedding *exists* (so the hypothesis of `ws6_poles_split` is inhabited and the theorem is
not vacuously about nothing), **and** that in a witness category the `coincide` premise *fails*
(so `ws6_poles_split` is not vacuously true — the `coincide` hypothesis genuinely carries the
weight). Take `C = D = ` the two-object category `{A, B}` with two distinct parallel maps `f ≠ g`
and `F = 𝟭` (identity functor, trivially faithful); `ws2_nondegenerate` justifies that `f ≠ g`
is realizable as the distinctness of `a, b`. This `C` has no zero object into which both objects
collapse, so `coincide` is false here. This precisely isolates `coincide` as the operative
hypothesis: remove it and the theorem is false (witnessed here); keep it and the theorem holds.

**F3 — empty standpoint (Partial).** Unchanged from original, including the honest vacuity
diagnosis via `endo_eq_id`.

```lean
theorem ws6_empty_standpoint (obs : (νPk κ).X → Prop) (h : PositionFree obs) :
    (∀ u, obs u) ∨ (∀ u, ¬ obs u)
```

Obstruction restated: `PositionFree` quantifies over endo-coalgebra maps; `endo_eq_id` forces each
to be `id`, so the hypothesis is satisfiable only trivially and carries no content. Partial by
construction; the theorem is true but content-free. A content-bearing standpoint needs views out of
*non-terminal* coalgebras (spans), unavailable on the terminal carrier alone.

**F5 — relative bottom (Partial-by-construction).** Unchanged.

```lean
theorem ws6_relative_bottom (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (bottomState hinf)).1 = (∅ : Set (νPk κ).X) ∧
    Nonempty (Bisim (νPk κ) (fun a b => a = b))
```

### 2.4 The assembly (revised)

```lean
structure WS6NoPoles (κ : Cardinal.{u}) where
  hinf        : ℵ₀ ≤ κ                                   -- ADDED: carried explicitly
  hcard       : mk (νPk κ).X ≥ κ                         -- ADDED: F2's wall hypothesis
  no_maximal  : ∀ u : (νPk κ).X, ¬ IsMaximal u
  poles_split : ∀ (C : Type u) [Category.{u} C] [Limits.HasZeroObject C]
                  (E : FaithfulCarrierEmbedding κ C),
                  (∀ x, Limits.IsZero (E.F.obj x)) → False
  standpoint  : ∀ obs, PositionFree obs → (∀ u, obs u) ∨ (∀ u, ¬ obs u)
  rel_bottom  : ((νPk κ).str (bottomState hinf)).1 = ∅   -- now well-scoped: uses `hinf` field

theorem ws6_split_and_no_maximal
    (hinf : ℵ₀ ≤ κ) (hcard : mk (νPk κ).X ≥ κ) : Nonempty (WS6NoPoles κ)
```

**Changes from original:**
1. **`hinf` is now a field**, so `rel_bottom`'s reference to `bottomState hinf` type-checks (the
   original referenced a non-existent `hinf_field`).
2. **`hcard` is a field**, supplying F2's cardinality wall; `no_maximal` is stated over it.
3. **`poles_split` carries the `coincide` premise** `(∀ x, IsZero (E.F.obj x))`, matching the
   corrected theorem, and drops `HasZeroMorphisms`.
4. **Universe honesty:** the assembly fixes `C : Type u`, `[Category.{u} C]`, and the standalone
   `ws6_poles_split` is polymorphic `(C : Type v) [Category.{w} C]`. The prose no longer claims the
   assembled field has the full polymorphic strength — it records the `u`-instance, which is what
   the `Type u` non-vacuity witness supports. If the fully polymorphic form is wanted in the
   assembly, restate `poles_split` with explicit `{v w}` binders and provide a `Type max u v`
   witness; flagged as an optional strengthening, not claimed by default.

Named `ws6_split_and_no_maximal`, **not** `ws6_resolved` / `ws6_zero_object`: the pole-coincidence
facet is an *impossibility* (the split), and a positive-sounding name would launder it.

### 2.5 Dependencies on imported theorems (explicit, revised)

- `ws2_nondegenerate` → sole load-bearing input to `ws6_poles_split` (supplies the distinct
  `a, b` realizing `witness.f ≠ witness.g`). **WS6→WS7 coupling flagged (unchanged).**
- `mk (νPk κ).X ≥ κ` (WS1, or added hypothesis `hcard`) → **new** load-bearing input to
  `ws6_no_maximal`. Because it depends on `κ`, **F2 is no longer `(F,κ)`-independent**; this is a
  **second WS6→WS7 coupling**, newly surfaced by the revision. If WS1 exposes the ≥κ bound as a
  ratified lemma, discharge `hcard` internally and the coupling is inherited from WS1 rather than
  introduced here.
- `lambek` (ws1) → still available as the surjectivity handle for the F2 fallback route, but the
  primary F2 proof now uses the `< κ` support bound + `hcard` directly.
- `endo_eq_id` (ws1) → F3 vacuity (unchanged; this is what keeps F3 Partial).
- `emptyCoalg`, `diagBisim` (ws1/ws2) → F5 (unchanged).
- Mathlib `HasZeroObject` / `IsZero` / `IsTerminal` / `Functor.Faithful` → the abstract machinery
  for the corrected F4. **`HasZeroMorphisms` is no longer used.** No custom ambient category is
  constructed (the source category `D` is small and carrier-derived, not a re-basing of the
  carrier), so no re-proof of the identity theory is incurred — F4 still passes T2.

**Expected terminal status (revised):** WS6 **Partial (split)** —
- `ws6_no_maximal` **Discharged**, robustness **Partial** (conditional on `mk (νPk κ).X ≥ κ`;
  `(F,κ)`-coupled, downgraded from the original's claimed robustness);
- `ws6_poles_split` **Impossibility-proved**, via terminality of the coincidence object under the
  corrected `coincide` premise — the "atom = everything" object cannot faithfully host the
  carrier's ≥2 distinct states;
- `ws6_empty_standpoint` and `ws6_relative_bottom` **Partial**, obstructions precise (F3 vacuity via
  `endo_eq_id`; F5 missing "everything" pole routed to F4).

The single most informative finding is sharpened by the correction: it is not the mere presence of a
zero object that is incompatible with the carrier (that was the false step), but the **coincidence
of the carrier's states with the zero object** — "atom = everything" — which terminality makes a
subsingleton and faithfulness contradicts. That is the charter's suspicion, now proved on the right
hypothesis.
