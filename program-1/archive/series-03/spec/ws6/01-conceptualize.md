# WS6 — No Poles, No Outside: Obligation Analysis

## What is at stake

The mathematical object is the terminal `P_κ`-coalgebra `νP_κ = Cofix (PkObj κ)` already built in WS1/WS2, together with a category-theoretic question about *where* it lives and what limits/colimits and distinguished objects that ambient category has. Three distinct properties are bundled under the WS6 obligation:

1. **Pole coincidence** — the "atom" (initial-like, contentless bottom) and the "everything" (terminal-like, all-encompassing top) must coincide as a *single* object that is both, and this object must be non-trivial (the coincidence must be structurally forced, not an artifact of a degenerate category where everything is isomorphic).

2. **No maximal element** — there is no `νP_κ`-object whose observation contains all objects; equivalently no fixed point of the "contains everything" operator, equivalently `str` is not surjective *onto the full powerset* (only onto `< κ`-bounded subsets). Under bounding this holds by the cardinal cutoff, and the non-triviality question is whether that cutoff is a genuine wall or a vacuous one.

3. **Empty external standpoint** — any object positioned "outside" every object (a global section over the whole diagram of local views) is contentless; equivalently, the terminal object of the relevant category, if it is a valid observer, observes nothing.

## Why it is non-trivial

The tension is categorical incompatibility. Pole coincidence is a **zero object** phenomenon — it lives naturally in additive/pointed categories (`Ab`, `Mod`, pointed sets), where initial and terminal objects merge. But `νP_κ` is a coalgebra over `Set` (via `Cofix`/QPF), and `Set` has `∅ ≠ {∗}` — no zero object. So the object realizing pole coincidence and the object realizing groundlessness are *prima facie in different categories*, and "one object does both" is an unproven bridging claim. Worse, forcing a zero object risks collapsing the distinguishing power that keeps `νP_κ` non-degenerate (WS7's floor). The core difficulty: **exhibit a single ambient category containing a groundless carrier, a zero object, and a Cantor-style no-maximal wall, without the zero object trivializing the carrier's bisimulation structure.**

The failure surface is therefore not one thing. It could fail by (a) *no coincidence* — every candidate ambient category keeps poles distinct; (b) *trivial coincidence* — the only category with the coincidence collapses the carrier to a point (the zero object *is* the whole carrier); (c) *no wall* — bounding does not actually forbid a maximal object, or forbids it only vacuously; (d) *category split* — the coincidence object and the carrier provably cannot cohabit.

---

## Candidate framings

### Framing 1 — Zero object in a pointed observation category

Reconstruct the carrier over pointed sets `Set_*` (or partial maps `Par`) rather than `Set`, so that `∅`-with-basepoint and `{∗}` merge. Prove the bounded observation functor lifts to this category, has a terminal coalgebra, and that this coalgebra has a zero object as a sub-object realizing pole coincidence.

**Ambient theory.** AFA modeled coalgebraically; `F = P_κ^*` the pointed/partial κ-bounded powerset endofunctor on `Set_*`; no monad/law needed. Carrier `νP_κ^* = Cofix` over the pointed QPF.

**Lean signature.**
```lean
theorem ws6_zero_object_pointed (hinf : ℵ₀ ≤ κ) :
    ∃ (C : Type u) [inst : Category.{u} C] (F : C ⥤ C) (U : Coalg_ptd F),
      IsTerminalCoalg U ∧ Nonempty (Limits.HasZeroObject C) ∧
      ∃ z : U.X, IsInitial z ∧ IsTerminal z
```

**Proof strategy.** Show `P_κ` on `Set_*` is still a QPF (the basepoint adds one shape); run the `Cofix` route from WS1 to get terminality; identify the zero object as the state with empty observation carrying the basepoint, and prove it is simultaneously initial and terminal in the coalgebra category via the unique-morphism argument (`endo_eq_id` analog).

**Success condition.** A genuine zero object exists *and* `νP_κ^*` remains non-degenerate (≥2 non-bisimilar states survive alongside the zero object).

**Failure mode.** Trivial coincidence (b): if the pointed lift forces every coalgebra morphism through the basepoint, the carrier collapses and `ws2_nondegenerate` fails to transport — the zero object eats the carrier.

**Trade-off.** Cleanest realization of the coincidence, but the highest risk of leaving `Set` in a way that breaks WS1/WS2's inherited theorems; requires re-proving the entire identity theory in the new category.

---

### Framing 2 — No-maximal-element as non-surjectivity (Cantor wall, internal)

Cash out "no everything" as: there is no state whose observation is the entire carrier's image. Prove `str` cannot hit a "universal" element. This is provable *inside* the existing `Set`-based carrier with no category change.

**Ambient theory.** Exactly WS1/WS2: `F = P_κ`, `νPk = Cofix (PkObj κ)`, `str = Cofix.dest`. No `T`, no `λ`.

**Lean signature.**
```lean
theorem ws6_no_maximal (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ u : (νPk κ).X, ∀ v : (νPk κ).X, v ∈ ((νPk κ).str u).1
```

**Proof strategy.** Two routes. (i) *Cardinality wall:* a `u` observing all of `(νPk κ).X` would need `mk (νPk κ).X < κ` (support bound) while `mk (νPk κ).X ≥ 2^{<κ}`-ish from the branching — contradiction; but this needs a lower bound on the carrier and is *not* `(F,κ)`-robust. (ii) *Diagonal (preferred):* a universal `u` gives a surjection-like structure onto `Set`-valued self-relations; run a Lawvere/Cantor diagonal analogous to WS5's `ws5_carrier_incomplete` to derive contradiction, consuming only the support bound.

**Success condition.** The theorem holds via route (ii) with no carrier-cardinality lower bound — making it functor-robust like WS5's incompleteness.

**Failure mode.** No wall (c): if route (ii) cannot avoid a cardinality premise, "no everything" holds only *by fiat* of `κ` (route i), which the charter explicitly flags as a concession rather than a discharge.

**Trade-off.** Fully on the existing carrier, no category risk, likely cheap. But addresses only one of the three bundled properties; says nothing about pole coincidence.

---

### Framing 3 — Empty terminal standpoint (no substantive global observer)

Cash out "no view from nowhere" as: the terminal object in the coalgebra category, viewed as an observer, has trivial observation — any global section over the diagram of all local views is contentless.

**Ambient theory.** Coalgebra category `Coalg P_κ`; the "external observer" is a candidate terminal *object of observers*, distinct from the terminal *coalgebra*. Model a view as a coalgebra morphism into a one-point observation.

**Lean signature.**
```lean
theorem ws6_empty_standpoint (hinf : ℵ₀ ≤ κ) :
    ∀ (obs : (νPk κ).X → Prop),
      (∀ u v, (∃ R, Bisim (νPk κ) R ∧ R u v) → (obs u ↔ obs v)) →
      (∀ u, obs u) ∨ (∀ u, ¬ obs u)
```

**Proof strategy.** A "view from nowhere" is a bisimulation-invariant global predicate. By `ws2_bisim_eq`, bisimulation is identity, so invariance is vacuous *unless* one also demands the predicate factor through some external quotient. Show the only bisimulation-invariant predicates that are also "position-free" (invariant under the carrier's automorphisms / the corec-image structure) are the two constant predicates — i.e. a truly external standpoint distinguishes nothing.

**Success condition.** Only constant global predicates survive the position-free constraint; every content-bearing view is internal (indexed by some `u`).

**Failure mode.** Non-existence / vacuity: the position-free constraint is either unstatable in a functor-robust way or so strong every predicate is constant trivially, making the theorem uninformative rather than a genuine "emptiness of the outside."

**Trade-off.** Directly targets the third bundled property and stays on the carrier, but the "position-free" side condition is the crux and risks being ad hoc; the cleanest formalization of it is itself open.

---

### Framing 4 — Bridging theorem: coincidence and carrier cohabit (or provably split)

Meet the charter's actual hazard head-on: state, as a single theorem, that there exists one ambient category hosting *all three* (groundless carrier, zero object, no-maximal wall) — or prove the negation (they cannot cohabit), which is an Impossibility-proved success.

**Ambient theory.** A category `C` to be exhibited (candidate: `Coalg P_κ` internal to a pointed topos, or the category of `P_κ`-coalgebras in `Set_*`); `F` its observation functor; no `T`/`λ`.

**Lean signature.**
```lean
theorem ws6_cohabitation (hinf : ℵ₀ ≤ κ) :
    (∃ (C : Type (u+1)) [Category.{u} C] (ι : Coalg κ → C),
        (∃ z : C, IsInitial z ∧ IsTerminal z) ∧
        Function.Injective ι ∧
        (∀ U, IsTerminalCoalg U → ¬ ∃ m : C, IsTerminal m ∧ ι U.X_obj = m))
    ∨
    (∀ (C : Type (u+1)) [Category.{u} C] (ι : Coalg κ → C),
        (∃ z : C, IsInitial z ∧ IsTerminal z) →
        ¬ Function.Injective ι)   -- the provable split
```

**Proof strategy.** Attempt the positive disjunct by construction (Framing 1's category, checking the wall via Framing 2 transported). If the transport fails, pivot to the negative disjunct: show any category with a zero object into which the carrier embeds faithfully must identify the ≥2 non-bisimilar states (zero object forces a null morphism factoring distinctions away), contradicting `ws2_nondegenerate` — a clean Impossibility.

**Success condition.** *Either* disjunct proved. This is the framing that matches the charter's demand that WS6 "exhibit the single category or declare the split."

**Failure mode.** Neither disjunct closes — the cohabitation question is left genuinely open (Partial), which is the honest fallback but not a discharge.

**Trade-off.** The only framing that resolves the charter's central WS6 hazard rather than a sub-piece. Also the most expensive and the one whose *type* is hardest to state faithfully (category-in-a-universe bookkeeping). High payoff, high cost.

---

### Framing 5 — Poles as a fibrewise zero in a slice, carrier untouched

Avoid re-basing the whole carrier: realize pole coincidence in a *slice* or *comma* construction over `νP_κ` where a fibrewise pointed structure gives a relative zero object, leaving the base carrier in `Set` and its theorems intact.

**Ambient theory.** Base `Set` with `νPk κ`; work in `Coalg P_κ / νPk` or a pointed-object category `Pointed(Coalg P_κ)`; `F` unchanged on the base.

**Lean signature.**
```lean
theorem ws6_relative_zero (hinf : ℵ₀ ≤ κ) :
    ∃ (star : (νPk κ).X),
      ((νPk κ).str star).1 = (∅ : Set (νPk κ).X) ∧
      (∀ u, ∃! f : PUnit → (νPk κ).X, f PUnit.unit = star) ∧
      Nonempty (Bisim (νPk κ) (fun a b => a = b))  -- carrier still non-degenerate
```

**Proof strategy.** Take the empty-observation state `e0` (WS2/WS3's `emptyCoalg` image) as the relative bottom; show it is initial-like among "atoms" (unique incoming from the trivial coalgebra) and terminal-like as a receiver of the empty view; certify via `diagBisim` that the carrier's identity theory is untouched. Coincidence is *relative* (a pointed-object zero), not absolute.

**Success condition.** The empty-observation state serves both roles fibrewise, and `ws2_nondegenerate` transports unchanged.

**Failure mode.** Weak coincidence: a *relative* zero is arguably not the charter's "atom = everything" — the "everything" role is not genuinely captured, so this may be a declared substitution rather than a discharge (honest Partial).

**Trade-off.** Lowest risk to upstream theorems, cheapest after Framing 2. But it likely under-delivers on the "everything" pole — closest to a Partial-by-construction.

---

## Cross-cutting trade-offs

The framings partition by *how much they leave `Set`*: Framings 2, 3, 5 stay on the built carrier (cheap, robust, but each covers only one facet); Framings 1, 4 change category (expensive, risk breaking WS1/WS2, but only these can realize genuine absolute pole coincidence). Framing 4 is the only one that resolves the charter's actual WS6 hazard, and it has an Impossibility-proved fallback (the negative disjunct) that counts as success, so it dominates on informativeness. A realistic composite: **Framing 2 (no-maximal, functor-robust) Discharged + Framing 3 or 5 (standpoint/relative-zero) + Framing 4's negative disjunct as the pole-coincidence resolution**, with the absolute-zero-in-`Set_*` route (Framing 1) as the high-risk attempt whose failure feeds Framing 4's Impossibility. The single most likely genuine result: no-maximal and empty-standpoint discharge on the existing carrier, while absolute pole coincidence resolves as *provable split* (Impossibility) — matching the charter's suspicion that the coincidence object and the groundless carrier are different objects in different categories.

The load-bearing risk across all framings is that the zero object and non-degeneracy are in direct tension: any construction strong enough to merge the poles is at risk of merging the ≥2 states the carrier needs, so every candidate must carry `ws2_nondegenerate` transport as an explicit proof obligation, not an afterthought.
