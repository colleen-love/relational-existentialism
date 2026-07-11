# WS6 — Triage and Design (Charter-aligned revision)

> **Revision lineage.** Revision 1 fixed the mathematics of the lead theorem (the zero object's
> load-bearing property is *terminality*, not null morphisms). This revision (Revision 2) binds the
> design to the charter and removes three drifts found on that binding:
>
> - **D1 — Criterion (vi) was under-delivered.** The charter's core WS6 criterion is (vi) "no
>   substantive terminal standpoint" (§3.7 third bullet, "no view from nowhere"; §4 WS6 line
>   names "the emptiness of the external standpoint" as a required deliverable). The prior design
>   routed (vi) entirely to F3, which is vacuous via `endo_eq_id`, and buried that as a minor
>   "Partial." (vi) is now surfaced as an **explicit, routed criterion-(vi) shortfall** in §2.6,
>   in the charter's §8.2 discipline, and F3's status line states the binding consequence.
> - **D2 — The split theorem's prose overclaimed its scope.** With the `coincide` premise,
>   `ws6_poles_split` proves that the *total* identification of the carrier with a zero object is
>   impossible (the charter's "atom = everything" trivialization hazard, §8 standing risk). It does
>   **not** prove the broader "different objects in different categories" bridging claim the §8.1
>   note emphasizes. The prose is re-scoped to what is proved, and the stronger cross-category
>   statement is stated as a **named open obligation** (`ws6_no_faithful_zero_host`) rather than
>   silently claimed.
> - **D3 — A coupling was mislabeled as newly-discovered.** F2's `κ`-bound dependency is not a new
>   hazard; it is the discharge of WS1's already-declared hand-off (§3.7 [REV-A], §8.1 WS1:
>   "no maximal everything holds by fiat of `κ`… lands as an obligation on WS6/WS7"). It is
>   relabeled accordingly in §2.5.
>
> All mathematical content from Revision 1 is retained. Changes are confined to scope statements,
> status lines, the new §2.6, and the dependency prose.

---

## Part 0 — Charter binding (new; makes the obligation explicit)

**Workstream:** WS6 — No poles, no outside (charter §4, deliverable 5 of §6).

**Commitments served:** Commitment 3 (§2.3 / §3.7, its three faces) and Commitment 6's
standpoint-collapse clause (§3.8, second bullet — already cross-referenced to §3.7 by the charter).

**Success criteria bound:** primary **(vi)** "no substantive terminal standpoint"; contributory to
the "no maximal everything" obligation the §8.1 audit hands WS6 from WS1. WS6 does **not** own
(i)–(iii) (carrier identity theory — WS1/WS2/WS4) or (iv)/(v)/(vii); it consumes (vii)'s
≥2-state non-degeneracy as an *input* (`ws2_nondegenerate`), it does not establish it.

**The three faces of §3.7, and where each lands in this design:**

| §3.7 face | Criterion | Design object | Terminal status |
|---|---|---|---|
| Bullet 1 — coinciding poles (zero object) | contributes to (vi)/Commitment 3 | `ws6_poles_split` (F4-neg) | **Impossibility-proved** (split), scoped — see §2.3, §2.6 |
| Bullet 2 — no maximal everything (Cantor wall) | "no-everything" obligation | `ws6_no_maximal` (F2) | **Discharged**, by `κ`-fiat (WS1 hand-off) |
| Bullet 3 — no view from nowhere | **(vi), the core** | `ws6_empty_standpoint` (F3) | **Open (vacuous)** — routed, see §2.6 |

**Charter-authorized resolution shape.** §8.1 (WS6) pre-authorizes exactly two terminal shapes for
the poles-coincidence facet: *exhibit* the single ambient category hosting all of
(poles-coincidence, no-everything, groundless carrier), or *declare the split*. This design takes
**declare the split** — a §5 Impossibility-proved outcome — and adopts the §8.2 naming discipline so
the negative is never read as a positive construction.

---

## Part 1 — Paper-decidable triage

*(Triage predicates T1–T7 and the scoring table are retained from the original design; the
collapsed decision — F2 Discharged + F4-negative Impossibility-proved as primary, F3/F5 as
Partial — stands. Two annotations change on charter binding:*

- *F2's T5 (`(F,κ)`-robust) is **Partial**, not Yes: the no-maximal wall consumes the `κ`-bound
  (§2.3, §2.5). This is not a demotion of F2's outcome (still Discharged) but an honest record that
  it pays down WS1's `κ`-fiat rather than escaping it.*
- *F3's Outcome class is **Open (vacuous) → criterion-(vi) shortfall**, sharper than the original
  "Partial," because F3 is the design's only carrier of criterion (vi) and it does not bear content
  (§2.6).)*

**Selected object for full design: F4's negative disjunct — the pole-coincidence split,
`ws6_poles_split` — with F2's `ws6_no_maximal` as its consumed sub-lemma; and the criterion-(vi)
standpoint result `ws6_empty_standpoint` carried as an explicitly-routed open obligation, not a
silent Partial.**

---

## Part 2 — Full mathematical design

### 2.0 Ambient theory and imports

Carrier: `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, the terminal `P_κ`-coalgebra from WS1/WS2.
`F = P_κ`. No monad, no distributive law. AFA modeled coalgebraically. Axiom budget
`[propext, Classical.choice, Quot.sound]`, to be confirmed by a machine-checked `#print axioms`
per the operational note the charter attaches to every workstream (§8.1 WS1/WS3/WS4).

The zero object's load-bearing property is **terminality**: two morphisms into a terminal object
are equal (its hom-sets from any object are subsingletons). This, not "everything factors through a
null morphism," is what generates the contradiction with non-degeneracy.

Imports (established, axiom-free):
- **ws1**: `lambek`, `hom_unique`, `endo_eq_id`, `emptyCoalg`, and — if exposed — the carrier
  cardinality lower bound `mk (νPk κ).X ≥ κ` (see §2.5).
- **ws2**: `ws2_nondegenerate` (**sole load-bearing input to the split**), `ws2_bisim_eq`
  (grounds F3), `diagBisim` (grounds F5).
- **Mathlib**: `CategoryTheory.Limits.HasZeroObject`, `IsZero`, `IsTerminal`,
  `CategoryTheory.Functor`, `CategoryTheory.Faithful`, `Function.cantor_surjective`, and the
  cardinality API for the F2 wall. **`HasZeroMorphisms` is not used** (removed in Revision 1).

### 2.1 Proof architecture (dependency graph)

```
   ws2_nondegenerate (ws2)         HasZeroObject → IsTerminal (0) (Mathlib)
        │ (≥2 states a≠b)                    │ (hom into terminal is subsingleton)
        └──────────────┬──────────────────────┘
                       ▼
             ws6_poles_split   ← F4-neg, IMPOSSIBILITY-PROVED
             (SCOPED: total identification of the carrier with a zero
              object is impossible — the "atom=everything" trivialization)
                       │
                       ├──▶ ws6_no_faithful_zero_host  ← D2 OPEN OBLIGATION
                       │     (the stronger cross-category bridging claim;
                       │      stated, not proved — routed within WS6)
                       ▲
                       │ consumes as wall premise
   WS1 κ-fiat ── ws6_no_maximal ← F2, DISCHARGED (pays down WS1 hand-off)
   (mk X ≥ κ)          (str u ⊆ <κ subset; univ would force mk X < κ)
                       │
   ws2_bisim_eq (ws2) ─┴── ws6_empty_standpoint ← F3
                            VACUOUS via endo_eq_id
                            └──▶ CRITERION (vi) SHORTFALL  ← D1
                                 routed to §2.6 (needs non-terminal views)
                       │
   emptyCoalg (ws1) ── ws6_relative_bottom ← F5, PARTIAL-by-construction
                       ▼
             ws6_split_and_no_maximal   ← assembly (NOT ws6_resolved)
```

### 2.2 Definitions

**Faithful embedding of the carrier's distinctness (F4).** A faithful functor out of a small
carrier-derived category carrying a genuine parallel-witness (two distinct parallel morphisms
sourced from the ≥2 non-bisimilar states). Faithfulness is the load-bearing property.

```lean
structure ParallelWitness (κ : Cardinal.{u}) (D : Type v) [Category.{w} D] where
  A B      : D
  f g      : A ⟶ B
  distinct : f ≠ g

structure FaithfulCarrierEmbedding
    (κ : Cardinal.{u}) (C : Type v) [Category.{w} C] where
  D        : Type w
  instD    : Category.{w} D
  witness  : ParallelWitness κ D
  F        : D ⥤ C
  faithful : F.Faithful
```

**No-maximal predicate (F2).**

```lean
def IsMaximal (u : (νPk κ).X) : Prop := ∀ v : (νPk κ).X, v ∈ ((νPk κ).str u).1
```

**Position-free view (F3).** Its vacuity is the whole point; retained to *state* the (vi) shortfall
precisely rather than hide it.

```lean
def PositionFree (obs : (νPk κ).X → Prop) : Prop :=
  ∀ (h : (νPk κ).X → (νPk κ).X),
    (∀ x, (νPk κ).str (h x) = PkMap κ h ((νPk κ).str x)) → ∀ x, obs (h x) = obs x
```

**Relative bottom (F5).**

```lean
noncomputable def bottomState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (emptyCoalg hinf)).choose PUnit.unit
```

### 2.3 Lemmas and theorems

**F2 — no maximal element (Discharged; pays down WS1's `κ`-fiat).**

```lean
theorem ws6_no_maximal (hcard : mk (νPk κ).X ≥ κ) (u : (νPk κ).X) : ¬ IsMaximal u
```

`IsMaximal u` means `(str u).1 = univ`. Since `str u : PkObj κ (…)` is a `< κ`-bounded subset,
maximality forces `mk (νPk κ).X < κ`, contradicting `hcard`. **Charter binding (D3 fix):** `hcard`
is *not* a new WS6 hazard. §3.7 [REV-A] and §8.1 (WS1) already declare that "no maximal everything
holds by fiat of the cardinal bound `κ`" and route it "as an obligation on WS6/WS7." This theorem
**is the discharge of that hand-off** — WS6 paying WS1's declared debt, not incurring its own. If
WS1 exposes `mk (νPk κ).X ≥ κ` as a ratified lemma, `hcard` is discharged internally and the
coupling is inherited from WS1 verbatim; otherwise it is WS6's local statement of the same fact.
The `κ`-dependence is exactly why §3.7's bullet 2 is secured "by fiat" and not by a `Set`-level
Cantor argument — the charter already concedes this, and the design does not pretend otherwise.

**F4 — the pole-coincidence split (Impossibility-proved, primary; scoped — D2 fix).**

```lean
theorem ws6_poles_split
    (C : Type v) [Category.{w} C] [Limits.HasZeroObject C]
    (E : FaithfulCarrierEmbedding κ C)
    (coincide : ∀ x, Limits.IsZero (E.F.obj x)) : False
```

Proof. From `coincide`, every `E.F.obj x` is a zero object, hence terminal, so any hom-set
`E.F.obj A ⟶ E.F.obj B` is a subsingleton: `E.F.map E.witness.f = E.F.map E.witness.g`.
Faithfulness gives `E.witness.f = E.witness.g`, contradicting `E.witness.distinct`. ∎

**Charter binding and honest scope (D2 fix).** The `coincide` premise is exactly the charter's
**"atom = everything" trivialization hazard** (§8 standing risk: "'Atom = everything' must be a
zero object, kept strictly apart from the incoherent universal set. Conflating them sinks the
program"). So what is proved is precisely: *the carrier cannot be totally identified with the zero
object without contradicting non-degeneracy* — the conflation the charter fears is fatal, proved.
This **is** a legitimate "declare the split": the poles-coincidence object and the groundless
carrier cannot be the *same* object.

What this theorem does **not** prove — and the prior design's prose wrongly claimed — is the
broader §8.1 bridging statement that no zero-object category *whatsoever* can faithfully host the
carrier's distinctions. A zero-object category (e.g. `Ab`, `Vec`, pointed sets) can host distinct
states faithfully as long as their images are *not* all zero objects; `coincide` is what rules that
out, and it is a strong premise. The general claim is therefore carried as a **named open
obligation, not a theorem:**

```lean
/-- OPEN (routed within WS6, D2). The stronger cross-category bridging claim the
    charter §8.1 note gestures at: no faithful structure-preserving embedding of the
    carrier into ANY zero-object category exists, without assuming total coincidence.
    Not proved here; `ws6_poles_split` proves only the `coincide` (total-collapse) case. -/
def ws6_no_faithful_zero_host (κ : Cardinal.{u}) : Prop :=
  ∀ (C : Type u) [Category.{u} C] [Limits.HasZeroObject C],
    IsEmpty (FaithfulCarrierEmbedding κ C)
```

This is stated `False`-free as a `Prop` and left unproved, with its obstruction precise: it is
almost certainly **false as stated** (pointed sets host the carrier faithfully), which is itself the
finding — the honest cross-category result is that the split holds *only* against total coincidence,
so §8.1's "different objects in different categories" is confirmed *as a split*, not as a blanket
non-embeddability. Recording it this way prevents the overclaim and gives WS7 a precise object to
ratify or refute against its final `(F, κ)`.

**Non-vacuity guard for F4.**

```lean
theorem ws6_embedding_nonvacuous :
    ∃ (C : Type u) (_ : Category.{u} C),
      Nonempty (FaithfulCarrierEmbedding κ C) ∧
      ¬ (∃ E : FaithfulCarrierEmbedding κ C, ∀ x, Limits.IsZero (E.F.obj x))
```

Certifies both that the hypothesis of `ws6_poles_split` is inhabited (so the theorem is not vacuous)
and that `coincide` genuinely fails in a witness category (so `coincide` carries the weight). Take
`C = D =` the two-object category with two distinct parallel maps and `F = 𝟭`; `ws2_nondegenerate`
justifies the distinctness. This `C` has no zero object collapsing both objects, so `coincide` is
false here — isolating `coincide` as the operative hypothesis.

**F3 — empty standpoint (Vacuous; criterion-(vi) shortfall, D1 fix).**

```lean
theorem ws6_empty_standpoint (obs : (νPk κ).X → Prop) (h : PositionFree obs) :
    (∀ u, obs u) ∨ (∀ u, ¬ obs u)
```

Proof: `PositionFree` quantifies over endo-coalgebra maps; `endo_eq_id` (ws1) forces each to be
`id`, so `h` is satisfiable only trivially and the disjunction holds without using `h`'s content. ∎

**Charter binding — this is the design's most important honest statement (D1 fix).** Criterion
**(vi)** — "no substantive terminal standpoint," the criterion the charter most centrally assigns to
WS6 (§4 WS6 line: "the emptiness of the external standpoint"; §3.7 bullet 3: "every genuine view is
internal… no global section over the whole") — is carried *only* by this theorem, and this theorem
is **vacuous**: it proves emptiness-of-standpoint by having no non-trivial standpoint to quantify
over, which is not the same as proving that substantive standpoints are empty. **Therefore
criterion (vi) is not discharged by this design.** The obstruction is exact and is routed in §2.6.
This is stated here, at the theorem, so no importer reads `ws6_empty_standpoint`'s `True`-ness as
(vi) closed — the same discipline WS4 applied with `ws4_graded_coherence_Luk`.

**F5 — relative bottom (Partial-by-construction).**

```lean
theorem ws6_relative_bottom (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (bottomState hinf)).1 = (∅ : Set (νPk κ).X) ∧
    Nonempty (Bisim (νPk κ) (fun a b => a = b))
```

Captures the bottom pole (empty-observation state) and certifies the identity theory is untouched
(`diagBisim`). The "everything" pole is explicitly not delivered — that is the F4 split. Partial.

### 2.4 The assembly

```lean
structure WS6NoPoles (κ : Cardinal.{u}) where
  hinf         : ℵ₀ ≤ κ
  hcard        : mk (νPk κ).X ≥ κ
  no_maximal   : ∀ u : (νPk κ).X, ¬ IsMaximal u
  poles_split  : ∀ (C : Type u) [Category.{u} C] [Limits.HasZeroObject C]
                   (E : FaithfulCarrierEmbedding κ C),
                   (∀ x, Limits.IsZero (E.F.obj x)) → False
  standpoint   : ∀ obs, PositionFree obs → (∀ u, obs u) ∨ (∀ u, ¬ obs u)
  rel_bottom   : ((νPk κ).str (bottomState hinf)).1 = ∅
  -- NOTE: no `standpoint_substantive` field. Criterion (vi) is deliberately ABSENT
  -- from the discharged bundle; it is the routed open obligation of §2.6, not a
  -- field that could be mistaken for a discharge.

theorem ws6_split_and_no_maximal
    (hinf : ℵ₀ ≤ κ) (hcard : mk (νPk κ).X ≥ κ) : Nonempty (WS6NoPoles κ)
```

Named `ws6_split_and_no_maximal`, **not** `ws6_resolved` / `ws6_zero_object` / `ws6_no_standpoint`:
the pole-coincidence facet is an impossibility (the scoped split), the standpoint criterion (vi) is
*not* in the bundle at all, and a positive-sounding name would launder both. Universe honesty: the
assembly fixes `Type u`; the standalone `ws6_poles_split` is polymorphic `(C : Type v)`. The bundle
records the `u`-instance (which the `Type u` non-vacuity witness supports); the polymorphic strength
is not claimed by the bundle.

### 2.5 Dependencies on imported theorems (explicit)

- `ws2_nondegenerate` → sole load-bearing input to `ws6_poles_split`. **WS6→WS7 coupling:** if WS7
  changes `(F, κ)` and non-degeneracy needs re-proof, the split must be re-ratified. (Unchanged.)
- `mk (νPk κ).X ≥ κ` → input to `ws6_no_maximal`. **This is the discharge of WS1's declared
  `κ`-fiat hand-off** (§3.7 [REV-A], §8.1 WS1), *not* a new WS6-originated hazard (D3 fix). It is
  `(F, κ)`-coupled because §3.7 bullet 2 is `κ`-secured *by the charter's own concession*; WS6
  inherits this, it does not create it. Routed to WS7's collector as part of the pre-existing WS1
  obligation.
- `endo_eq_id` (ws1) → the F3 vacuity, hence the criterion-(vi) shortfall (§2.6). This is what makes
  (vi) open rather than discharged.
- `emptyCoalg`, `diagBisim` (ws1/ws2) → F5 relative bottom.
- Mathlib `HasZeroObject` / `IsZero` / `IsTerminal` / `Faithful` → the F4 split. No custom ambient
  category is constructed (the source `D` is small and carrier-derived), so no re-proof of the
  identity theory is incurred — F4 passes T2 (carrier-preserving) where F1 failed.

### 2.6 [D1] Criterion (vi) shortfall — stated and routed, in §8.2 discipline

**The shortfall.** Criterion (vi) "no substantive terminal standpoint" is the criterion the charter
most centrally assigns to WS6, and this design discharges it only **vacuously**: `PositionFree`
collapses under `endo_eq_id`, so `ws6_empty_standpoint` says "there is no non-trivial global view to
quantify over," which is weaker than the charter's §3.7 bullet 3 content — "every genuine view is
internal, sheaf-like local sections with no global section over the whole." Vacuity is not that
content; it is the absence of the objects that would carry it.

**Why the vacuity is forced, precisely.** On the *terminal* carrier `νPk κ`, every endo-coalgebra
map is the identity (`endo_eq_id`, itself a consequence of terminality / `hom_unique`). So the only
"views" expressible as endomorphisms of the carrier are trivial, and any predicate invariant under
them is unconstrained. The content of (vi) requires a genuinely larger class of views — **spans out
of non-terminal coalgebras** (local sections indexed by objects that are *not* the whole), which the
terminal carrier alone does not furnish. This is the sheaf-theoretic "local sections, no global
section" picture §3.7 names, and it is not constructible inside the terminal object by itself.

**Route (per §5 / §8.2).** The obstruction is handed off, not relabeled:
1. Criterion (vi) is reported **Open**, with obstruction = "the terminal carrier admits only
   trivial endo-views (`endo_eq_id`); substantive standpoints require non-terminal-coalgebra spans
   not available on `νPk κ` alone."
2. The content-bearing standpoint theory is routed to a **site/sheaf layer over the category of
   `P_κ`-coalgebras** (local sections = views from non-terminal objects; the claim to prove is *no
   global section over the terminal object*, which would be the substantive form of "no view from
   nowhere"). This is a WS6 residual that couples to WS2's choice of coalgebra category and to WS7's
   `(F, κ)` ratification.
3. Nothing in the discharged bundle (`WS6NoPoles`) is named or shaped so that (vi) could be read as
   closed; the criterion is deliberately absent from the structure (§2.4).

**Consequence for the WS6 terminal class.** WS6 is **Partial**, and the Partial is driven *primarily*
by the criterion-(vi) shortfall — not by F3/F5 being incidental extra facets. The headline
Impossibility (the scoped split) resolves the poles-coincidence *hazard*, but it is not criterion
(vi), and the design says so.

### 2.7 Expected terminal status (charter §5 vocabulary)

- `ws6_no_maximal` — **Discharged**, by `κ`-fiat; robustness Partial; **binding:** discharges WS1's
  §3.7-bullet-2 hand-off, contributes to the "no-everything" obligation. Not `(F,κ)`-independent
  (inherited, per §2.5/D3).
- `ws6_poles_split` — **Impossibility-proved (scoped)**; **binding:** resolves the §8 "atom =
  everything" trivialization hazard and Commitment-3 poles-coincidence as a declared split; the
  broader cross-category claim is the *open* `ws6_no_faithful_zero_host` (D2), not proved.
- `ws6_empty_standpoint` — **Open (vacuous)**; **binding:** carries criterion **(vi)**, which is
  therefore **not discharged**; obstruction routed to a sheaf/site layer (§2.6, D1). This is the
  design's principal residual.
- `ws6_relative_bottom` — **Partial-by-construction**; the "everything" pole is the F4 split.

**Overall WS6: Partial.** Faithful to the charter's two-shape authorization (declare the split),
with the split proved on the correct (terminality) mechanism and honestly scoped to total
coincidence; the "no-maximal" hand-off from WS1 discharged by `κ`-fiat as the charter concedes; and
the workstream's core criterion (vi) reported Open with a precise, routed obstruction rather than
laundered through a vacuous theorem. The single most charter-relevant statement of this design:
**the poles-coincidence hazard resolves as a provable split, but criterion (vi) — the emptiness of
the external standpoint with content — is not delivered by the terminal carrier and is routed
forward.**
