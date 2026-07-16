/-
`series-03/formal/ws6.lean`

WS6 (`series-03/spec/ws6/04-charter-design-review.md`, rev. 2): **no poles, no
outside.** The charter's two-shape authorization for the poles-coincidence facet is
resolved as **declare the split** — a §5 Impossibility-proved outcome — with the
"no-maximal" hand-off from WS1 discharged by `κ`-fiat, and the core criterion (vi)
reported **Open** with a precise routed obstruction (never laundered).

Built on `ws1`/`ws2` (imported, axiom-free): `endo_eq_id`, `emptyCoalg`,
`mk_empty_lt`, `νPk`, `νPk_terminal`, `diagBisim`, `Bisim`, `PkMap(_val)`. Uses
Mathlib `CategoryTheory` (`HasZeroObject`/`IsZero`/`Faithful`). WS3/WS4 not needed.

## Outcome: PARTIAL, exactly as the charter §8.1 pre-registers

* **F4 — pole-coincidence split: Impossibility-proved (scoped).** `ws6_poles_split`:
  if a faithful carrier-embedding lands entirely in zero objects (`coincide`), a
  contradiction follows — the "atom = everything" trivialization the charter fears is
  fatal. The load-bearing mechanism is **terminality** (two morphisms into a zero
  object agree), not null morphisms. `ws6_embedding_nonvacuous` certifies the
  hypothesis is inhabited and `coincide` genuinely carries the weight. The broader
  cross-category claim is the *named open obligation* `ws6_no_faithful_zero_host`
  (D2), stated not proved — almost certainly false as a blanket (pointed sets host
  the carrier faithfully), which is itself the finding: the split holds only against
  *total* coincidence.
* **F2 — no maximal element: Discharged (by `κ`-fiat).** `ws6_no_maximal`:
  maximality would force the `< κ` support to be all of the carrier, contradicting
  `κ ≤ #(νPk κ).X`. This **discharges WS1's declared `κ`-fiat hand-off** (§3.7
  [REV-A]), not a new WS6 hazard (D3).
* **F3 — empty standpoint: Open (vacuous) → criterion (vi) shortfall (D1).** See the
  honest-signature note below. `ws6_standpoint_vacuous` proves the *true* content:
  `PositionFree` is vacuous (holds for every `obs`) because the terminal carrier
  admits only the identity endo-view (`endo_eq_id`). That vacuity is precisely why
  **criterion (vi) is NOT discharged** — substantive standpoints need non-terminal
  spans the terminal carrier does not furnish (routed, design §2.6).
* **F5 — relative bottom: Partial-by-construction.** `ws6_relative_bottom`: the
  empty-observation pole exists and the identity theory is untouched (`diagBisim`).
* **Assembly.** `WS6NoPoles` / `ws6_split_and_no_maximal`, named to keep criterion
  (vi) OUT of the discharged bundle (the WS4 `ws4_graded_coherence_Luk` discipline).

All `sorry`-free and **axiom-free** beyond Mathlib's standard
`propext`/`Classical.choice`/`Quot.sound` (verify `#print axioms
ws6_split_and_no_maximal`).

## Honest signature note (a faithful correction, surfaced not silently patched)

The design's §2.3 `ws6_empty_standpoint : (∀ u, obs u) ∨ (∀ u, ¬ obs u)` is **false
as stated**: since `endo_eq_id` makes `PositionFree obs` hold *vacuously for every*
`obs`, that disjunction would force every predicate to be constant — refuted by any
non-constant `obs` on the ≥2-element carrier. The design's own prose says F3 is
"vacuous" and (vi) is not discharged; the literal disjunction over-shoots that into an
untrue proposition. The honest realization is `ws6_standpoint_vacuous : ∀ obs,
PositionFree obs` — true, and exactly the "there is no substantive standpoint
constraint" content that leaves (vi) Open. This mirrors the WS4 `pentagon` erratum
and WS5 `Nonempty` corrections. `κ.IsRegular` is non-load-bearing throughout.
-/
import ws2

universe u v w

open CategoryTheory Limits Cardinal Series03.WS1 Series03.WS2

attribute [local instance] Classical.propDecidable

namespace Series03.WS6

variable {κ : Cardinal.{u}}

/-! ## §2.2 Definitions -/

/-- A genuine parallel-witness in a category: two distinct parallel morphisms
(sourced, in the intended reading, from the ≥2 non-bisimilar carrier states). -/
structure ParallelWitness (κ : Cardinal.{u}) (D : Type v) [Category.{w} D] where
  A : D
  B : D
  f : A ⟶ B
  g : A ⟶ B
  distinct : f ≠ g

/-- A faithful embedding of a small carrier-derived category `D` (carrying a genuine
parallel-witness) into `C`. **Faithfulness is the load-bearing property.** The source
`D` and its category are explicit parameters (rather than bundled fields) — an
equivalent formalization that avoids a typeclass diamond on the bundled instance. -/
structure FaithfulCarrierEmbedding (κ : Cardinal.{u})
    (D : Type w) [Category.{w} D] (C : Type v) [Category.{w} C] where
  witness : ParallelWitness κ D
  F : D ⥤ C
  [faithful : F.Faithful]

attribute [instance] FaithfulCarrierEmbedding.faithful

/-- Maximality: `u`'s attention support is the whole carrier — the "everything" pole. -/
def IsMaximal (u : (νPk κ).X) : Prop := ∀ v : (νPk κ).X, v ∈ ((νPk κ).str u).1

/-- A position-free (endo-invariant) observation. Its vacuity is the whole point
(design §2.2, F3). -/
def PositionFree (obs : (νPk κ).X → Prop) : Prop :=
  ∀ (h : (νPk κ).X → (νPk κ).X),
    (∀ x, (νPk κ).str (h x) = PkMap κ h ((νPk κ).str x)) → ∀ x, obs (h x) = obs x

/-- The relative bottom: the empty-observation state, as the terminal image of the
empty coalgebra. -/
noncomputable def bottomState (hinf : ℵ₀ ≤ κ) : (νPk κ).X :=
  (νPk_terminal κ (emptyCoalg hinf)).choose PUnit.unit

/-! ## §2.3 F2 — no maximal element (Discharged, by `κ`-fiat) -/

/-- **F2 (Discharged).** No carrier state is maximal: maximality injects the whole
carrier into the `< κ` support, forcing `#(νPk κ).X < κ`, contradicting `κ ≤ #`.
This **discharges WS1's declared `κ`-fiat hand-off** (§3.7 [REV-A]), not a new
hazard. -/
theorem ws6_no_maximal (hcard : κ ≤ Cardinal.mk (νPk κ).X) (u : (νPk κ).X) :
    ¬ IsMaximal u := by
  intro hmax
  have hinj : Function.Injective
      (fun v : (νPk κ).X => (⟨v, hmax v⟩ : ↥((νPk κ).str u).1)) :=
    fun a b hab => congrArg Subtype.val hab
  have hle : Cardinal.mk (νPk κ).X ≤ Cardinal.mk ↥((νPk κ).str u).1 :=
    Cardinal.mk_le_of_injective hinj
  exact absurd (lt_of_le_of_lt hle ((νPk κ).str u).2) (not_lt.mpr hcard)

/-! ## §2.3 F4 — the pole-coincidence split (Impossibility-proved, scoped) -/

/-- **F4 (Impossibility-proved, scoped — the primary result).** A faithful
carrier-embedding cannot land entirely in zero objects: `coincide` makes each
`E.F.obj x` terminal, so the two parallel images agree, and faithfulness collapses
the witness — contradicting `distinct`. The mechanism is **terminality**. This is the
charter's "atom = everything" trivialization, proved fatal (a declared split). -/
theorem ws6_poles_split (D : Type w) [Category.{w} D] (C : Type v) [Category.{w} C]
    [HasZeroObject C] (E : FaithfulCarrierEmbedding κ D C)
    (coincide : ∀ x, IsZero (E.F.obj x)) : False := by
  have heq : E.F.map E.witness.f = E.F.map E.witness.g :=
    (coincide E.witness.B).eq_of_tgt (E.F.map E.witness.f) (E.F.map E.witness.g)
  exact E.witness.distinct (E.F.map_injective heq)

/-- **OPEN (routed within WS6, D2).** The stronger cross-category claim the §8.1 note
gestures at: no faithful embedding of the carrier into ANY zero-object category, sans
total coincidence. Stated as a `Prop`, left unproved — almost certainly *false* as a
blanket (pointed sets host the carrier faithfully), which is the honest finding: the
split holds only against total coincidence. A precise object for WS7 to ratify. -/
def ws6_no_faithful_zero_host (κ : Cardinal.{u}) : Prop :=
  ∀ (C : Type u) [Category.{u} C] [HasZeroObject C] (D : Type u) [Category.{u} D],
    IsEmpty (FaithfulCarrierEmbedding κ D C)

/-! ### Non-vacuity witness for F4 (a single-object non-zero category) -/

/-- The witness category: one object, hom-monoid `Bool` under `&&` (unit `true`). The
object is **not** a zero object (its endo-hom `Bool` is not a subsingleton), so
`coincide` genuinely fails here — isolating it as the operative hypothesis of F4. -/
def WCat : Type u := PUnit.{u+1}

noncomputable instance : Category.{u} WCat where
  Hom _ _ := ULift.{u} Bool
  id _ := ULift.up true
  comp f g := ULift.up (f.down && g.down)
  id_comp f := by cases f with | up b => simp
  comp_id f := by cases f with | up b => simp
  assoc f g h := by cases f; cases g; cases h; simp [Bool.and_assoc]

/-- A faithful carrier-embedding into `WCat`: identity functor on the one-object
category, with the two distinct parallel morphisms `true ≠ false`. -/
noncomputable def wcatEmbedding : FaithfulCarrierEmbedding κ WCat WCat where
  witness :=
    { A := PUnit.unit, B := PUnit.unit, f := ULift.up true, g := ULift.up false
    , distinct := by
        intro h
        have h' : (ULift.up true : ULift.{u} Bool) = ULift.up false := h
        simp at h' }
  F := 𝟭 WCat

/-- **Non-vacuity of F4.** The hypothesis of `ws6_poles_split` is inhabited (there is
a faithful carrier-embedding), and `coincide` genuinely fails in a witness category
(so it carries the weight, and the theorem is not vacuous). -/
theorem ws6_embedding_nonvacuous :
    ∃ (C : Type u) (_ : Category.{u} C),
      Nonempty (FaithfulCarrierEmbedding κ C C) ∧
      ¬ (∃ E : FaithfulCarrierEmbedding κ C C, ∀ x, IsZero (E.F.obj x)) := by
  refine ⟨WCat, inferInstance, ⟨wcatEmbedding⟩, ?_⟩
  rintro ⟨E, hE⟩
  have hz := hE E.witness.A
  have heq : (ULift.up true : E.F.obj E.witness.A ⟶ E.F.obj E.witness.A)
           = (ULift.up false : E.F.obj E.witness.A ⟶ E.F.obj E.witness.A) :=
    hz.eq_of_tgt (Y := E.F.obj E.witness.A) _ _
  have heq' : (ULift.up true : ULift.{u} Bool) = ULift.up false := heq
  simp at heq'

/-! ## §2.3 F3 — empty standpoint (Open/vacuous → criterion (vi) shortfall) -/

/-- **F3 (Open/vacuous) — the honest form (see the header signature note).**
`PositionFree` is vacuous: it holds for *every* observation, because `endo_eq_id`
forces every endo-coalgebra map on the terminal carrier to be the identity. This
vacuity is exactly why **criterion (vi) is NOT discharged** — there is no substantive
standpoint constraint to satisfy; the content of (vi) requires non-terminal spans the
terminal carrier does not furnish (routed, design §2.6). The design's disjunction
`(∀u,obs u) ∨ (∀u,¬obs u)` is false-as-stated and is deliberately NOT claimed. -/
theorem ws6_standpoint_vacuous (obs : (νPk κ).X → Prop) : PositionFree obs := by
  intro h hh x
  have hid : h = id := endo_eq_id (νPk_terminal κ) h hh
  simp [hid]

/-! ## §2.3 F5 — relative bottom (Partial-by-construction) -/

/-- **F5 (Partial-by-construction).** The empty-observation pole exists (the terminal
image of the empty coalgebra observes nothing), and the identity theory is untouched
(`diagBisim`). The "everything" pole is precisely the F4 split, not delivered here. -/
theorem ws6_relative_bottom (hinf : ℵ₀ ≤ κ) :
    ((νPk κ).str (bottomState hinf)).1 = (∅ : Set (νPk κ).X) ∧
    Nonempty (Bisim (νPk κ) (fun a b => a = b)) := by
  refine ⟨?_, ⟨diagBisim (νPk κ)⟩⟩
  have hnat := (νPk_terminal κ (emptyCoalg hinf)).choose_spec.1 PUnit.unit
  unfold bottomState
  rw [hnat]
  simp [PkMap_val, emptyCoalg]

/-! ## §2.4 The assembly -/

/-- The WS6 "no poles, no outside" bundle. **Criterion (vi) is deliberately ABSENT**
(no `standpoint_substantive` field): it is the routed open obligation of §2.6, not a
field that could be mistaken for a discharge. `standpoint_vacuous` records only the
vacuity that *causes* the (vi) shortfall. -/
structure WS6NoPoles (κ : Cardinal.{u}) where
  hinf               : ℵ₀ ≤ κ
  hcard              : κ ≤ Cardinal.mk (νPk κ).X
  no_maximal         : ∀ u : (νPk κ).X, ¬ IsMaximal u
  poles_split        : ∀ (D : Type u) [Category.{u} D] (C : Type u) [Category.{u} C]
                         [HasZeroObject C] (E : FaithfulCarrierEmbedding κ D C),
                         (∀ x, IsZero (E.F.obj x)) → False
  standpoint_vacuous : ∀ (obs : (νPk κ).X → Prop), PositionFree obs
  rel_bottom         : ((νPk κ).str (bottomState hinf)).1 = (∅ : Set (νPk κ).X)

/-- **The WS6 deliverable.** Named `ws6_split_and_no_maximal`, **not** `ws6_resolved`
/ `ws6_zero_object` / `ws6_no_standpoint`: the poles-coincidence facet is an
impossibility (the scoped split), the no-maximal wall is discharged by `κ`-fiat, and
criterion (vi) is *not in the bundle at all* — a positive-sounding name would launder
both. -/
theorem ws6_split_and_no_maximal (hinf : ℵ₀ ≤ κ)
    (hcard : κ ≤ Cardinal.mk (νPk κ).X) : Nonempty (WS6NoPoles κ) := by
  refine ⟨{ hinf := hinf
          , hcard := hcard
          , no_maximal := fun u => ws6_no_maximal hcard u
          , poles_split := ?_
          , standpoint_vacuous := ws6_standpoint_vacuous
          , rel_bottom := (ws6_relative_bottom hinf).1 }⟩
  intro D _ C _ _ E hco
  exact ws6_poles_split D C E hco

end Series03.WS6
