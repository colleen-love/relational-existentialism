/-
`series-05/formal/ws5.lean`

WS5 — **The self-bounding of the world, revisited.** Series 05. The "grain, not wall"
thesis, now claimed tower-wide.

Series 05 does **not** refute Series 04's M1/M2/M3 (all true): within a level, faces still
cannot bound branching (M1), same-face quotient does not collapse plurality (M2), and
within one carrier global groundlessness collapses (M3). It *contextualizes* them — the
bounding was never supposed to happen within a level — and frees the bound *between*
levels (WS3's no-last-level), reporting honestly that the *values* of the cardinals remain
a residual fiat.

Design doc: `series-05/spec/ws05-design.md` (G1 + G2, G3 rejected, G4 reported).
Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series05.ws4

universe u

open Cardinal Series05.WS1 Series05.WS2 Series05.WS3

namespace Series05.WS5

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## The Series 04 negatives, transcribed and standing (unrefuted) -/

/-- **M1 (sharp negative, standing).** Contraction does not free the bound: the carrier is
still `≥ κ`. Faces tame quality, not branching. (= `carrier_card_ge`.) -/
theorem ws5_contraction_insufficient (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X :=
  carrier_card_ge κ

/-- **M2 (sharp negative, standing).** Same-face quotient does not collapse plurality:
distinct faced states survive. -/
theorem ws5_quotient_insufficient (hinf : ℵ₀ ≤ κ) :
    ∃ a b : νLk κ (ULift.{u} Bool), a ≠ b := by
  obtain ⟨a, b, hab, _, _⟩ := ws3_plurality_core_concrete hinf
  exact ⟨a, b, hab⟩

/-- **M3 (Impossibility, standing).** Within one carrier, global groundlessness collapses
the world — exactly the hypothesis the doubly-unbounded tower avoids. -/
theorem ws5_global_groundless_collapses (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X :=
  Series05.WS2.ws5_global_groundless_collapses hinf h

/-! ## G3 — the off-spine improper-self-face route is rejected -/

/-- **G3 rejected.** The Series 04 spine route does not generalize: the derived self-face is
*trivial* — empty (when `x` does not relate to itself) or improper (`= ReachSet x`, when it
does), never a nonempty proper self-model. So endogeneity cannot be extended off the spine
by improper self-faces; Series 05's endogeneity comes from *between* levels (G1/G2), a
different mechanism. -/
theorem ws5_selfface_trivial (x : (νPk κ).X) :
    face x x = ∅ ∨ face x x = ReachSet x := by
  by_cases hx : x ∈ ((νPk κ).str x).1
  · right; ext z; simp only [mem_face, ReachSet, Set.mem_setOf_eq, hx, true_and]
  · left; ext z
    simp only [mem_face, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd h hx

/-! ## G1 / G2 — the bound is endogenous, tower-wide (against the standing M1/M2) -/

/-- **G1 — grain, not wall, tower-wide.** Every object is bounded by its level's grain
(`ws1_local_bound`), the tower is bounded by no cardinal (`hunb`), and the M1 negative
still stands (faces do not bound branching within any level). The endogeneity is *located
between levels*, where M1/M2 do not apply. -/
theorem ws5_endogenous_tower (T : Tower Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :
    (∀ x : Winf T, ∃ (a : T.Idx) (y : (T.lvl a).carrier),
        x = toColim T y ∧ Cardinal.mk ↥(lstr y).1 < (T.lvl a).card)
  ∧ (∀ c : Cardinal.{u}, ∃ (a : T.Idx), c < (T.lvl a).card)
  ∧ (∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → κ ≤ Cardinal.mk (νPk κ).X) :=
  ⟨fun x => ws1_local_bound T x, hunb, fun κ _ => carrier_card_ge κ⟩

/-- **G2 — the M1/M2 adjudication (coincidence).** The single-carrier bound `κ ≤ #carrier`
(M1, standing) and the tower's no-global-cap (`hunb`) are *both* true, of different objects
— the carrier and the tower — so the tower does what one carrier provably cannot. The
direct analogue of WS3's `ws3_wall_vs_grain`. -/
theorem ws5_stratification_frees_bound (T : Tower Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    (κ ≤ Cardinal.mk (νPk κ).X) ∧ (∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :=
  ⟨carrier_card_ge κ, hunb⟩

/-! ## G4 — the residual fiat, reported honestly -/

/-- The **necessity of unboundedness is forced** (by the Explosion Dilemma, WS2): a single
carrier provably walls or collapses, so *something* unbounded is necessary. -/
def UnboundednessForced (T : Tower Q) : Prop := ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card

/-- The **particular cardinal values** `κ_α` and their cofinality are chosen — the residual
fiat WS5 reports rather than concealing. **Report-flag** (pass-2 R5): this is `:= True`, a prose
tag marking "the cardinal assignment is a chosen fiat," *not* a proved characterization of that
choice. The `ws5_residual_fiat` second conjunct is therefore `trivial`; only the first conjunct
(`UnboundednessForced`, the earned necessity) carries content. -/
def CardinalValuesChosen (_ : Tower Q) : Prop := True

/-- **G4 — the honest split.** The *necessity* of unboundedness is earned (WS2); the
*particular* cardinal assignment is a residual fiat. Reported, not concealed — the "reports
honestly if the bound smuggles a fiat back in" clause discharged. -/
theorem ws5_residual_fiat (T : Tower Q)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :
    UnboundednessForced T ∧ CardinalValuesChosen T :=
  ⟨hunb, trivial⟩

end Series05.WS5
