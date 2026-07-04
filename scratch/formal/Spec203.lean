/-
Spec 2.03 — certify the Mirror.

Normative sources: `scratch/spec/2-03.md` (the finding), `scratch/spec/2-00.md`.
Builds on `Spec201`/`Spec201b`/`Spec201c`/`Spec201d` (imported).

Spec201c constructed Ω₀ correctly for a signature that turns out to be the boolean
shadow in two-sorted clothing. T1 fires: the universe is one point. This file proves
that fact with dignity, proves the coincidence of the framework's four forbidden
extremes at that point, and banks the honesty lemmas that keep T5/T10's current
status from being misread. Certification, not construction — the repo's proudest scar.
-/
import Spec201
import Spec201b
import Spec201c
import Spec201d
import Spec202

namespace RelEx
namespace TwoSorted

/-- Over a one-point world every unordered pair is the diagonal. -/
instance : Subsingleton (Sym2 PUnit) := ⟨by
  intro a b
  induction a using Sym2.ind with | _ a1 a2 =>
  induction b using Sym2.ind with | _ b1 b2 =>
  rw [Subsingleton.elim a1 b1, Subsingleton.elim a2 b2]⟩

/-! ## DIAG and UNIT -/

/-- Spec 2-03 D20 — THE F(1) DIAGNOSIS. Over a one-point world there is exactly one
possible unfolding: `Sym2 PUnit` is a singleton, and the nonempty finite subsets of a
singleton are one element. G(1) ≅ 1 is the collapse criterion made concrete — the
Parmenides check, failed by the quality-free signature. Every future functor computes
this BEFORE construction (D20, pre-registered). -/
theorem G_unit_subsingleton : Subsingleton (G PUnit) := ⟨by
  intro a b
  apply Subtype.ext
  apply Set.eq_of_subset_of_subset
  · intro p _
    obtain ⟨q, hq⟩ := b.2.2
    rwa [Subsingleton.elim p q]
  · intro p _
    obtain ⟨q, hq⟩ := a.2.2
    rwa [Subsingleton.elim p q]⟩

/-- The one-point bounded Raw: one object, one self-relation, whole-pattern.
The Raw form of Spec200's `Shadow.unit`. -/
def unitRaw : Raw where
  O := PUnit
  R := PUnit
  endpoints _ := s(PUnit.unit, PUnit.unit)
  pat _ := Set.univ
  pat_nonempty _ := ⟨PUnit.unit, trivial⟩

/-- The one-point Raw is final among bounded Raws — the two-sorted `unit_final`.
Existence: constant maps; `end_comm` because `Sym2 PUnit` is a subsingleton;
`pat_comm` because `Set PUnit`'s universe equals the image of any nonempty set
(the Spec200 crux, reused: nonemptiness is used exactly once, and must be).
Uniqueness: both carrier maps land in `PUnit`. -/
theorem isFinalBRaw_unitRaw : IsFinalBRaw unitRaw := by
  refine ⟨?bounded, fun A _ => ?main⟩
  case bounded => intro _; show (Set.univ : Set PUnit).Finite; exact Set.finite_univ
  case main =>
    refine ⟨⟨fun _ => PUnit.unit, fun _ => PUnit.unit,
      fun _ => Subsingleton.elim (α := Sym2 PUnit) _ _, ?patc⟩, trivial, ?uniq⟩
    case patc =>
      intro x
      show Set.univ = (fun _ => PUnit.unit) '' A.pat x
      refine (Set.eq_univ_iff_forall.mpr (fun p => ?_)).symm
      obtain ⟨r, hr⟩ := A.pat_nonempty x
      exact ⟨r, hr, Subsingleton.elim (α := PUnit) _ _⟩
    case uniq =>
      rintro ⟨fO, fR, -, -⟩ -
      have hfO : fO = fun _ => PUnit.unit := funext fun _ => Subsingleton.elim (α := PUnit) _ _
      have hfR : fR = fun _ => PUnit.unit := funext fun _ => Subsingleton.elim (α := PUnit) _ _
      subst hfO; subst hfR; rfl

/-! ## T17 — the Mirror -/

/-- Spec 2-03 T17 — THE MIRROR. The constructed universe is a single point: T1
firing on our own construction. The signature of 2-01 §2 — relations individuated by
bare endpoints, no grading anywhere in the functor — is the boolean shadow in
two-sorted clothing, and the framework's first theorem enforced itself against the
framework's authors. The construction (Spec201c) is CORRECT; what it constructs is
the One. ω̂ is not Ω's first citizen; it is its only citizen. Derived structure
(contexts, apertures, dyads) is bisimilarity-invariant and cannot individuate — the
D4 corollary, returning. The many require loss in the functor (2-03 D21). This is the
hostile-first culture working exactly as designed: the formalization fought back and
won. Route A (canonicity): `final_unique` composed with `Subsingleton PUnit`. -/
theorem omega_collapse : ∀ x y : Ω₀, x = y := by
  obtain ⟨f, g, hgf, -⟩ := final_unique ZΩ unitRaw isFinalBRaw_ZΩ isFinalBRaw_unitRaw
  intro x y
  have hx : (Hom.compRaw g f).fO x = x := by rw [hgf]; rfl
  have hy : (Hom.compRaw g f).fO y = y := by rw [hgf]; rfl
  calc x = (Hom.compRaw g f).fO x := hx.symm
    _ = g.fO (f.fO x) := rfl
    _ = g.fO (f.fO y) := by rw [Subsingleton.elim (α := PUnit) (f.fO x) (f.fO y)]
    _ = (Hom.compRaw g f).fO y := rfl
    _ = y := hy

/-- ω̂'s corrected gloss, as a corollary with its own name: the only citizen. -/
theorem omegaHat_only : ∀ x : Ω₀, x = omegaHat := fun x => omega_collapse x omegaHat

/-- The collapsed universe's relation sort is a subsingleton too. -/
instance : Subsingleton (Sym2 Ω₀) := ⟨by
  intro a b
  induction a using Sym2.ind with | _ a1 a2 =>
  induction b using Sym2.ind with | _ b1 b2 =>
  rw [omega_collapse a1 b1, omega_collapse a2 b2]⟩

/-! ## T18 — the Coincidence of Extremes -/

/-- The collapsed universe as a Model: coherence holds because everything is
everything (subsingleton membership); `dy` is the only choice available. -/
noncomputable def ZΩModel : Model where
  O := Ω₀
  R := Sym2 Ω₀
  endpoints := id
  pat := ZΩ.pat
  pat_nonempty := ZΩ.pat_nonempty
  coherent := by
    intro r x _
    obtain ⟨r', hr'⟩ := ZΩ.pat_nonempty x
    rwa [Subsingleton.elim (α := Sym2 Ω₀) r r']
  dy _ := omegaHat

/-- Spec 2-03 T18 — THE COINCIDENCE OF EXTREMES. In the collapsed universe the four
extremes the framework forbids are provably one point: ω̂ is Total (its pattern is
everything), Windowless (Internal = pat), and its self-relation is SelfAnchored with
saturating aperture (ctx = pat — the `reflexive_saturation` configuration, whose
witness model was this universe all along). T16, C1, S0, and A1 are four faces of a
single exclusion: the One cannot live among the many. The exclusion zone of the entire
framework is a point — and this project constructed it. (C1's conditional stands
consistent: its no-total hypothesis fails exactly here, as it should.) -/
theorem extremes_coincide :
    Total ZΩModel omegaHat ∧
    Windowless ZΩModel omegaHat ∧
    ∃ r ∈ ZΩModel.pat omegaHat,
      SelfAnchored ZΩModel r ∧ ctx ZΩModel omegaHat r = ZΩModel.pat omegaHat := by
  refine ⟨?total, ?windowless, ?rel⟩
  case total =>
    show ZΩModel.pat omegaHat = Set.univ
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨r0, hr0⟩ := ZΩ.pat_nonempty omegaHat
    rwa [Subsingleton.elim (α := Sym2 Ω₀) p r0]
  case windowless =>
    show Internal ZΩModel omegaHat = ZΩModel.pat omegaHat
    apply Set.eq_of_subset_of_subset (internal_subset _ _)
    intro r hr
    refine ⟨hr, fun z _ => ?_⟩
    have hz : z = omegaHat := omega_collapse z omegaHat
    subst hz
    exact subset_rfl
  case rel =>
    obtain ⟨r0, hr0⟩ := ZΩ.pat_nonempty omegaHat
    refine ⟨r0, hr0, ?_, ?_⟩
    · -- SelfAnchored: omegaHat (the only object) is an endpoint of r0
      obtain ⟨w, hw⟩ := sym2_hasMem r0
      rw [omega_collapse w omegaHat] at hw
      exact hw
    · apply Set.eq_of_subset_of_subset (ctx_subset _ _ _)
      intro s hs
      refine ⟨hs, ?_⟩
      obtain ⟨w, hw⟩ := sym2_hasMem s
      rw [omega_collapse w omegaHat] at hw
      exact hw

/-! ## HON — the honesty lemmas -/

/-- HONESTY LEMMA. `EqDepth` is trivially total over the collapsed universe — the
density surrogate currently has no content. Template survives; content awaits the
corrected Ω. -/
theorem eqDepth_trivial : ∀ (n : ℕ) (x y : Ω₀), EqDepth n x y := by
  intro n x y
  rw [omega_collapse x y]
  exact eqDepth_refl n y

/-- HONESTY LEMMA (Spec 2-03 §1). Genesis is VACUOUSLY TRUE over the collapsed
universe — everything is depth-matched by ω̂'s orbit because everything IS ω̂. This is
not a resolution of T10; it is the reason T10 must be re-anchored against the corrected
Ω (2-03 §5). Kept in the file so no later reader mistakes the anchor for the answer. -/
theorem genesis_vacuous : Genesis :=
  fun x n => ⟨omegaHat, omegaHat_mem_omegaOrbit, eqDepth_trivial n x omegaHat⟩

end TwoSorted
end RelEx

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms G_unit_subsingleton
#print axioms isFinalBRaw_unitRaw
#print axioms omega_collapse
#print axioms omegaHat_only
#print axioms extremes_coincide
#print axioms eqDepth_trivial
#print axioms genesis_vacuous
end AxiomAudit

/-
-- Specs 2-00 / 2-03 ↔ scratch/formal/Spec203.lean
-- DIAG (F(1))          = RelEx.TwoSorted.G_unit_subsingleton
-- UNIT                 = RelEx.TwoSorted.unitRaw, isFinalBRaw_unitRaw
-- T17 (The Mirror)     = RelEx.TwoSorted.omega_collapse (Route A: final_unique), omegaHat_only
-- T18 (Coincidence)    = RelEx.TwoSorted.ZΩModel, extremes_coincide
-- HON                  = RelEx.TwoSorted.eqDepth_trivial, genesis_vacuous
--
-- T17 route shipped: Route A (canonicity — `final_unique ZΩ unitRaw`, then Subsingleton PUnit).
--
-- Deviations from 2-03-mechanization-a.md:
--   * Registered as an eighth Lake library root (`Spec203`).
--   * Added `import Spec202` (beyond the work order's Spec201/b/c/d list): T18 uses
--     `Total`/`Windowless`/`Internal`/`internal_subset`, which live in Spec202.
-/
