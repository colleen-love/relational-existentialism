/-
`program-2/series-2/formal/P2S2/ws3.lean`

WS3 - The four readings, asymmetric and partial (the facing). Program 2 Series 2 (2.2).

The four readings (self of self, self of other, other of self, other of other) are typed as the directed knowing
`faces` and all witnessed (`ws3_four_readings`). The facing is ASYMMETRIC: the reading-DIRECTION lift `faceLift`
(each edge tagged with whether the reading goes strictly UP the constitution tower) has the symmetric relating as
its plain reduct and is `¬ Recoverable` (`ws3_facing_asymmetric`) — the self reads UP (to the higher other) while
the other has NO upward reading, so the up/down direction is non-recoverable from the symmetric relating, the S0
`ws3_direction_not_recoverable` mechanism with the label the reading-direction (distinct from WS2's source rank).
The facing is PARTIAL: no perspective totalizes itself, the imported diagonal `ws1_no_self_total_hold` at each
perspective's genuine self-reading (`ws3_facing_partial`; the diagonal conjunct is DISCLOSED as the
structure-independent companion, load-bearing paired with the witnessed self-loops). The readings are TYPED but
never EVALUATED.

Design docs: `program-2/series-2/spec/ws3-design.md`; shared objects `spec/README.md` §1-§4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S2.ws2

universe u

namespace P2S2

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The four readings (typed, all witnessed) -/

/-- **A READING**: `x` reads `y` iff `x` actively attends `y` (S0's directed `knows`). The four readings are the
four ordered pairs among the two loci; typed as a `Prop` over the attentions, never a selected/evaluated content. -/
def faces (x y : RCar) : Prop := y ∈ attendsR x

/-- **THE FOUR READINGS ARE ALL GENUINE (typed, not evaluated).** Self of self, self of other, other of self,
other of other all hold on the witness: the mutual, four-reading structure. -/
theorem ws3_four_readings :
    faces slf slf ∧ faces slf oth ∧ faces oth slf ∧ faces oth oth := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · unfold faces; decide

variable {κ : Cardinal.{0}}

/-! ## The direction lift (`faceLift`, the asymmetry engine) -/

/-- **THE READING-DIRECTION LIFT.** Each edge `(x,y)` is tagged with whether the reading is strictly UPWARD the
constitution tower (`rankR x < rankR y`). The plain reduct forgets the direction bit (the symmetric relating);
the self's upward edge to the higher other has no match at the other, which reads only down and flat. Distinct
from `rankLift`'s source-rank label: the tag depends on BOTH source and target (the direction). -/
noncomputable def faceLift (hinf : ℵ₀ ≤ κ) : RCar → LkObj κ (ULift.{0} Bool) RCar :=
  fun x => PkMap κ (fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) (outDest hinf attendsR x)

lemma faceLift_val (hinf : ℵ₀ ≤ κ) (x : RCar) :
    (faceLift hinf x).1
      = (fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) '' (↑(attendsR x) : Set RCar) := rfl

/-- **The symmetric relating forgets the direction.** `plainOf (faceLift hinf) = outDest hinf attendsR`. -/
lemma plainOf_faceLift (hinf : ℵ₀ ≤ κ) : plainOf (faceLift hinf) = outDest hinf attendsR := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) '' (outDest hinf attendsR x).1)
      = (outDest hinf attendsR x).1
  rw [Set.image_image]; simp

/-- **THE DIRECTION SEPARATES THE SELF FROM THE OTHER.** No label-bisimulation over `faceLift` relates `slf` and
`oth`: `slf`'s upward edge to `oth` (tag `true`, `rankR slf < rankR oth`) has no match at `oth`, whose every edge
is down or flat (tag `false`). The `firstOther_label_sep` argument on the reading-direction. -/
lemma face_label_sep (hinf : ℵ₀ ≤ κ) : ¬ ∃ R, IsBisimL (faceLift hinf) R ∧ R slf oth := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR slf oth hRel
  have hedge : ((⟨decide (rankR slf < rankR oth)⟩ : ULift.{0} Bool), oth) ∈ (faceLift hinf slf).1 := by
    rw [faceLift_val]
    exact ⟨oth, by show oth ∈ (↑(attendsR slf) : Set RCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [faceLift_val] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hwmem : w ∈ attendsR oth := Finset.mem_coe.mp hw
  rw [attendsR_oth] at hwmem
  fin_cases hwmem <;> revert hfst <;> decide

/-! ## The payoffs -/

/-- **THE FACING IS ASYMMETRIC (audit (c)).** The self reads the other and the other reads the self (both
directed readings witnessed); the self reads UP the constitution tower (an edge strictly raising `rankR`), the
other has NO upward reading; and the reading-direction lift `faceLift` is `¬ Recoverable` from the symmetric
relating. Knowing is directed: the up/down direction of a reading is not recoverable from the symmetric relating
that forgets it (the S0 `ws3_direction_not_recoverable` mechanism, the label the reading-direction). Distinct
from WS2's twoness (source rank): this separates the DIRECTION of the reading (source-vs-target rank). -/
theorem ws3_facing_asymmetric (hinf : ℵ₀ ≤ κ) :
    (oth ∈ attendsR slf ∧ slf ∈ attendsR oth)
  ∧ (∃ z ∈ attendsR slf, rankR slf < rankR z)
  ∧ (¬ ∃ z ∈ attendsR oth, rankR oth < rankR z)
  ∧ ¬ Recoverable (faceLift hinf) := by
  refine ⟨⟨by decide, by decide⟩, ⟨oth, by decide, by decide⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hlt⟩
    rw [attendsR_oth] at hz
    fin_cases hz <;> revert hlt <;> decide
  · intro hrec
    have hs : SHNE (plainOf (faceLift hinf)) slf := by rw [plainOf_faceLift]; exact ws1_rcar_SHNE hinf slf
    have ho : SHNE (plainOf (faceLift hinf)) oth := by rw [plainOf_faceLift]; exact ws1_rcar_SHNE hinf oth
    obtain ⟨R, hR, hab⟩ := ws1_atomless_bisim (plainOf (faceLift hinf)) slf oth hs ho
    exact face_label_sep hinf ⟨R, hrec R hR, hab⟩

/-- **THE FACING IS PARTIAL (audit, the diagonal).** Both perspectives have genuine self-readings (`slf ∈
attendsR slf`, `oth ∈ attendsR oth`, the self-of-self and other-of-other readings), and no inspection is
self-total (the imported diagonal `ws1_no_self_total_hold`): each self-reading leaves the diagonal residue.
DISCLOSED (charter §0.3): the diagonal conjunct is the SAME structure-independent fact for every inspection,
load-bearing here PAIRED with the witnessed self-readings — the charter's WS3-partial ("under inspection no
self-total hold, by the diagonal"). The PR1-S1 tautology concern is WS4's burden (the MUTUAL residue), not
WS3's. -/
theorem ws3_facing_partial (hinf : ℵ₀ ≤ κ) :
    (slf ∈ attendsR slf ∧ oth ∈ attendsR oth)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t) :=
  ⟨⟨by decide, by decide⟩, fun insp => ws1_no_self_total_hold (outDest hinf attendsR) insp⟩

end P2S2
