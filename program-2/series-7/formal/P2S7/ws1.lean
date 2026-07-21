/-
`program-2/series-7/formal/P2S7/ws1.lean`

WS1 - The measure `Q`, non-trivial (the risky ground). Program 2 Series 7 (2.7), the blocking workstream.

Imports `P2S6` and reaches the recoverability/import test, the rank lift, the collapse engine, and the tick
machinery transitively (`Recoverable`, `plainOf`, `ws4_recoverable_not_import`, `ws1_atomless_bisim`, `rankLift`,
`AttentionDistinguishes`, `outDest`, `finsetToPk`). It fixes the witness carrier `MCar = Fin 4` and DEFINES the
measure of distinction `Q := rankM` (the reification rank, the accumulated import-content), proved NON-TRIVIAL: two
configurations with different `Q`, the difference a genuine import (`AttentionDistinguishes`, the reified relatum
`e1` plain-bisimilar to its base `e0` yet rank-separated). `rankM` is defined STRUCTURALLY, with no reference to its
conservation (WS2) or its diagonal status (WS4); those are proved of the independent measure, so it is not rigged.
This file also proves the general rank-separation `rankM_sep_general` (a `Q`-change over the plain quotient is a
label-import), shared with WS3.

Design docs: `program-2/series-7/spec/ws1-design.md`; shared objects `spec/README.md` §2-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S6

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## The witness carrier `MCar` (spec/README.md §3) -/

/-- The witness carrier: two base relata, a reified relatum, and a higher reified relatum. -/
abbrev MCar : Type := Fin 4

def e0  : MCar := 0   -- a BASE relatum (rank 0)
def e0' : MCar := 1   -- a SECOND base relatum (rank 0): makes rank NON-INJECTIVE
def e1  : MCar := 2   -- a reified relatum (rank 1), = reifyM {e0}  (an actualized tick-product)
def e2  : MCar := 3   -- a reified relatum (rank 2), = reifyM {e1}  (carrying the reified constituent e1)

/-- The plain relating: `e0`, `e0'` self-loop; `e1 → e0`; `e2 → e1`. All four are `SHNE`. -/
def attendsM : MCar → Finset MCar := fun x =>
  if x = e0 then {e0}
  else if x = e0' then {e0'}
  else if x = e1 then {e0}       -- attendsM (reifyM {e0}) = {e0}
  else {e1}                      -- attendsM (reifyM {e1}) = {e1}

/-- **THE MEASURE `Q`.** The reification-tower height: bases at 0, the reified relatum `e1` at 1, the higher
reified relatum `e2` at 2. Defined structurally — no conservation or rise clause; WS2/WS4 are proved of it. -/
def rankM : MCar → ℕ := fun x =>
  if x = e1 then 1 else if x = e2 then 2 else 0

/-- The pointwise reification section: `{e0}` reifies to `e1`, `{e1}` to `e2`; else `e0`. Total `FinReify` is
unsatisfiable on the finite carrier (as in S0/S1), so the section is pointwise. -/
def reifyM : Finset MCar → MCar := fun s =>
  if s = {e0} then e1 else if s = {e1} then e2 else e0

/-- The measure lift: the rank-labelled lift of the plain relating (the label broadcasts the measure). -/
noncomputable def destML {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) : MCar → LkObj κ (ULift.{0} ℕ) MCar :=
  rankLift (outDest hinf attendsM) rankM

/-! ## Carrier lemmas (all reduce by the kernel; `rfl`/`decide`) -/

lemma attendsM_e0  : attendsM e0  = {e0} := rfl
lemma attendsM_e1  : attendsM e1  = {e0} := rfl
lemma attendsM_e2  : attendsM e2  = {e1} := rfl

lemma reifyM_e0 : reifyM {e0} = e1 := rfl
lemma reifyM_e1 : reifyM {e1} = e2 := by decide

/-- The pointwise reification sections at the two used patterns. -/
lemma sectionM_e0 : attendsM (reifyM {e0}) = {e0} := by decide
lemma sectionM_e1 : attendsM (reifyM {e1}) = {e1} := by decide

lemma attendsM_nonempty : ∀ x : MCar, (attendsM x).Nonempty := by decide

variable {κ : Cardinal.{0}}

lemma outDestM_ne_empty (hinf : ℵ₀ ≤ κ) (x : MCar) : (outDest hinf attendsM x).1 ≠ ∅ := by
  show (↑(attendsM x) : Set MCar) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsM_nonempty x))

/-- Every witness node is `SHNE` (all successor sets nonempty), so the collapse engine applies. -/
lemma SHNE_M (hinf : ℵ₀ ≤ κ) (x : MCar) : SHNE (outDest hinf attendsM) x :=
  fun v _ => outDestM_ne_empty hinf v

/-- The general fact `plainOf (rankLift dest lab) = dest` on `MCar` (the label forgets to the bare relating). -/
lemma plainOf_rankLiftM (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- The rank-labelled edge set at `x`. -/
lemma rankLiftM_val (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) (x : MCar) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1 := rfl

/-! ## The general rank-separation (shared with WS3) -/

/-- **THE GENERAL RANK-SEPARATION.** For any plain coalgebra `dest` and label `lab`, two states whose labels
differ and whose source has a non-empty edge set are NOT bisimilar over the rank lift: an outgoing edge of `x`
carries first-coordinate `lab x`, and forward-matching under a label-bisim forces some edge of `y` with the same
first-coordinate, but every edge of `y` carries `lab y`, so `lab x = lab y`, contradiction. The mechanism of
`P1.Reader.ws2_many_general` / `firstOther_label_sep`. A `Q`-change over the plain quotient is a label-import. -/
theorem rankM_sep_general (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) (x y : MCar)
    (hlab : lab x ≠ lab y) (hne : (dest x).1 ≠ ∅) :
    ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR x y hRel
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hedge : ((⟨lab x⟩ : ULift.{0} ℕ), z) ∈ (rankLift dest lab x).1 := by
    rw [rankLiftM_val]; exact ⟨z, hz, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [rankLiftM_val] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have : lab x = lab y := congrArg ULift.down hfst
  exact hlab this

/-! ## The payoff -/

/-- **THE MEASURE IS NON-TRIVIAL (WS1, the risky ground).** `rankM` (the measure `Q`) is not constant
(`rankM e1 = 1 ≠ 0 = rankM e0`), and the value-difference is a GENUINE import: `e1` (a reified relatum) and its
base `e0` are plain-bisimilar (the collapse engine `ws1_atomless_bisim`, both `SHNE`) yet NOT bisimilar over the
measure lift (the rank gap, `rankM_sep_general`): exactly `AttentionDistinguishes`. So a `Q`-difference IS a
`¬ Recoverable` distinction; `Q` measures import-content, and it is not rigged (defined structurally). -/
theorem ws1_rank_nontrivial (hinf : ℵ₀ ≤ κ) :
    rankM e1 ≠ rankM e0
  ∧ AttentionDistinguishes (destML hinf) e1 e0
  ∧ (∃ x y : MCar, rankM x ≠ rankM y) := by
  refine ⟨by decide, ⟨?_, ?_⟩, ⟨e1, e0, by decide⟩⟩
  · show ∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0
    rw [destML, plainOf_rankLiftM]
    exact ws1_atomless_bisim (outDest hinf attendsM) e1 e0 (SHNE_M hinf e1) (SHNE_M hinf e0)
  · show ¬ ∃ R, IsBisimL (destML hinf) R ∧ R e1 e0
    exact rankM_sep_general (outDest hinf attendsM) rankM e1 e0 (by decide) (outDestM_ne_empty hinf e1)

end P2S7
