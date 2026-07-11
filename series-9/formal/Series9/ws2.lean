/-
`series-9/formal/Series9/ws2.lean`

WS2 — **The residue breaks the collapse from one position.** Series 9, the payoff.

The diagonal residue `residue insp := diag insp` is distinct from every hold's content and FREE
(not recoverable from the inspection), derived from ONE position with no second position in the
premise — the exact repair of Series 8's circularity (`x↾(x,y) ≠ y↾(y,x)` needed `x ≠ y`). Series 8's
distributed perspective recovers as a special case (mutual residues), not the source.

Depends on WS1 (the diagonal spine and its independence). Design doc: `series-9/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws1

universe u

namespace Series9.WS2

open Series9.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-- The **residue** of an inspection: the diagonal content no hold realises. -/
def residue {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  diag insp

/-- The residue is **recoverable** iff some hold's content realises it (a function of the inspection). -/
def ResidueRecoverable {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ h, insp h = residue insp

/-- **D1 — plurality from one position.** The residue is distinct from every hold's content, with NO
second position in the premise — the repair of Series 8's `x↾(x,y) ≠ y↾(y,x)` needing `x ≠ y`. A hold
whose content is the residue would be self-total, which the diagonal (WS1) forbids. -/
theorem ws2_residue_distinct {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ∀ h, insp h ≠ residue insp := by
  intro h hh
  exact ws1_no_self_total_hold dest insp ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

/-- **D2 — the residue is free (non-circularity core).** Not recoverable from the inspection;
recoverability would reconstruct the self-total hold, which the diagonal (WS1) forbids. -/
theorem ws2_residue_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ResidueRecoverable insp := by
  rintro ⟨h, hh⟩
  exact ws2_residue_distinct dest insp h hh

/-- **D3 — freeness is an import; recoverability ⇒ self-total hold (the semantic-test bind).** The
residue lands on the `ws4_free_label_is_import` horn (free), never `ws4_recoverable_not_import`. -/
theorem ws2_residue_is_import {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) := by
  refine ⟨ws2_residue_free dest insp, ?_⟩
  rintro ⟨h, hh⟩
  exact ⟨h, fun h' => Iff.of_eq (congrFun hh h')⟩

/-- **D4 — from one position, non-circular, tied to the independent spine (the headline).** Plurality
exists (the residue is distinct and free) from ONE inspection, and it is genuine plurality (not the
Series 8 coincidence) BECAUSE the spine is the independent diagonal (WS1's `ws1_no_self_total_hold`,
certified diagonal-not-bisimulation by `ws1_diagonal_not_bisim`). -/
theorem ws2_from_one_position {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (∀ h, insp h ≠ residue insp)
  ∧ (¬ ResidueRecoverable insp)
  ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨ws2_residue_distinct dest insp, ws2_residue_free dest insp,
   ws1_no_self_total_hold dest insp⟩

/-- **D5 — distributed perspective as a special case, scoped honestly.** Series 8's `labelLoop` pair
recovers as two distinct holds each lying in the residue (mutual blind spots): distributed perspective
is a SPECIAL CASE of the residue, not its source. NOT claimed universal (charter §9). -/
theorem ws2_distributed_special_case (hinf : ℵ₀ ≤ κ) :
    ∃ (insp : Hold (plainOf (labelLoop hinf)) → HoldPred (plainOf (labelLoop hinf)))
      (h₁ h₂ : Hold (plainOf (labelLoop hinf))),
        residue insp h₂ ∧ residue insp h₁ ∧ h₁ ≠ h₂ := by
  refine ⟨fun _ => (fun _ => False),
    ⟨(⟨true⟩, ⟨true⟩), ?_⟩, ⟨(⟨false⟩, ⟨false⟩), ?_⟩, ?_, ?_, ?_⟩
  · rw [plainOf_labelLoop_val]; exact rfl
  · rw [plainOf_labelLoop_val]; exact rfl
  · simp [residue, diag]
  · simp [residue, diag]
  · intro he
    have hv : ((⟨true⟩ : ULift.{u} Bool), (⟨true⟩ : ULift.{u} Bool)) = (⟨false⟩, ⟨false⟩) :=
      congrArg Subtype.val he
    exact absurd hv (by decide)

end Series9.WS2
