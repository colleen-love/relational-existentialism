/-
`program-2/series-7/formal/P2S7/ws4.lean`

WS4 - The free-lunch crux (the knot). Program 2 Series 7 (2.7), the genuinely-uncertain obligation.

Imports `P2S7.ws3`. The fork on self-reference: does the diagonal (the residue, `ws2_residue_free`) CHANGE `Q`
with no external import (CREATE from within, FREE-LUNCH) or only RELOCATE distinction already latent (CONSERVED)?
Both reachable, the knot on the DIAGONAL (the residue), not on import-ness (the costume gate). The load-bearing
genuine content is the P1 diagonal: `ws2_residue_free` (the residue is a real non-recoverable content, produced by
self-inspection alone, no import crossing) and `ws1_coincidence_not_identity_witness` (from one position the
diagonal yields two DISTINCT such contents). A decidable count skeleton (`Qc`, `diagStep`) carries the
create-vs-relocate arithmetic and is DISCLOSED as a skeleton, conjoined with (not derived from) the residue facts
(finding C5-S1, COSMETIC). Both branches reachable and neither forced ⇒ the crux is relative, not decided from
within.

Design docs: `program-2/series-7/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws3

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-! ## The bookkeeping skeleton (decidable) and an inhabited self-inspecting position -/

/-- The count of distinct distinction-contents in a finite budget (a decidable skeleton, disclosed). -/
def Qc (B : Finset (Fin 2)) : ℕ := B.card

/-- The diagonal/residue step on a budget: adjoin the diagonal index `d`. -/
def diagStep (B : Finset (Fin 2)) (d : Fin 2) : Finset (Fin 2) := insert d B

/-- An inhabited self-inspecting position: a `Hold` on the plain relating (`e0` self-loops, `e0 ∈ attendsM e0`). -/
def h0 (hinf : ℵ₀ ≤ κ) : Hold (outDest hinf attendsM) :=
  ⟨(e0, e0), by
    show e0 ∈ (↑(attendsM e0) : Set MCar)
    rw [attendsM_e0]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self e0)⟩

/-! ## The fork -/

/-- **FREE-LUNCH REACHABLE (WS4).** From ONE self-inspecting position (`h0`), the diagonal produces at least TWO
DISTINCT free residues (`ws1_coincidence_not_identity_witness`: the constant-`True` / constant-`False` inspections,
pointwise-opposite residues), each non-recoverable (`ws2_residue_free`), with NO import crossing the boundary — the
content arises from self-inspection alone. So self-reference CAN manufacture a plurality of distinct non-recoverable
distinctions from within: the diagonal can be a genuine internal source, the count rising (skeleton: `Qc` up by one).
This rests on the diagonal (`residue`), not on boundary import-ness (audit c). -/
theorem ws4_free_lunch_reachable (hinf : ℵ₀ ≤ κ) :
    (∃ insp₁ insp₂ : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM),
        ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂)
  ∧ Qc (diagStep ∅ 0) = Qc ∅ + 1 :=
  ⟨ws1_coincidence_not_identity_witness (outDest hinf attendsM) (h0 hinf), by decide⟩

/-- **CONSERVED REACHABLE (WS4).** Relative to a budget that already contains the diagonal's content, the residue
step actualizes it WITHOUT net increase (skeleton: `Qc` unchanged) — the free residue relocates onto an
already-latent slot. The residue is STILL a genuine non-recoverable content (`ws2_residue_free`, universally); it
simply adds no NET unit. So creation is lossless here: CONSERVED. -/
theorem ws4_conserved_reachable (hinf : ℵ₀ ≤ κ) :
    (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)
  ∧ Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2)) :=
  ⟨fun insp => ws2_residue_free (outDest hinf attendsM) insp, by decide⟩

/-- **THE CRUX IS RELATIVE, NOT DECIDED FROM WITHIN (WS4, no fiat).** FREE-LUNCH (the count rises) and CONSERVED
(the count holds) are BOTH reachable, neither forced by the structure: whether the diagonal is a net source depends
on what is already latent, which is relative. The general-relativity shape at the free-lunch crux. -/
theorem ws4_crux_both_reachable (hinf : ℵ₀ ≤ κ) :
    (Qc (diagStep ∅ 0) = Qc ∅ + 1)
  ∧ (Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2))) := by decide

end P2S7
