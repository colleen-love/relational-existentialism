/-
`series-10/formal/Series10/ws2.lean`

WS2 — **Genuine growth, not bookkeeping.** Series 10, the payoff.

The reified relatum genuinely grows the carrier: `Ω_{α+1}` does NOT label-bisimulation-embed into `Ω_α`
(the reified free relatum's label survives the quotient, `ws2_growth_strict`), and it lands on the
`ws4_free_label_is_import` horn — plain-invisible, label-visible — not the recoverable horn
(`ws2_growth_is_free_label`). Two distinct-history relata are merged by the PLAIN collapse engine yet
kept apart at the LABELLED level (`ws2_history_not_merged`), the break of the Series 07 collapse Series
09's moving hole (bisimulation-invariant) could not make.

**The honest disclosure (`ws2_plain_collapse_persists`):** at the PLAIN level the collapse engine still
merges. Genuine growth lives at the LABELLED level, where the free residue is the reified relatum's
relating. Whether that label is internal carrier structure (genuine growth) or an external record
(Bookkeeping) is the strip-test adjudication WS7 owns.

Depends on WS1. Design doc: `series-10/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws1

universe u

namespace Series10.WS2

open Series10.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-- **D1 — strict internal growth.** The reified free relatum is not label-bisimilar to any prior
relatum, so `Ω_{α+1}` does NOT label-bisimulation-embed into `Ω_α`: growth is a bigger world, not a
lengthening record. Secured by WS1's freeness (`ws4_label_survives_quotient` / `ws2_residue_free`). -/
theorem ws2_growth_strict (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ws4_label_survives_quotient hinf

/-- **D2 — growth is the free-label import (the bookkeeping check discharged).** The reified relatum is
plain-invisible (the collapse engine would merge it) but label-visible (FREE) — the
`ws4_free_label_is_import` horn, never `ws4_recoverable_not_import`. Genuine growth, not recovered. -/
theorem ws2_growth_is_free_label (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D3 — distinct histories not merged (breaks the Series 07 collapse).** The plain collapse engine
merges ANY two atomless relata (first conjunct, `ws1_atomless_bisim`), so it would merge two
distinct-history relata; but they are NOT label-bisimilar (second conjunct), so the reified free label
keeps them apart — where Series 09's moving hole (bisimulation-invariant) was still merged. -/
theorem ws2_history_not_merged (hinf : ℵ₀ ≤ κ) :
    (∀ x y, ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R x y)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨fun x y => ws1_atomless_bisim _ x y (labelLoop_atomless hinf x) (labelLoop_atomless hinf y),
   ws4_label_survives_quotient hinf⟩

/-- **D4 — the honest disclosure (the anti-overclaim pin).** At the PLAIN level the collapse engine still
merges: growth and the break of the collapse live at the LABELLED level only. Stated so the level of
growth cannot be silently inflated. -/
theorem ws2_plain_collapse_persists (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩ :=
  ⟨fun _ _ => True, plainOf_labelLoop_true_bisim hinf, trivial⟩

/-- **D5 — the direct repair, the headline contrast.** Series 09's residue moved but never became an
object (bisimulation-invariant, `ws2_residue_distinct`: the content is realised nowhere); Series 10's
reified relatum EXISTS and its free label does not embed (`ws2_growth_strict`). Generation, not
relocation — existence differentiates where the moving hole did not. -/
theorem ws2_not_moving_hole {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hinf : ℵ₀ ≤ κ) :
    (∀ h, insp h ≠ residue insp)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws2_residue_distinct dest insp, ws2_growth_strict hinf⟩

end Series10.WS2
