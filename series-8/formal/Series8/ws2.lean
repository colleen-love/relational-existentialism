/-
`series-8/formal/Series8/ws2.lean`

WS2 — **Perspective breaks the collapse.** Series 8, the payoff.

Two finite holds of a shared relation, taken from opposite sides, fail "relate alike" so the
Series 7 merge does not apply — plurality with no import (vs. weight) and no leaf (vs.
limit-atomlessness), provided the asymmetry is FREE, which WS1 secures. The witnesses are the
transcribed free-label machinery (`Series8.ws1`); WS2 re-reads them as "distinct perspectives
do not merge" and delivers the freeness verdict.

Design doc: `series-8/spec/ws2-design.md`. Depends on WS1 (the global freeness the payoff leans on
is `ws1_no_gods_eye` / `ws1_directed_hold_free`).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series8.ws1

universe u

namespace Series8.WS2

open Series8.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-- **D1 — perspective breaks the merge.** Plain-bisimilar (Series 7 would merge them) yet the
directed holds do not relate alike: the merge fails. -/
theorem ws2_perspective_breaks_merge (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D2 — freeness.** The directed hold is not recoverable — the relating does not carry it. -/
theorem ws2_free_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

/-- **D4 — plurality by distributed perspective.** Plural, atomless (no leaf), non-merging, free. -/
theorem ws2_plurality_by_perspective (hinf : ℵ₀ ≤ κ) :
    ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
  ∧ (∀ i, SHNE (plainOf (labelLoop hinf)) i)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ ¬ Recoverable (labelLoop hinf) :=
  ⟨by decide, labelLoop_atomless hinf, ws4_label_survives_quotient hinf,
   ws4_labelLoop_not_recoverable hinf⟩

/-- **D3 — the freeness verdict (monism-broken).** The code delivers MONISM-BROKEN: the perspective
is free (D2), so it survives (D1); it is NOT the recoverable face that collapses. -/
theorem ws2_monism_broken (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (labelLoop hinf)
  ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws4_labelLoop_not_recoverable hinf, ws4_free_label_is_import hinf⟩

end Series8.WS2
