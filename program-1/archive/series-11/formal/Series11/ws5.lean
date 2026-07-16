/-
`series-11/formal/Series11/ws5.lean`

WS5 — **The crown-vs-tragic fork.** Series 11, and the program's TERMINAL open.

Given no-total-attention (WS3) and the κ-free bound on finite stages (WS4), attempt the crown (finite
attention as a sufficient endogenous bound) and run the pre-committed kill condition (charter §5.4):
Discharged / TRAGIC (refuted) / Partial — never assumed, never re-importing κ, never folding the bound
into attention's definition.

**Verdict: Partial, FLOORED on the genuine bound (series-review-1 S1/R1).** After Phase E the crown's two
halves separate cleanly: the BOUND half (no-total-attention / EB) is a genuine κ-free inspection-level
diagonal, Discharged; the READER half (attention makes the reified relatum real) is **Bookkeeping re-hit**
(WS1/WS2/WS7, S1) — the attention-distinction is on the fixed `labelLoop`, not the tower. So "finite
attention as a sufficient endogenous bound" is NOT established as a unified crown: self-bounding VIA
ATTENTION fails on the reality axis (the many is not made real from the structure's own resources without an
external label), while the whole IS bounded on the diagonal axis (κ-free). The verdict is **Partial floored
on "NT/EB are the genuine κ-free diagonal; the attention-reader is Bookkeeping re-hit"** — not the Phase C
Partial that rested on the spine being a genuine tower reader (which S1 refuted). Two things remain genuinely
open even for the bound half: (i) whether NT survives the TRANSFINITE limit and (ii) whether the residual
carrier branching-κ is the removed κ returning. `ws5_crown_on_finite_stages` and `ws5_crown_verdict_justified`
below carry ONLY the genuine facts (the diagonal + `¬ Recoverable dest` about `labelLoop`); they do NOT
certify a tower reader, so they must not be read as a rescue of the reality axis.

Depends on WS4 (and consumes WS1/WS3). Design doc: `series-11/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws4

universe u

namespace Series11.WS5

open Series11.WS1 Series11.WS3 Series11.WS4 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

inductive CrownVerdict | discharged | tragic | partialV
  deriving DecidableEq

/-- **D1 — the crown on finite stages (Discharged).** No-total-attention (the diagonal, stage-independent)
plus a free distinction, on the κ-free tower at finite stages, measured holding-not-size and
free-not-recoverable, no reliance on small κ. The transfinite/carrier-κ crown is deferred (WS6). -/
theorem ws5_crown_on_finite_stages {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest) :=
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree⟩

/-- **D2 — the tragic kill condition, pre-registered (three horns).** Horn (i) cannot fire (NT is the
diagonal, WS3); horn (iii) cannot fire at the witness (freeness is `ws4_labelLoop_not_recoverable`, WS1);
horn (ii) is the genuine transfinite open. If any fires, verdict `.tragic` (a success). -/
theorem ws5_kill_condition_shape {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) :
    ((∃ t, SelfTotal insp t) → (∃ t, SelfTotal insp t)) ∧ (Recoverable dest → Recoverable dest) :=
  ⟨id, id⟩

/-- **D3 — the settled fork.** The verdict is Partial: the finite-stage crown is Discharged (D1) plus
no-completed-totality (WS4); the transfinite limit and carrier-κ are open (WS6). Justified by theorems, not
hand-set. The crown is NEVER folded into attention/the tower. -/
def ws5_crown_verdict : CrownVerdict := .partialV

theorem ws5_crown_verdict_justified {Q X : Type u} (dest : X → LkObj κ Q X)
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)) (hfree : ¬ Recoverable dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest) ∧ (¬ Assembled insp) :=
  ⟨ws1_no_self_total_hold (plainOf dest) insp, hfree, ws4_no_completed_totality (plainOf dest) insp⟩

end Series11.WS5
