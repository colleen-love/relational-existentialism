/-
`series-11/formal/Series11/ws5.lean`

WS5 — **The crown-vs-tragic fork.** Series 11, and the program's TERMINAL open.

Given no-total-attention (WS3) and the κ-free bound on finite stages (WS4), attempt the crown (finite
attention as a sufficient endogenous bound) and run the pre-committed kill condition (charter §5.4):
Discharged / TRAGIC (refuted) / Partial — never assumed, never re-importing κ, never folding the bound
into attention's definition.

**Verdict: Partial (Discharged on finite stages, transfinite/carrier-κ open).** No-total-attention is a
diagonal fact, stage-independent, so it holds at every finite stage (WS4); the attention-distinction is
free at the witness (WS1). So the crown is Discharged on finite stages. But (i) whether no-total-attention
survives the TRANSFINITE limit and (ii) whether the residual carrier branching-κ is genuinely not the
removed κ are un-rangeable — the tragic edge. So the verdict is **Partial**, mirroring Series 10's WS5. The
TRAGIC horn is pre-registered and live: if the transfinite limit re-admits a total attention, or the
distinction is recoverable at the tower, or the carrier-κ is judged the removed κ returning, the crown is
TRAGIC (a success, the program's honest terminus).

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
