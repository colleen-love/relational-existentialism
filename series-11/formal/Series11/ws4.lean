/-
`series-11/formal/Series11/ws4.lean`

WS4 — **The endogenous bound, κ removed.** Series 11, the structural heart.

With κ removed, no-total-attention (WS3) plus bounded-holding means no completed totality is ever formed
(no self-total hold), so the carrier does not Russell-explode despite being unboundedly many. The bound is
HOLDING-NOT-SIZE (`ws4_bound_is_holding_not_size`) — the guard against κ readmitted (charter §4.4). The
κ-free bound is Discharged; the transfinite limit is handed to WS5.

**Honest scope (protocol §0.5; series-review-1 R1).** The bound is `¬ ∃ t, SelfTotal insp t` (holding),
refutable by a total attention, holding even on an infinite carrier (`Infinite X`) — no cardinality
ceiling. The diagonal references no cardinal (`ws4_kappa_free`), the genuine κ-removal. The residual carrier
branching-κ (in `PkObj κ`, the section `reify`'s existence condition) is disclosed as scaffolding, NOT a
proliferation or holding bound; whether it counts as κ readmitted is the WS5/WS7 verdict. **R1 correction:**
EB is an INSPECTION-LEVEL diagonal fact — `Assembled insp := ∃ t, SelfTotal insp t` is about `insp`, and
`ws4_bound_finite_stages` takes `reify`/`Ω₀`/`n` and DISCARDS them. So this is a bound on self-inspection
(tower-independent, κ-free), not a proved bound on the `reifyStep`-tower; the "tower never assembles" /
"finite stages" reading is interpretive, carried in Series 10 Phase E's honest inspection-level wording.

Depends on WS3. Design doc: `series-11/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws3

universe u

namespace Series11.WS4

open Series11.WS1 Series11.WS3 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **D0 — assembly = self-total hold (the pin).** The tower is ASSEMBLED iff some hold is the totality of
relata below it — a completed self-inspection. Pinned so no-assembly routes through the diagonal. -/
def Assembled {X : Type u} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ t, SelfTotal insp t

/-- **D1 — (EB) no completed totality (the bound).** The tower never assembles into a completed totality:
assembly would be a self-total hold, which no-total-attention forbids. -/
theorem ws4_no_completed_totality {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ Assembled insp :=
  ws3_no_total_attention dest insp

/-- **D2 — the bound is HOLDING-NOT-SIZE (the κ-readmitted guard, the flagship).** No-assembly is a fact
about HOLDING (no self-total hold), refutable by a total attention — NOT a fact about SIZE: it holds for
every κ and even when the tower is infinite. -/
theorem ws4_bound_is_holding_not_size {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ Assembled insp) ∧ (Assembled insp → ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ Assembled insp) :=
  ⟨ws3_no_total_attention dest insp, fun h => h, fun _ => ws3_no_total_attention dest insp⟩

/-- **D3 — no Russell blowup.** An UNRESTRICTED carrier (a hold ranging over ALL contents) is inconsistent,
but the attention-bounded tower is NOT: no hold is total, so no surjective inspection, so the tower is
consistent DESPITE being unboundedly many. The bound is what keeps it from Russell — the incompletability,
not a ceiling. -/
theorem ws4_no_russell_blowup {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ ins : Hold dest → HoldPred dest, Function.Surjective ins) ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨ws1_unrestricted_carrier_inconsistent dest, ws1_no_self_total_hold dest insp⟩

/-- **D4 — the bound is κ-free (the genuine removal).** No-total-hold references no cardinal: it holds for
every carrier and every κ. The residual carrier branching-κ is the section's existence condition,
disclosed, NOT a bound (§2.7). -/
theorem ws4_kappa_free {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  (ws1_diagonal_not_bisim dest insp).2

/-- **D5 — no self-total hold, uniformly (transfinite → WS5).** The no-self-total-hold fact is stage- and
tower-INDEPENDENT: the `reify`/`Ω₀`/`n` arguments are taken and DISCARDED, the proof is the diagonal over
`insp`. So this is the inspection-level bound stated per-stage as an interpretive gloss (R1); the genuine
transfinite/tower claim is WS5's, not established here. -/
theorem ws4_bound_finite_stages {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (n : ℕ) : ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp

end Series11.WS4
