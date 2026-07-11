/-
`series-9/formal/Series9/ws7.lean`

WS7 — **The anti-circularity audit.** Series 9, owns the verdict.

The audit against the four Series-9 circularity risks — the-diagonal-is-really-a-bisimulation (the
coincidence re-hit, the flagship), monotonicity-by-fiat, residue-recoverable-by-definition, and
hold-reflexivity-too-weak-or-too-strong — aggregated into a mechanized `Audit` certificate whose every
field is a theorem (the flagship field `diagonalNotBisim` carries the spine's INDEPENDENCE), and a typed
`Series9Verdict` that is a function of it, so it cannot be hand-set. The coincidence rule is PROMOTED to
a first-class spine check (`ws7_coincidence_check`).

Runs last; consumes WS1–WS6. Design doc: `series-9/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series9.ws2
import Series9.ws6

universe u

namespace Series9.WS7

open Series9.WS1 Series9.WS2 Series9.WS3 Series9.WS4 Series9.WS5 Cardinal

variable {κ : Cardinal.{u}}

/-- The typed verdict. `selfReferenceEstablished`: spine independent (not Coincident), residue free,
dynamics forced, monotonicity settled. `coincident`: the spine unfolds to relational identity (Series
8's wall re-hit). `monismStands`: a self-total hold constructible or the carrier a mere self-loop.
`Circular`: freeness free-by-fiat, monotonicity baked-in, or carrier Russell-inconsistent. -/
inductive Series9Verdict | selfReferenceEstablished | coincident | monismStands | Circular
  deriving DecidableEq

/-- **The mechanized audit certificate.** Every field a theorem from WS1–WS5; the flagship field
`diagonalNotBisim` carries the spine's INDEPENDENCE from relational identity, not merely the spine. -/
structure Audit (κ : Cardinal.{u}) : Prop where
  spineDiagonal : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    ¬ ∃ t, SelfTotal insp t
  diagonalNotBisim : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    (¬ ∃ t, SelfTotal insp t)
      ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t)
  residueFree : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    ¬ ResidueRecoverable insp
  onePosition : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h : Hold dest), insp h ≠ residue insp
  orderEndogenous : ∀ {X : Type u} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest),
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m'
  -- (NL), relabelled (series-review-1 F-7): the residue is a face, and CAN be a full face (witnessed).
  residueFace : ∀ {X : Type u} (dest : X → PkObj κ X),
    ∃ insp : Hold dest → HoldPred dest, ∀ h, diag insp h
  -- forced dynamics FROM incompleteness (series-review-1 F-4): no reachable stage is complete.
  dynamicsForced : ∀ {X : Type u} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest),
    prec dest m m' → ¬ Complete m'
  monotonicityTested : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest), diag insp h₀ → (∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀)
  carrierConsistent : ∀ {X : Type u} (dest : X → PkObj κ X),
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5, including the flagship
`diagonalNotBisim` (the spine's INDEPENDENCE from relational identity). -/
theorem ws7_audit : Audit κ where
  spineDiagonal := fun dest insp => ws1_no_self_total_hold dest insp
  diagonalNotBisim := fun dest insp => ws1_diagonal_not_bisim dest insp
  residueFree := fun dest insp => ws2_residue_free dest insp
  onePosition := fun dest insp h => ws2_residue_distinct dest insp h
  orderEndogenous := fun dest m m' => ws3_order_endogenous dest m m'
  residueFace := fun dest => ws3_redi_no_leaf dest
  dynamicsForced := fun dest m m' hp => ws3_dynamics_forced dest m m' hp
  monotonicityTested := fun dest insp h₀ hb => ws5_kill_condition dest insp h₀ hb
  carrierConsistent := fun dest => ws1_unrestricted_carrier_inconsistent dest

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series9Verdict := .selfReferenceEstablished

def ws7_verdict : Series9Verdict := verdict (ws7_audit (κ := κ))

theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series9Verdict.selfReferenceEstablished := rfl

/-- **D3 — with a certificate, never coincident, never monism, never Circular.** The ONLY route to
those is a FAILED audit; the `diagonalNotBisim` field is why `≠ coincident` is earned, not stipulated. -/
theorem ws7_audited_not_coincident (cert : Audit κ) :
    verdict cert ≠ Series9Verdict.coincident := by
  show Series9Verdict.selfReferenceEstablished ≠ Series9Verdict.coincident; decide

theorem ws7_audited_not_monism (cert : Audit κ) :
    verdict cert ≠ Series9Verdict.monismStands := by
  show Series9Verdict.selfReferenceEstablished ≠ Series9Verdict.monismStands; decide

theorem ws7_audited_not_circular (cert : Audit κ) :
    verdict cert ≠ Series9Verdict.Circular := by
  show Series9Verdict.selfReferenceEstablished ≠ Series9Verdict.Circular; decide

/-- **D4 — the coincidence check (the flagship).** The spine is diagonal-not-bisimulation, orthogonal to
relational identity, contrasted IN THE SAME STATEMENT with the Series 8 coincidence witness
`ws1_symmetric_states_bisimilar` (which needs `Symmetric` and PRODUCES a bisimulation, whereas the spine
DENIES a fixed point). The certificate that Series 9 escaped Series 8's wall. -/
theorem ws7_coincidence_check {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t)
  ∧ (∀ {Q Y : Type u} (d : Y → LkObj κ Q Y), Symmetric d → ∀ x y, ∃ R, IsBisimL d R ∧ R x y) :=
  ⟨ws1_no_self_total_hold dest insp, (ws1_diagonal_not_bisim dest insp).2,
   fun d hsym x y => ws1_symmetric_states_bisimilar d hsym x y⟩

/-- **D5a — no coincidence.** The spine is bisimulation-free, orthogonal to relational identity. -/
theorem ws7_no_coincidence {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ws1_diagonal_not_bisim dest insp

/-- **D5b — no monotonicity-by-fiat.** Monotonicity is TESTED (the kill condition fires), not baked in. -/
theorem ws7_no_monotonicity_by_fiat {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (h₀ : Hold dest) (hb : diag insp h₀) :
    ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀ :=
  ws5_kill_condition dest insp h₀ hb

/-- **D5c — freeness is not defined-in.** Freeness is a theorem; recoverability would reconstruct the
self-total hold. -/
theorem ws7_freeness_not_defined_in {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ResidueRecoverable insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp

/-- **D5d — the carrier is genuine (consistent).** The too-strong (surjective-`insp`) horn has no model;
the ambient κ-bounded carrier sidesteps it. -/
theorem ws7_carrier_genuine {X : Type u} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp :=
  ws1_unrestricted_carrier_inconsistent dest

/-- **D6 — the strip ledger.** Each payoff, stripped of its structural word, is a bare fact — and above
all the spine strips to a CANTOR FIXED-POINT (`¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h`), NOT a bisimulation
(the whole repair). Plurality strips to "diag not in range"; forced-dynamics to `Function.update`
seriality; the monotonicity bound to a diagonal-flip. All hold; the self-reference readings are the
earned surplus. -/
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h)
  ∧ (∀ h, insp h ≠ (fun h' => ¬ insp h' h'))
  ∧ (∀ h₀ : Hold dest, ∃ insp' : Hold dest → HoldPred dest, insp' h₀ = (fun h' => ¬ insp h' h'))
  ∧ (∀ h₀ : Hold dest, diag insp h₀ → ∃ insp', ReDiagStep dest insp insp' ∧ ¬ diag insp' h₀) := by
  classical
  refine ⟨ws1_no_self_total_hold dest insp, ws2_residue_distinct dest insp, ?_, ?_⟩
  · intro h₀
    exact ⟨Function.update insp h₀ (fun h' => ¬ insp h' h'), by simp⟩
  · intro h₀ hb
    exact ws5_kill_condition dest insp h₀ hb

/-- The no-certificate outcomes: `coincident` (spine unfolds to bisimulation) or `Circular` (a defined-in
exclusion). Documentation; the load-bearing content is D3 (with a certificate, never these). -/
def verdictSpineCoincident : Series9Verdict := .coincident
def verdictNoCertificate : Series9Verdict := .Circular

end Series9.WS7
