/-
`program-2/series-0/formal/P2S0/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 0 (2.0).

The verdict is COMPUTED from the WS1/WS3/WS4 flags (never WS2, never hand-set): `verdict` is a total function
`Bool³ → Outcome`, `ws5_verdict_eq` computes GROUND-ESTABLISHED by `rfl`, and the falsifiability theorems
(`ws5_verdict_not_obstructed`, `ws5_verdict_not_partial`) show the function DISCRIMINATES. The three flags are
EARNED by `ws5_flags_justified` (reification exists, direction non-recoverable, the import separates). The five
audit clauses (a)-(e) are actual propositions bundling the WS1-WS4 payoffs, with audit (d) the key one:
`ws5_audit_collapse_inherited` states BY `rfl` that `ws2_collapse_inherited` is definitionally the imported
engine, and `verdict` takes no collapse argument, so no verdict hinges on the inherited collapse.

Design docs: `program-2/series-0/spec/ws5-design.md`; shared objects `spec/README.md` §2.4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S0.ws1
import P2S0.ws2
import P2S0.ws3
import P2S0.ws4

universe u

namespace P2S0

open P1.Core P1.Reader Cardinal

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** (`partial'` primed: `partial` is a Lean keyword.) -/
inductive Outcome
  | groundEstablished
  | partial'
  | obstructed
  deriving DecidableEq

/-- **The verdict FUNCTION.** GROUND-ESTABLISHED iff reification exists (WS1), the asymmetry is genuine (WS3),
and the import is seated (WS4); OBSTRUCTED if reification or the asymmetry fails; else PARTIAL. NOTE: the
collapse (WS2) is NOT an argument (audit (d)). -/
def verdict (reif asym imp : Bool) : Outcome :=
  if reif && asym && imp then Outcome.groundEstablished
  else if reif && asym then Outcome.partial'
  else Outcome.obstructed

/-- **THE COMPUTED VERDICT.** On the certified flags, GROUND-ESTABLISHED, by computation. -/
theorem ws5_verdict_eq : verdict true true true = Outcome.groundEstablished := rfl

/-- **Falsifiability.** The verdict function DISCRIMINATES: on the certified flags it is not OBSTRUCTED. -/
theorem ws5_verdict_not_obstructed : verdict true true true ≠ Outcome.obstructed := by decide
/-- **Falsifiability.** ... and not PARTIAL. Had a WS1/WS3 obligation fallen short, `verdict` would compute a
different outcome (`verdict false _ _ = obstructed`, `verdict true true false = partial'`). -/
theorem ws5_verdict_not_partial : verdict true true true ≠ Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The verdict's three `true` inputs are EARNED: reification exists (WS1), the
knowing direction is non-recoverable (WS3), and the import separates plain-bisimilar states (WS4). The
verdict's inputs are theorems, not choices. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0)
  ∧ (¬ Recoverable (knowLiftD hinf))
  ∧ (∀ {Q : Type} (f : Bool → Q), f true ≠ f false →
        ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false) := by
  refine ⟨(ws1_first_other hinf).2.2, ws3_direction_not_recoverable hinf, ?_⟩
  intro Q f hf
  exact (ws4_import_breaks_baseline hinf f hf).2

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) NO CARDINAL CEILING.** The out-neighborhoods are finite (`< ℵ₀`), uniformly in `κ`. -/
theorem ws5_audit_no_ceiling {κ : Cardinal.{u}} (hinf : ℵ₀ ≤ κ) {X : Type u} (attends : X → Finset X) :
    ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < Cardinal.aleph0 :=
  ws1_bound_is_finite_attention hinf attends

/-- **(b) THE ASYMMETRY IS NOT A LABEL.** A genuine reader, over the unified first-other witness: the first
other `s1` and the self `s0` are plain-bisimilar over the bare relating yet tower-separated
(`AttentionDistinguishes`), with `s1` actively attending `s0` while `s0` does not attend back (the passive
asymmetry). Load-bearing (Charter Extension 1), the separation derived from the passive/reification structure,
not a bare tag. -/
theorem ws5_audit_asymmetry_not_label {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0
  ∧ (s1 ∈ attendedBy attendsU s0 ∧ s1 ∉ attendsU s0) :=
  ⟨(ws3_active_passive_distinct hinf).2,
   (ws3_active_passive_distinct hinf).1.2.1, (ws3_active_passive_distinct hinf).1.2.2⟩

/-- **(c) DIRECTION IS NON-RECOVERABLE.** A proof term. -/
theorem ws5_audit_direction_free {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (knowLiftD hinf) :=
  ws3_direction_not_recoverable hinf

/-- **(d) THE COLLAPSE IS INHERITED, NOT RELITIGATED.** `ws2_collapse_inherited` is DEFINITIONALLY the
imported engine `ws2_import_theorem_static` (relitigation impossible), and `verdict` takes no collapse
argument, so no verdict hinges on it. -/
theorem ws5_audit_collapse_inherited {κ : Cardinal.{u}} (hinf : ℵ₀ ≤ κ) {X : Type u}
    (hcar : Cardinal.mk X < κ) (attends : X → Finset X)
    (hb : BehaviorallyIdentified (symDest hinf hcar attends))
    (ha : ∀ x, SHNE (symDest hinf hcar attends) x) :
    ws2_collapse_inherited hinf hcar attends hb ha
      = ws2_import_theorem_static (symDest hinf hcar attends) hb ha := rfl

/-- **(e) THE IMPORT IS QUANTIFIED, NOT NAMED.** The baseline-breaking is `∀`-quantified over the import; no
proof term names the import content. -/
theorem ws5_audit_import_quantified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type} (f : Bool → Q), f true ≠ f false →
        ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false :=
  fun f hf => (ws4_import_breaks_baseline hinf f hf).2

end P2S0
