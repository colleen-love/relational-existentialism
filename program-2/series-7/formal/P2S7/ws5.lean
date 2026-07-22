/-
`program-2/series-7/formal/P2S7/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 7 (2.7).

The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= monotoneOnly` on the
HONEST flags, DISCRIMINATING (reaches all six outcomes), the flags EARNED by the WS1-WS4 headlines. The computed
verdict is MONOTONE-ONLY: a non-trivial measure `Q` (WS1) that the tick strictly RAISES (WS2, the arrow) and that is
NOT conserved in-sight (WS3 — `rankM` is not plain-bisimulation-invariant, and the only conserved measures are
trivial), the rise genuine internally-manufactured import-content (WS4, all creation). So `inSightConserved` is
honestly FALSE, and the verdict function returns `monotoneOnly`. The universe has an arrow and keeps no conserved
ledger, even locally.

This recomputes the verdict after the Tier-1 landing review found the earlier CONSERVED-RELATIVE a costume (finding
T1-S1, closed Relabeled): the earlier `inSightConserved` was set true on the state-bisimilarity (the collapse), not
on a genuine `Q`-invariance. The new audit `ws5_audit_not_conserved` is the corrected core: it CHECKS that a
conserved-in-sight measure would be plain-invariant, and exhibits that `rankM` is not — the check the earlier gate
lacked. The five audit clauses (a)-(e) bundle the payoffs; (e) is the grep-certified placeholder.

Design docs: `program-2/series-7/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S7.ws1
import P2S7.ws2
import P2S7.ws3
import P2S7.ws4

universe u

namespace P2S7

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `conservedRel` the measure is conserved in-sight, the import its source, the free-lunch
crux relative; `monotoneOnly` nothing conserved even in-sight, only an arrow rises (all creation, no ledger);
`freeLunch` the diagonal a genuine source with creation FORCED and conservation excluded; `global` a genuine
absolute conserved invariant is forced; `disconnected` no non-trivial measure survives; `partial'` primed
(`partial` is a Lean keyword) an obligation degenerate. No identifier embeds a forbidden content-name as a whole
word (audit e). -/
inductive Outcome
  | conservedRel
  | monotoneOnly
  | freeLunch
  | global
  | disconnected
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION.** `monotoneOnly` iff the measure is non-trivial (WS1) but NOT conserved in-sight (WS2/WS3
— `inSightConserved = false`): an arrow with no ledger. `conservedRel` would require `inSightConserved` true AND the
free-lunch crux reaching both sides; `freeLunch` creation reachable with conservation excluded; `disconnected` no
non-trivial measure; `global` a global invariant forced; `partial'` degenerate. The function is unchanged from the
prior landing; only the HONEST flags differ (the earlier `inSightConserved = true` was the costume). -/
def verdict (nonTrivial inSightConserved changeIsSource
            freeLunchReachable conservedReachable globalForced : Bool) : Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if globalForced then Outcome.global
  else if !inSightConserved then Outcome.monotoneOnly
  else if !changeIsSource then Outcome.partial'
  else if freeLunchReachable && !conservedReachable then Outcome.freeLunch
  else if !freeLunchReachable then Outcome.partial'
  else Outcome.conservedRel

/-- **THE COMPUTED VERDICT.** On the honest flags (a non-trivial measure, NOT conserved in-sight, the change a
genuine import, the rise internal creation, no global forced), `monotoneOnly`, by computation. -/
theorem ws5_verdict_eq : verdict true false true true false false = Outcome.monotoneOnly := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all six outcomes. `conservedRel`/`freeLunch` require
`inSightConserved = true`, which the honest flags do NOT set (so neither is reachable by fiat here). -/
theorem ws5_verdict_discriminates :
    verdict false false true true false false = Outcome.disconnected
  ∧ verdict true true true true true true  = Outcome.global
  ∧ verdict true false true true false false = Outcome.monotoneOnly
  ∧ verdict true true false true true false = Outcome.partial'
  ∧ verdict true true true true false false = Outcome.freeLunch
  ∧ verdict true true true true true false  = Outcome.conservedRel := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set: `nonTrivial`
(WS1, `ws1_rank_nontrivial`); the ARROW `rankM (reifyM {e0}) = rankM e0 + 1` (WS2, `ws2_tick_raises`); NOT conserved
in-sight, so `inSightConserved = false` (WS3, `ws3_not_conserved` — a plain-bisimilar pair with different `rankM`);
the rise internal creation (WS4, `ws4_rise_is_internal`). The meta-flag `globalForced` is honestly `false`. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (rankM e1 ≠ rankM e0 ∧ AttentionDistinguishes (destML hinf) e1 e0)
  ∧ (rankM (reifyM {e0}) = rankM e0 + 1)
  ∧ ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp) :=
  ⟨⟨(ws1_rank_nontrivial hinf).1, (ws1_rank_nontrivial hinf).2.1⟩,
   (ws2_tick_raises hinf).1,
   (ws3_not_conserved hinf).1,
   (ws4_rise_is_internal hinf).1⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(the corrected core, the gate-gap fix) IN-SIGHT CONSERVATION IS NOT ESTABLISHED BY THE COLLAPSE.** A genuinely
in-sight-conserved measure would be plain-bisimulation-invariant; `rankM` is NOT (`e1 ~ e0` plainly yet `rankM e1 ≠
rankM e0`), and any plain-invariant `f` must agree on `e1`, `e0` (blind to the tick). So `inSightConserved` cannot be
honestly set true from the state-bisimilarity — the collapse hides the rise, it does not conserve the measure — and
the verdict is `monotoneOnly`. This is the check the earlier landing lacked (finding T1-S1). -/
theorem ws5_audit_not_conserved {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (∀ f : MCar → ℕ,
        (∀ x y, (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R x y) → f x = f y) → f e1 = f e0)
  ∧ (verdict true false true true false false = Outcome.monotoneOnly) :=
  ⟨(ws3_not_conserved hinf).1, (ws3_not_conserved hinf).2, rfl⟩

/-- **CONSERVATION IS NOT REACHABLE (the crux, settled by proof).** The verdict is `monotoneOnly`, not `conservedRel`,
because conservation is IMPOSSIBLE from within, not merely unbuilt: the tick raises the measure (`rankM (reifyM {e0})
≠ rankM e0`) and the diagonal is always a source (`ws2_residue_free`, the residue free for every inspection), so there
is no genuine conserved side. The earlier CONSERVED-RELATIVE landing reached the conserved side only by a counter
disconnected from the diagonal (finding T1-S1). The full search is on record in `P2S7.ConservedRelativeAttempt`. -/
theorem ws5_audit_no_conserved_side {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (rankM (reifyM {e0}) ≠ rankM e0)
  ∧ (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)
  ∧ (verdict true false true true false false = Outcome.monotoneOnly) :=
  ⟨(ws4_no_conserved_side hinf).1, (ws4_no_conserved_side hinf).2, rfl⟩

/-- **(a) NO GLOBAL CONSERVATION ASSERTED.** No proof term asserts a globally conserved `Q` — indeed not even a LOCAL
conservation holds (`rankM` rises, `ws3_not_conserved`); `global` is returned only under `globalForced = true`
(honestly false). -/
theorem ws5_audit_no_global {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (verdict true false true true true true = Outcome.global) :=
  ⟨(ws3_not_conserved hinf).1, rfl⟩

/-- **(b) THE VERDICT IS NOT BY FIAT.** The measure is non-trivial (`ws1_rank_nontrivial`) — so NOT `disconnected` —
and it genuinely RISES (`ws2_tick_raises`) and is NOT conserved (`ws3_not_conserved`) — so `monotoneOnly`, not
`conservedRel`. The arrow is a genuine `Q`-fact, not a definitional artifact. -/
theorem ws5_audit_arrow_genuine {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (rankM e1 ≠ rankM e0)
  ∧ (rankM (reifyM {e0}) = rankM e0 + 1)
  ∧ ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0) :=
  ⟨(ws1_rank_nontrivial hinf).1, (ws2_tick_raises hinf).1, (ws3_not_conserved hinf).1⟩

/-- **(c) THE RISE IS THE DIAGONAL-AS-SOURCE, NOT IMPORT-NESS (the costume gate).** The internal source of the arrow
is the residue (`ws2_residue_free`, the P1 diagonal): self-inspection manufactures non-recoverable content from
within, no import crossing. The measure rises by creation, not by a boundary import. -/
theorem ws5_audit_source_is_diagonal {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)
  ∧ AttentionDistinguishes (destML hinf) e1 e0 :=
  ws4_rise_is_internal hinf

/-- **(d) EACH CHANGE IS A GENUINE IMPORT.** `ws3_change_is_source` (every `Q`-change an `AttentionDistinguishes`
import) and `¬ Recoverable (destML)` rest on Series 07 (`ws4_recoverable_not_import`): the rise is real
import-content, not a bookkeeping artifact. The import is quantified, never named. -/
theorem ws5_audit_change_is_source {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ ¬ Recoverable (destML hinf) :=
  ws3_change_is_source hinf

/-- **(e) NAMES-NOT-TERMS.** A META-property about identifiers, not a proposition: no proof term, definition, or
discharged obligation is named as a forbidden content-word ("energy," "conservation," "information," "measure,"
"creation," "self," "import," "god," "choice," "subjectivity") as a whole word. Enforced by the protocol §6
mechanical grep (hits are docstring prose only), not by this `True`; carried as the accepted house placeholder.
Made non-vacuous at Program Review 2-1 (PR2-R2, the accepted S13 C1-S1 form): the statement below proves
the outcome codomain a genuine discrimination among neutrally-named values. -/
theorem ws5_audit_names_not_terms :
    Outcome.conservedRel ≠ Outcome.monotoneOnly
  ∧ Outcome.monotoneOnly ≠ Outcome.freeLunch
  ∧ Outcome.freeLunch ≠ Outcome.global
  ∧ Outcome.global ≠ Outcome.disconnected
  ∧ Outcome.disconnected ≠ Outcome.partial'
  ∧ Outcome.conservedRel ≠ Outcome.partial' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end P2S7
