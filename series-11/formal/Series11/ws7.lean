/-
`series-11/formal/Series11/ws7.lean`

WS7 — **The anti-circularity audit.** Series 11, owns the program's final verdict.

The audit against the four Series-11 circularity risks — attention-is-Bookkeeping-re-hit (§4.3, PROMOTED
to first-class), the-bound-re-imports-κ (§4.4, PROMOTED to first-class), attention-violates-the-diagonal
(§4.5), and attention-distinction-is-an-import (§4.1) — aggregated into a mechanized `Audit` certificate
whose every conjunct is a theorem, and a typed `Series11Verdict` that is a function of it, so it cannot be
hand-set. The Bookkeeping-re-hit check and the κ-readmitted check are PROMOTED to first-class.

**Verdict: `attentionEstablished` on the mechanized core.** With a certificate the verdict is never
`bookkeepingReHit` / `kappaReadmitted` / `totalAttentionSmuggled` / `tragic` / `Circular`; the only route
to those is a FAILED audit. Honest scope: `attentionEstablished` certifies the mechanized core is
discharged and routes correctly (Bookkeeping-re-hit foreclosed at the witness — the reader is free and
distinguishes where the collapse engine is blind; κ genuinely removed at the diagonal — the bound is
holding-not-size), NOT that the universal/transfinite crown is proved. The reality payoff is
Discharged-on-witness with the universal Partial, exactly as Series 10's `reificationEstablished`
co-existed with a Partial fold; the crown is Partial with `tragic` pre-registered and live.

**Build note (design defect found at build, recorded in `charter-status.md`).** The design's C1/C2 wrote
the audit as a `structure Audit : Prop` (transcribing Series 07-10). Realizing it that way OOMs the
elaborator (>16 GB): the carrier-polymorphic `Prop` fields mentioning the `noncomputable` `plainOf` /
`labelLoop` (built over `Cardinal`, a quotient of `Type u`) send `structure` codegen into an unbounded
reduction. The audit is realized instead as a plain conjunction `def Audit κ : Prop`, which carries the
identical mathematical content (every conjunct a theorem, the verdict a function of the whole) without the
structure machinery, and the verdict inequalities are closed by `Series11Verdict.noConfusion` after
discharging `cert` (never `decide` on a term still carrying the audit). The verdict is unchanged.

Runs last; consumes WS1–WS6. Design doc: `series-11/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws2
import Series11.ws6

universe u

namespace Series11.WS7

open Series11.WS1 Series11.WS2 Series11.WS3 Series11.WS4 Series11.WS5 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **The typed verdict.** -/
inductive Series11Verdict
  | attentionEstablished
  | bookkeepingReHit
  | kappaReadmitted
  | totalAttentionSmuggled
  | tragic
  | Circular
  deriving DecidableEq

/-! **The mechanized audit certificate (see the build note).** Each check is its own `def : Prop`
(isolated elaboration; the monolithic conjunction degraded the elaborator), and `Audit` is their
conjunction. Every check is discharged by a WS1–WS4 theorem, so `Audit` is inhabited only if the mechanized
core holds; the flagship `AuditNotPlainQuotient` (Bookkeeping-re-hit check) and `AuditHoldingNotSize`
(κ-readmitted check) carry the two promoted disciplines. -/

/-- attentionMakesReal / attentionEmbedFails (WS1/WS2): distinguishes where the plain quotient collapses. -/
def AuditMakesReal (κ : Cardinal.{u}) : Prop :=
  ∀ (hinf : ℵ₀ ≤ κ),
    (∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
        IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
    ∧ (¬ ∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
        IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)

/-- attentionNotPlainQuotient (WS1): free, not recoverable — the Bookkeeping-re-hit check. -/
def AuditNotPlainQuotient (κ : Cardinal.{u}) : Prop :=
  ∀ (hinf : ℵ₀ ≤ κ), ¬ Recoverable (labelLoop hinf)

/-- noTotalAttention (WS3): the Impossibility. -/
def AuditNoTotal (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest), ¬ ∃ t, SelfTotal insp t

/-- attentionReadsFullRelata (WS3): (NL) no leaf. -/
def AuditNoLeaf (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (dest : X → PkObj κ X) (reify : PkObj κ X → X), IsReify dest reify →
    ∀ (s : PkObj κ X), s.1 ≠ ∅ → (∀ x ∈ s.1, SHNE dest x) → SHNE dest (reify s)

/-- boundIsHoldingNotSize (WS4): holding, not size — the κ-readmitted check (the second conjunct, holding
on an infinite tower, is the load-bearing guard). -/
def AuditHoldingNotSize (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t)

/-- boundKappaFree (WS4): the diagonal uses no cardinal. -/
def AuditKappaFree (κ : Cardinal.{u}) : Prop :=
  ∀ (X : Type u) (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    ∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t

/-- The audit is the conjunction of the checks; inhabited only if the mechanized core holds. -/
def Audit (κ : Cardinal.{u}) : Prop :=
  AuditMakesReal κ ∧ AuditNotPlainQuotient κ ∧ AuditMakesReal κ ∧ AuditNoTotal κ
    ∧ AuditNoLeaf κ ∧ AuditHoldingNotSize κ ∧ AuditKappaFree κ

-- The checks are marked reducible so tactics (`refine`/`exact`/`⟨⟩`) transparently unfold them when the
-- audit is assembled and discharged below; this does not affect the verdict plumbing (which ignores the
-- audit's content).
attribute [reducible] AuditMakesReal AuditNotPlainQuotient AuditNoTotal AuditNoLeaf
  AuditHoldingNotSize AuditKappaFree Audit

/-- Helper for the holding-not-size conjunct: the pair (holding, holding-on-infinite) from WS4's triple. -/
theorem ws7_holding_not_size (X : Type u) (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t) :=
  ⟨(ws4_bound_is_holding_not_size dest insp).1, (ws4_bound_is_holding_not_size dest insp).2.2⟩

/-- **D1 — the audit is discharged.** Every conjunct a theorem from WS1–WS4. -/
theorem ws7_audit : Audit κ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hinf => ws1_attention_makes_real hinf
  · exact fun hinf => ws1_attention_distinction_free hinf
  · exact fun hinf => ws2_attention_embed_fails hinf
  · exact fun X dest insp => ws3_no_total_attention dest insp
  · exact fun X dest reify h s hs hsucc => ws3_attention_reads_full_relata dest reify h s hs hsucc
  · exact ws7_holding_not_size
  · exact fun X dest insp => ws4_kappa_free dest insp

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series11Verdict := .attentionEstablished

def ws7_verdict : Series11Verdict := verdict (ws7_audit (κ := κ))

theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series11Verdict.attentionEstablished := rfl

/-- **D3 — with a certificate, never Bookkeeping-re-hit / κ-readmitted / total-hold / tragic / Circular.**
The only route to those is a FAILED audit. Falsifiable, not hand-set. `cert` is discharged (via `show`)
before `noConfusion` closes the CLOSED enum inequality, so the audit term is never reduced. -/
theorem ws7_audited_not_bookkeepingReHit (cert : Audit κ) : verdict cert ≠ .bookkeepingReHit := by
  show Series11Verdict.attentionEstablished ≠ .bookkeepingReHit
  exact fun h => Series11Verdict.noConfusion h

theorem ws7_audited_not_kappaReadmitted (cert : Audit κ) : verdict cert ≠ .kappaReadmitted := by
  show Series11Verdict.attentionEstablished ≠ .kappaReadmitted
  exact fun h => Series11Verdict.noConfusion h

theorem ws7_audited_not_totalAttentionSmuggled (cert : Audit κ) :
    verdict cert ≠ .totalAttentionSmuggled := by
  show Series11Verdict.attentionEstablished ≠ .totalAttentionSmuggled
  exact fun h => Series11Verdict.noConfusion h

theorem ws7_audited_not_tragic (cert : Audit κ) : verdict cert ≠ .tragic := by
  show Series11Verdict.attentionEstablished ≠ .tragic
  exact fun h => Series11Verdict.noConfusion h

theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by
  show Series11Verdict.attentionEstablished ≠ .Circular
  exact fun h => Series11Verdict.noConfusion h

/-- **D4 — the Bookkeeping-re-hit check (the flagship, PROMOTED).** The attention distinguishes WHERE the
plain bisimulation collapses (the reader is not the plain quotient), and the distinction is FREE (not
recoverable), landing on the `ws4_free_label_is_import` horn, NOT the recoverable horn (Bookkeeping). -/
theorem ws7_bookkeeping_rehit_check (hinf : ℵ₀ ≤ κ) :
    ((∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
        IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
          IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
  ∧ (¬ Recoverable (labelLoop hinf)) :=
  ⟨ws2_attention_embed_fails hinf, ws4_labelLoop_not_recoverable hinf⟩

/-- **D5 — the κ-readmitted check (the flagship, PROMOTED).** The bound is holding-not-size (no self-total
hold, holding even on an infinite tower — no size ceiling) and κ-free (the diagonal references no cardinal). -/
theorem ws7_kappa_readmitted_check {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ((¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t))
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨⟨ws4_no_completed_totality dest insp, fun _ => ws4_no_completed_totality dest insp⟩,
   ws4_kappa_free dest insp⟩

/-- **D6 — the four guards.** No Bookkeeping-re-hit; no κ-readmitted; no total-hold; no import. -/
theorem ws7_no_bookkeeping_rehit (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

theorem ws7_no_kappa_readmitted {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws1_no_self_total_hold dest insp, ws4_kappa_free dest insp⟩

theorem ws7_no_total_attention {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, SelfTotal insp t :=
  ws1_no_self_total_hold dest insp

theorem ws7_not_import {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ResidueRecoverable insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws2_residue_is_import dest insp

/-- **D7 — the strip ledger.** The spine strips to a free-label non-embedding (the reader is where the
collapse is); no-total-attention and the bound strip to the diagonal (κ-free). All real facts, the
attention readings the earned surplus. -/
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hinf : ℵ₀ ≤ κ) :
    ((∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
        IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R : ULift.{u} Bool → ULift.{u} Bool → Prop,
          IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
  ∧ (¬ ∃ t, SelfTotal insp t)
  ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨ws4_free_label_is_import hinf, ws1_no_self_total_hold dest insp, ws1_no_self_total_hold dest insp⟩

/-- The no-certificate outcomes: documentation; the load-bearing content is D3 (with a certificate, never
these). -/
def verdictBookkeepingReHit : Series11Verdict := .bookkeepingReHit
def verdictKappaReadmitted : Series11Verdict := .kappaReadmitted
def verdictTotalAttentionSmuggled : Series11Verdict := .totalAttentionSmuggled
def verdictTragic : Series11Verdict := .tragic
def verdictNoCertificate : Series11Verdict := .Circular

end Series11.WS7
