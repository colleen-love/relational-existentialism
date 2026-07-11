/-
`series-8/formal/Series8/ws7.lean`

WS7 — **The anti-circularity audit.** Series 8, owns the verdict.

Audits the two Series-8 circularity risks — conservation-by-fiat and
perspective-recoverable-by-definition — aggregated into a mechanized `Audit` certificate whose every
field is a theorem, and a typed `Series8Verdict` that is a function of it (transcribing Series 7's
`Audit`/`verdict` pattern), so it cannot be hand-set. Runs last; consumes WS1–WS6.

Design doc: `series-8/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series8.ws2
import Series8.ws6

universe u

namespace Series8.WS7

open Series8.WS1 Series8.WS2 Series8.WS3 Series8.WS5 Cardinal

variable {κ : Cardinal.{u}}

/-- Series 8's three outcomes. -/
inductive Series8Verdict
  | perspectiveEstablished   -- spine lands, plurality free, dynamics forced, conservation settled
  | monismStands             -- god's-eye node constructible OR perspective recoverable
  | Circular                 -- freeness or conservation holds only by a definitional exclusion
  deriving DecidableEq

/-- The mechanized audit certificate. Every field is a THEOREM from WS1–WS5; you cannot construct an
`Audit` without discharging them, and the verdict is a function of it. -/
structure Audit (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) : Prop where
  spineCollapses : ∀ {Q X : Type u} (dest : X → LkObj κ Q X), Symmetric dest →
                     BehaviorallyIdentifiedL dest → Subsingleton X
  freenessTheorem : ¬ Recoverable (labelLoop hinf)
                    ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
                    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  orderEndogenous : ∃ h : Hold (twoLoop hinf), ReReStep (twoLoop hinf) h h
  noLeaf : ∀ {Y : Type u} (dest : Y → PkObj κ Y) (h : Hold dest), SHNE dest h.1.2 →
             ∃ h', ReReStep dest h h' ∧ SHNE dest h'.1.1
  conservationTested : (∃ (h h' : Hold (pingPong hinf)), ReReStep (pingPong hinf) h h' ∧ h ≠ h'
                          ∧ breadth (pingPong hinf) h' = breadth (pingPong hinf) h)
                       ∧ ¬ ConservesStrict (twoLoop hinf)

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5. -/
theorem ws7_audit (hinf : ℵ₀ ≤ κ) : Audit κ hinf where
  spineCollapses := fun {_Q _X} dest hsym hbeh => ws1_gods_eye_collapses dest hsym hbeh
  freenessTheorem := ⟨ws2_free_not_recoverable hinf,
                      (ws4_free_label_is_import hinf).1, (ws4_free_label_is_import hinf).2⟩
  orderEndogenous := ws3_imported_index_refuted hinf
  noLeaf := fun {_Y} dest h hs => ws3_rerestriction_no_leaf dest h hs
  conservationTested := ws5_verdict_justified hinf

/-- **D2 — the typed verdict** (series-review-1 R2, relabelled honestly). The LOAD-BEARING content is
the `Audit` *structure*: its five fields are theorems, so you cannot construct a certificate without
discharging them, and `ws7_audit` does. `verdict` then tags a discharged certificate with the outcome
— it is a constant selector on *having a certificate*, NOT a decision procedure that reads the
certificate's contents (a `Prop` certificate is proof-irrelevant, so it cannot be branched on). The
earned fact is "a certificate exists ⟹ the tag is `perspectiveEstablished`"; the anti-hand-setting
guarantee lives in the certificate's fields, not in this selector. -/
def verdict {hinf : ℵ₀ ≤ κ} (_cert : Audit κ hinf) (_settled : Bool) : Series8Verdict :=
  .perspectiveEstablished

def ws7_verdict (hinf : ℵ₀ ≤ κ) : Series8Verdict := verdict (ws7_audit hinf) true

theorem ws7_verdict_eq (hinf : ℵ₀ ≤ κ) :
    ws7_verdict hinf = Series8Verdict.perspectiveEstablished := rfl

/-- **D3 — with a discharged certificate the tag is neither monism nor Circular.** Since `verdict` is
a constant selector, these are facts about the three distinct constructors — the substantive content
is upstream: without an `Audit` (which requires all five theorems) there is no `perspectiveEstablished`
tag at all. The certificate is the falsifiable object; this records that the tag on it is never the
failure outcomes. -/
theorem ws7_audited_not_monism {hinf : ℵ₀ ≤ κ} (cert : Audit κ hinf) (b : Bool) :
    verdict cert b ≠ Series8Verdict.monismStands := by
  show Series8Verdict.perspectiveEstablished ≠ Series8Verdict.monismStands; decide

theorem ws7_audited_not_circular {hinf : ℵ₀ ≤ κ} (cert : Audit κ hinf) (b : Bool) :
    verdict cert b ≠ Series8Verdict.Circular := by
  show Series8Verdict.perspectiveEstablished ≠ Series8Verdict.Circular; decide

/-- **D4 — the two guards.** No conservation-by-fiat (conservation tested & refuted); no
freeness-defined-in (freeness a theorem; the god's-eye node collapsed by the engine). -/
theorem ws7_no_conservation_by_fiat (hinf : ℵ₀ ≤ κ) :
    (¬ ConservesStrict (twoLoop hinf))
  ∧ (∃ (h h' : Hold (pingPong hinf)), ReReStep (pingPong hinf) h h' ∧ h ≠ h'
        ∧ breadth (pingPong hinf) h' = breadth (pingPong hinf) h) := by
  obtain ⟨kill, refuted⟩ := ws5_verdict_justified hinf
  exact ⟨refuted, kill⟩

theorem ws7_freeness_not_defined_in (hinf : ℵ₀ ≤ κ) :
    (¬ Recoverable (labelLoop hinf))
  ∧ (∀ {Q X : Type u} (dest : X → LkObj κ Q X), Symmetric dest →
       BehaviorallyIdentifiedL dest → Subsingleton X) :=
  ⟨ws4_labelLoop_not_recoverable hinf,
   fun {_Q _X} dest hsym hbeh => ws1_gods_eye_collapses dest hsym hbeh⟩

/-- **D5 — the strip ledger.** Each payoff, stripped of its structural word, is a bare
recoverable-collapse / free-label / seriality / breadth-constancy fact — all real, the perspectival
reading named as earned surplus. -/
theorem ws7_strip_ledger (hinf : ℵ₀ ≤ κ) :
    (∀ {Q X : Type u} (dest : X → LkObj κ Q X), Recoverable dest → BehaviorallyIdentifiedL dest →
       (∀ x, SHNE (plainOf dest) x) → Subsingleton X)
  ∧ ((∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
       ∧ ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (∀ {Y : Type u} (dest : Y → PkObj κ Y) (h : Hold dest), SHNE dest h.1.2 →
       ∃ h', ReReStep dest h h' ∧ SHNE dest h'.1.2)
  ∧ (∃ (h h' : Hold (pingPong hinf)), ReReStep (pingPong hinf) h h' ∧ h ≠ h'
       ∧ breadth (pingPong hinf) h' = breadth (pingPong hinf) h) := by
  refine ⟨fun {_Q _X} dest hrec hbeh hatom => ws1_no_gods_eye dest hrec hbeh hatom,
          ws4_free_label_is_import hinf,
          fun {_Y} dest h hs => ws3_dynamics_forced dest h hs, ?_⟩
  obtain ⟨kill, _⟩ := ws5_verdict_justified hinf
  exact kill

/-- The no-certificate outcome: `Circular` (a failed audit leaves only this). The load-bearing
content is D3 (with a certificate, never Circular). -/
def verdictNoCertificate : Series8Verdict := .Circular

end Series8.WS7
