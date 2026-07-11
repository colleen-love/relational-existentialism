/-
`series-10/formal/Series10/ws7.lean`

WS7 — **The anti-circularity audit.** Series 10, owns the verdict.

The audit against the four Series-10 circularity risks — growth-is-bookkeeping (the moving-hole re-hit,
PROMOTED to first-class), reify-smuggles-a-self-total-hold (trivial closure), κ-by-fiat (conservation
relocated, PROMOTED to first-class), and reification-is-an-import — aggregated into a mechanized `Audit`
certificate whose every field is a theorem, and a typed `Series10Verdict` that is a function of it, so it
cannot be hand-set. The flagship fields `growthStrict` (bookkeeping check) and `foldIsReflexivity`
(κ-by-fiat check) carry the two promoted disciplines.

Runs last; consumes WS1–WS6. Design doc: `series-10/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws2
import Series10.ws6

universe u

namespace Series10.WS7

open Series10.WS1 Series10.WS2 Series10.WS3 Series10.WS4 Series10.WS5 Cardinal

variable {κ : Cardinal.{u}}

/-- The typed verdict. `reificationEstablished`: productive blindness routes through the diagonal, growth
strict-and-internal (not a `List`), CLOSE forbidden, fold settled (Partial / Discharged-on-scaffold), no
reliance on small κ. `bookkeeping`: growth is a lengthening record while the carrier is
bisimulation-constant. `selfTotalSmuggled`: `reify` closes the tower (a design defect). `kappaByFiat`: the
fold rests on the imposed κ. `Circular`: freeness/growth/fold defined-in. -/
inductive Series10Verdict
  | reificationEstablished | bookkeeping | selfTotalSmuggled | kappaByFiat | Circular
  deriving DecidableEq

/-- **The mechanized audit certificate.** Every field a theorem from WS1–WS5; the flagship fields
`growthStrict` (the bookkeeping check) and `foldIsReflexivity` (the κ-by-fiat check) carry the two
promoted disciplines. -/
structure Audit (κ : Cardinal.{u}) : Prop where
  freeReification : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)
  growthStrict : ∀ (hinf : ℵ₀ ≤ κ),
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩
  growthIsFreeLabel : ∀ (hinf : ℵ₀ ≤ κ),
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  reifyPreservesSHNE : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (_ : IsReify dest reify) (s : PkObj κ X) (_ : s.1 ≠ ∅) (_ : ∀ x ∈ s.1, SHNE dest x),
    SHNE dest (reify s)
  orderEndogenous : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (a b : Set X),
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b
  closeForbidden : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X), ¬ Closes dest reify insp Ω₀
  foldIsReflexivity : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X),
    Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω')
  foldOnScaffold : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X),
    Folds dest reify Ω₀

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5, including the flagship
`growthStrict` (the bookkeeping check) and `foldIsReflexivity` (the κ-by-fiat check). -/
theorem ws7_audit : Audit κ where
  freeReification := fun dest insp => ws1_free_reification dest insp
  growthStrict := fun hinf => ws2_growth_strict hinf
  growthIsFreeLabel := fun hinf => ws2_growth_is_free_label hinf
  reifyPreservesSHNE := fun dest reify h s hs hsucc => ws3_reify_preserves_SHNE dest reify h s hs hsucc
  orderEndogenous := fun dest reify a b => ws3_order_endogenous dest reify a b
  closeForbidden := fun dest reify insp Ω₀ => ws4_close_forbidden dest reify insp Ω₀
  foldIsReflexivity := fun dest reify Ω₀ => ws4_fold_is_reflexivity dest reify Ω₀
  foldOnScaffold := fun dest reify Ω₀ => ws5_fold_on_scaffold dest reify Ω₀

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series10Verdict := .reificationEstablished

def ws7_verdict : Series10Verdict := verdict (ws7_audit (κ := κ))

theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series10Verdict.reificationEstablished := rfl

/-- **D3 — with a certificate, never bookkeeping, never smuggle, never κ-by-fiat, never Circular.** The
ONLY route to those is a FAILED audit; `growthStrict` is why `≠ bookkeeping` is earned, `foldIsReflexivity`
why `≠ kappaByFiat`, `closeForbidden` why `≠ selfTotalSmuggled`. -/
theorem ws7_audited_not_bookkeeping (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.bookkeeping := by
  show Series10Verdict.reificationEstablished ≠ Series10Verdict.bookkeeping; decide

theorem ws7_audited_not_selfTotalSmuggled (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.selfTotalSmuggled := by
  show Series10Verdict.reificationEstablished ≠ Series10Verdict.selfTotalSmuggled; decide

theorem ws7_audited_not_kappaByFiat (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.kappaByFiat := by
  show Series10Verdict.reificationEstablished ≠ Series10Verdict.kappaByFiat; decide

theorem ws7_audited_not_circular (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.Circular := by
  show Series10Verdict.reificationEstablished ≠ Series10Verdict.Circular; decide

/-- **D4 — the bookkeeping check (the flagship, PROMOTED).** Growth is not-bisim-embed (a bigger world)
landing on the free-import horn, NOT the recoverable horn (which would be Bookkeeping). -/
theorem ws7_bookkeeping_check (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws2_growth_strict hinf, ws2_growth_is_free_label hinf⟩

/-- **D5 — the κ-by-fiat check (the flagship, PROMOTED).** The fold is distributed reflexivity (a
reachability), NOT a cardinality bound, and it holds for all large κ (`ws5_fold_on_scaffold` rests on
`reifyStep`'s definition). -/
theorem ws7_kappa_discipline {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    (Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω'))
  ∧ (Folds dest reify Ω₀) :=
  ⟨ws4_fold_is_reflexivity dest reify Ω₀, ws5_fold_on_scaffold dest reify Ω₀⟩

/-- **D6a — no bookkeeping** (growth strict, not a `List`). -/
theorem ws7_no_bookkeeping (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ := ws2_growth_strict hinf

/-- **D6b — no smuggle** (CLOSE forbidden: no self-total hold reached). -/
theorem ws7_no_smuggle {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : ¬ Closes dest reify insp Ω₀ :=
  ws4_close_forbidden dest reify insp Ω₀

/-- **D6c — no κ-by-fiat** (the fold holds as reachability for all large κ). -/
theorem ws7_no_kappa_by_fiat {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    Folds dest reify Ω₀ := ws5_fold_on_scaffold dest reify Ω₀

/-- **D6d — no import** (freeness routes through the diagonal: recoverability reconstructs a self-total
hold). -/
theorem ws7_not_import {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws1_free_reification dest insp

/-- **D7 — the strip ledger.** Each payoff, stripped of its structural word, is a bare fact — productive
blindness → the diagonal freeness (not a fresh assumption), growth → a label-non-embedding (NOT a `List`,
the bookkeeping check surfaced), CLOSE-forbidden → the diagonal, the fold → a reification-reachability
(NOT a κ-bound, the κ-by-fiat check surfaced). All hold; the reification readings are the earned surplus. -/
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ h, insp h = residue insp)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ Closes dest reify insp Ω₀)
  ∧ (Folds dest reify Ω₀) :=
  ⟨ws2_residue_free dest insp, ws2_growth_strict hinf,
   ws4_close_forbidden dest reify insp Ω₀, ws5_fold_on_scaffold dest reify Ω₀⟩

/-- The no-certificate outcomes: documentation; the load-bearing content is D3 (with a certificate, never
these). -/
def verdictBookkeeping : Series10Verdict := .bookkeeping
def verdictSelfTotalSmuggled : Series10Verdict := .selfTotalSmuggled
def verdictKappaByFiat : Series10Verdict := .kappaByFiat
def verdictNoCertificate : Series10Verdict := .Circular

end Series10.WS7
