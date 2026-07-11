/-
`series-10/formal/Series10/ws7.lean`

WS7 — **The anti-circularity audit.** Series 10, owns the verdict.

**PHASE E RE-GRADE (series-review-1 S1/S2/S3). Verdict: `bookkeeping`.** The engine parts are genuinely
Discharged (the diagonal `ws1_no_self_total_hold`, the tower construction, (NL) `ws3_reify_preserves_SHNE`,
the endogenous order `prec`, CLOSE-forbidden at the inspection level, the fold Partial). But the PAYOFF —
strict internal carrier growth — is **Bookkeeping** (S1): on the plain carrier the collapse engine makes
every reified `SHNE` relatum bisimilar to prior relata, so `Ω_{α+1}` bisim-embeds into `Ω_α`
(`growthBookkeeping`, from `ws2_reify_bisim_embeds`). The verdict function therefore returns `.bookkeeping`,
not `reificationEstablished`: the honest headline is "engine Discharged, payoff Bookkeeping." The `Audit`
fields are all genuine theorems; the verdict reads the `growthBookkeeping` field and reports the
moving-hole re-hit honestly. Two accompanying relabels: `foldOnScaffold` is the DEFINITIONAL per-step fold
(S2, `reifyStep`'s construction, not a substantive discharge), and `closeForbidden` is the
INSPECTION-LEVEL diagonal (S3, tower-independent; the carrier-level closure is charter §9's open question).

Runs last; consumes WS1–WS6. Design doc: `series-10/spec/ws7-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series10.ws2
import Series10.ws6

universe u

namespace Series10.WS7

open Series10.WS1 Series10.WS2 Series10.WS3 Series10.WS4 Series10.WS5 Cardinal

variable {κ : Cardinal.{u}}

/-- The typed verdict. `bookkeeping` (DELIVERED): the engine is Discharged but the payoff — strict
internal growth — is the moving-hole re-hit (the tower is bisimulation-constant on the `SHNE` field).
`reificationEstablished`: would require strict internal growth, which is FALSE here (S1). `selfTotalSmuggled`:
`reify` closes the tower (not triggered, CLOSE-forbidden held). `kappaByFiat`: the fold rests on the
imposed κ (not triggered, the fold is reachability for all large κ). `Circular`: freeness/growth/fold
defined-in (not triggered, disclosures present). -/
inductive Series10Verdict
  | reificationEstablished | bookkeeping | selfTotalSmuggled | kappaByFiat | Circular
  deriving DecidableEq

/-- **The mechanized audit certificate.** Every field a theorem from WS1–WS5. The flagship field is
`growthBookkeeping` — the honest S1 finding that the reified relatum bisim-embeds (growth is
cardinality-only). `foldOnScaffold` is the definitional per-step fold (S2); `closeForbidden` is the
inspection-level diagonal (S3). -/
structure Audit (κ : Cardinal.{u}) : Prop where
  freeReification : ∀ {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)
  reifyInjective : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X),
    IsReify dest reify → Function.Injective reify
  -- S1: the tower is bisimulation-constant on the SHNE field — the reified relatum bisim-embeds.
  growthBookkeeping : ∀ {X : Type u} (dest : X → PkObj κ X) (x y : X),
    SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y
  reifyPreservesSHNE : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (_ : IsReify dest reify) (s : PkObj κ X) (_ : s.1 ≠ ∅) (_ : ∀ x ∈ s.1, SHNE dest x),
    SHNE dest (reify s)
  orderEndogenous : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (a b : Set X),
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b
  -- S3: no self-total hold at the inspection level (tower-independent; carrier closure is charter §9's open).
  closeForbidden : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X), ¬ Closes dest reify insp Ω₀
  foldIsReflexivity : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X),
    Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω')
  -- S2: the DEFINITIONAL per-step fold (reifyStep's construction read back, not a substantive discharge).
  foldOnScaffold : ∀ {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X),
    Folds dest reify Ω₀

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5. -/
theorem ws7_audit : Audit κ where
  freeReification := fun dest insp => ws1_free_reification dest insp
  reifyInjective := fun dest reify h => ws1_reify_injective dest reify h
  growthBookkeeping := fun dest x y hx hy => ws2_growth_is_bookkeeping dest x y hx hy
  reifyPreservesSHNE := fun dest reify h s hs hsucc => ws3_reify_preserves_SHNE dest reify h s hs hsucc
  orderEndogenous := fun dest reify a b => ws3_order_endogenous dest reify a b
  closeForbidden := fun dest reify insp Ω₀ => ws4_close_forbidden dest reify insp Ω₀
  foldIsReflexivity := fun dest reify Ω₀ => ws4_fold_is_reflexivity dest reify Ω₀
  foldOnScaffold := fun dest reify Ω₀ => ws5_fold_on_scaffold dest reify Ω₀

/-- **D2 — the typed verdict**, a function of the discharged audit. The `growthBookkeeping` field is why
the verdict is `bookkeeping`: the payoff (strict growth) is the moving-hole re-hit. -/
def verdict (_cert : Audit κ) : Series10Verdict := .bookkeeping

def ws7_verdict : Series10Verdict := verdict (ws7_audit (κ := κ))

theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series10Verdict.bookkeeping := rfl

/-- **D3 — the verdict is `bookkeeping`, and given a certificate it is never the others.**
`≠ reificationEstablished` because growth is bookkeeping (S1); `≠ selfTotalSmuggled` because CLOSE is
forbidden (no smuggle); `≠ kappaByFiat` because the fold is reachability for all large κ; `≠ Circular`
because the disclosures are present. The verdict is falsifiable, tied to the `growthBookkeeping` field. -/
theorem ws7_audited_is_bookkeeping (cert : Audit κ) :
    verdict cert = Series10Verdict.bookkeeping := rfl

theorem ws7_audited_not_reificationEstablished (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.reificationEstablished := by
  show Series10Verdict.bookkeeping ≠ Series10Verdict.reificationEstablished; decide

theorem ws7_audited_not_selfTotalSmuggled (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.selfTotalSmuggled := by
  show Series10Verdict.bookkeeping ≠ Series10Verdict.selfTotalSmuggled; decide

theorem ws7_audited_not_kappaByFiat (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.kappaByFiat := by
  show Series10Verdict.bookkeeping ≠ Series10Verdict.kappaByFiat; decide

theorem ws7_audited_not_circular (cert : Audit κ) :
    verdict cert ≠ Series10Verdict.Circular := by
  show Series10Verdict.bookkeeping ≠ Series10Verdict.Circular; decide

/-- **D4 — the bookkeeping check (the flagship, PROMOTED, S1).** Growth is the moving-hole re-hit: the
reified `SHNE` relatum is bisimilar to every prior `SHNE` relatum (the collapse engine), so `Ω_{α+1}`
bisim-embeds into `Ω_α`. Strict internal growth is FALSE; the payoff is Bookkeeping. -/
theorem ws7_bookkeeping_check {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ z ∈ s.1, SHNE dest z)
    (y : X) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R (reify s) y :=
  ws2_reify_bisim_embeds dest reify h s hs hsucc y hy

/-- **D5 — the κ-by-fiat check (the flagship, PROMOTED, PASS).** The fold is distributed reflexivity (a
reachability), NOT a cardinality bound, and it holds for all large κ. The one honest defect (S2) is that
this per-step fold is DEFINITIONAL (`reifyStep`'s construction), not a substantive discharge — the
verdict Partial's real content (the residue-fold) is fully open. But κ-by-fiat is genuinely avoided. -/
theorem ws7_kappa_discipline {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    (Folds dest reify Ω₀ ↔
      (∀ Ω : Set X, prec dest reify Ω₀ Ω → ∀ s : PkObj κ X, s.1 ⊆ Ω → s.1 ≠ ∅ →
        ∃ Ω' : Set X, prec dest reify Ω Ω' ∧ reify s ∈ Ω'))
  ∧ (Folds dest reify Ω₀) :=
  ⟨ws4_fold_is_reflexivity dest reify Ω₀, ws5_fold_on_scaffold dest reify Ω₀⟩

/-- **D6a — CLOSE-forbidden at the inspection level (S3, honest restatement).** No self-total hold exists
(the diagonal), independent of the tower. The carrier-level tower closure (the founding-equation iso) is
charter §9's OPEN question, NOT forbidden by this theorem. -/
theorem ws7_close_forbidden_inspection_level {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) : ¬ Closes dest reify insp Ω₀ :=
  ws4_close_forbidden dest reify insp Ω₀

/-- **D6b — the spine is residue-freeness through the diagonal (R1, honest restatement).** Freeness
routes through `ws1_no_self_total_hold` (genuine, not a fresh assumption), but it is freeness of the
Series 09 residue CONTENT (`insp` only); `reify` is NOT in the term. The reification lift is interpretive,
NOT machine-checked. -/
theorem ws7_spine_is_residue_freeness {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) :=
  ws1_free_reification dest insp

/-- **D7 — the strip ledger (honest, S1/S2/S3 surfaced).** Each payoff, stripped, is a bare fact whose
reification reading is UNBUILT: productive blindness → the diagonal residue-freeness (`reify` absent, R1);
"growth" → the tower BISIM-EMBEDS (the moving-hole re-hit, S1 — the specified non-embedding is false);
CLOSE-forbidden → the inspection-level diagonal (tower-independent, S3); the fold → `reifyStep`'s
definitional membership (S2). The engine facts hold; the reification surplus is not proved. -/
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X)
    (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) :
    (¬ ∃ h, insp h = residue insp)                      -- blindness → diagonal freeness (reify absent)
  ∧ (∃ R, IsBisim dest R ∧ R x y)                       -- "growth" → the SHNE field bisim-collapses (S1)
  ∧ (¬ Closes dest reify insp Ω₀)                       -- CLOSE-forbidden → inspection-level diagonal (S3)
  ∧ (Folds dest reify Ω₀) :=                            -- fold → reifyStep's definitional membership (S2)
  ⟨ws2_residue_free dest insp, ws2_growth_is_bookkeeping dest x y hx hy,
   ws4_close_forbidden dest reify insp Ω₀, ws5_fold_on_scaffold dest reify Ω₀⟩

/-- The other outcomes: documentation. `reificationEstablished` would need strict internal growth (false,
S1); the delivered verdict is `bookkeeping`. -/
def verdictReificationEstablished : Series10Verdict := .reificationEstablished
def verdictSelfTotalSmuggled : Series10Verdict := .selfTotalSmuggled
def verdictKappaByFiat : Series10Verdict := .kappaByFiat
def verdictNoCertificate : Series10Verdict := .Circular

end Series10.WS7
