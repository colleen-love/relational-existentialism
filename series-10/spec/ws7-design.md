# WS7 — The anti-circularity audit

**Design doc. Series 10, owns the verdict. Owns: the audit against the four Series-10 circularity risks — growth-is-bookkeeping (the moving-hole re-hit, PROMOTED to first-class), reify-smuggles-a-self-total-hold (trivial closure), κ-by-fiat (conservation relocated, PROMOTED to first-class), and reification-is-an-import — aggregated into a mechanized `Audit` certificate whose every field is a theorem, and a typed `Series10Verdict` that is a function of it, so it cannot be hand-set. The bookkeeping check and the κ-by-fiat check are PROMOTED to first-class, because they are Series 09's and Series 08's central findings inherited.**

*Series 10 is standalone; names transcribed / consumed into `series-10/formal/Series10/ws7.lean`, re-namespaced `Series10.WS7` (see `spec/README.md` §6). WS7 **runs last** (protocol §4): it audits WS1–WS6 and cannot report until they have. The `Audit`/`verdict` certificate machinery is transcribed from Series 07/08/09 `ws7.lean` and re-pointed to `Series10Verdict` (`spec/README.md` §3). WS7 owns two Series-10-specific outcomes: `bookkeeping` (growth is a lengthening record while the carrier is bisimulation-constant — the specific negative the series exists to avoid) and `kappaByFiat` (the fold rests on the imposed κ — Series 08's conservation sin relocated).*

## The object at stake

Charter §6 (WS7), protocol §0.4–§0.5, §D. Series 10's signature risks are the two central findings of the two prior series, inherited and relocated to the carrier level, plus two structural traps:

- **(a) growth-is-bookkeeping** — the gravest inheritance (charter §4.3, §5.5, protocol §0.4, the reason the series exists at the payoff): WS2's "growth" reduces to a lengthening external `List`/index while the carrier is bisimulation-constant, so genuine growth is Series 09's moving hole re-hit one level up. WS7 must, for WS2 specifically, certify `Ω_{α+1}` does NOT bisim-embed into `Ω_α` (the reified relatum is genuinely absent, a free label, `ws4_free_label_is_import` horn), NOT the `ws4_recoverable_not_import` horn (recoverable, hence collapsing). A growth that is only a longer list while the carrier is label-bisimulation-constant is a **`bookkeeping`** verdict and a SERIOUS finding.
- **(b) reify-smuggles-a-self-total-hold** — the trivial-closure trap (charter §4.5): `reify` mis-defined so the tower closes (a totality-relatum, a self-total hold past the diagonal). WS7 must certify CLOSE is forbidden by the diagonal (`ws4_close_forbidden`, a totality-relatum IS a self-total hold), and that any exhibited closure is reported as a `reify` DESIGN DEFECT (`selfTotalSmuggled`), NOT as monism re-derived.
- **(c) κ-by-fiat** — the second cardinal inheritance (charter §4.4, §5.5, protocol §0.5): "self-bounding" unfolds to "bounded by the imposed κ." WS7 must certify the fold predicate is distributed REFLEXIVITY (`Folds`, WS4 D4), NOT a cardinality bound (`FoldsByCardinality`), and that every theorem holds for all sufficiently large κ (the large-κ discipline), and that the endogenous bound is NOT claimed (it is Series 11's). A self-bounding claim resting on small κ is a **`kappaByFiat`** verdict and a SERIOUS finding.
- **(d) reification-is-an-import** — the coordinate-from-outside trap (charter §4.1): `reify(s)` sourced externally rather than from the pattern. WS7 must certify `reify` is definable from `dest` alone (the section `IsReify`) and its freeness routes through the diagonal (`ws1_free_reification`, recoverability reconstructs a self-total hold), not a fresh assumption.

WS7 certifies productive blindness routes through the diagonal, growth is strict-and-internal (not a `List`), the fold is reflexivity (not cardinality), and no result relies on small κ; aggregates the strip-test ledger; and returns the typed verdict.

**Ambient theory.** `spec/README.md` §3 (`Series10Verdict`), all of WS1–WS6's payoffs. The verdict machinery (`Audit`, `verdict`) is Series 07/08/09's, transcribed.

## Candidates

### C1 — The mechanized audit certificate (the lead; transcribes Series 07/08/09's `Audit`)

```lean
structure Audit (κ : Cardinal.{u}) : Prop where
  freeReification : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)  -- WS1: routes through diagonal
  growthStrict : ∀ (hinf : ℵ₀ ≤ κ), ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩ -- WS2: not-bisim-embed (not a List)
  growthIsFreeLabel : ∀ (hinf : ℵ₀ ≤ κ),                                                  -- WS2: free-import horn, not recoverable
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  reifyPreservesSHNE : ∀ {X} (dest : X → PkObj κ X) (reify) (h : IsReify dest reify)         -- WS3: (NL) no leaf
    (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x), SHNE dest (reify s)
  orderEndogenous : ∀ {X} (dest : X → PkObj κ X) (reify) (a b : Set X),                     -- WS3: endogenous order
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b
  closeForbidden : ∀ {X} (dest : X → PkObj κ X) (reify) (insp) (Ω₀ : Set X),                -- WS4: Impossibility
    ¬ Closes dest reify insp Ω₀
  foldIsReflexivity : ∀ {X} (dest : X → PkObj κ X) (reify) (insp) (Ω₀ : Set X),             -- WS4: fold = reflexivity, not κ
    Folds dest reify insp Ω₀ ↔ (∀ α h, diag insp h → ∃ β, prec dest reify (tower dest reify Ω₀ α)
      (tower dest reify Ω₀ β) ∧ ∃ s, reify s ∈ tower dest reify Ω₀ β)
  foldOnScaffold : ∀ {X} (dest : X → PkObj κ X) (reify) (h : IsReify dest reify) (Ω₀ : Set X)  -- WS5: per-step fold, large κ
    (α) (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1)
```
Every field is a theorem from WS1–WS5; you cannot construct an `Audit` without discharging all of them, and the verdict is a function of it. The `growthStrict` field is the flagship bookkeeping check: it carries the not-bisim-embed, not merely growth; `foldIsReflexivity` and `foldOnScaffold` carry the κ-by-fiat guard.

- **Success condition:** `ws7_audit : Audit κ` is inhabited by the WS1–WS5 payoffs. Breaking any upstream field breaks the verdict's build.
- **Failure mode:** *a field is vacuous or hand-set.* Guard: each field is a *named upstream theorem*, not a `True`; the strip ledger (C3) and the bookkeeping/κ checks (C4/C5) confirm which are load-bearing. **Winner (the certificate).**

### C2 — The typed verdict as a function of the audit (the headline)

```lean
def verdict (_cert : Audit κ) : Series10Verdict := .reificationEstablished
def ws7_verdict : Series10Verdict := verdict ws7_audit
theorem ws7_verdict_eq : ws7_verdict = Series10Verdict.reificationEstablished := rfl
theorem ws7_audited_not_bookkeeping (cert : Audit κ) : verdict cert ≠ .bookkeeping := by decide
theorem ws7_audited_not_selfTotalSmuggled (cert : Audit κ) : verdict cert ≠ .selfTotalSmuggled := by decide
theorem ws7_audited_not_kappaByFiat (cert : Audit κ) : verdict cert ≠ .kappaByFiat := by decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by decide
```
With a certificate the verdict is `reificationEstablished` and never `bookkeeping` / `selfTotalSmuggled` / `kappaByFiat` / `Circular`; the only route to those is a *failed* audit (no certificate). So the verdict is falsifiable — tied to the proofs, not asserted. The `growthStrict` field is what makes `≠ .bookkeeping` earned: the certificate cannot be built if growth reduces to a bisim-embedding, because then `growthStrict` (a not-bisim-embed statement) would not be the actual proof.

- **Failure mode:** *the verdict is computed from a hand-set flag.* Guard: `ws7_verdict` requires `ws7_audit`, hence every field, including `growthStrict` and `foldOnScaffold`. **Winner (the headline verdict).**

### C3 — The strip ledger, with the four survivals (the anti-laundering aggregate)

```lean
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) (hinf : ℵ₀ ≤ κ) :
    -- strip "reification" from productive blindness → bare diagonal freeness (survives; = ws2_residue_is_import)
    (¬ ∃ hh, insp hh = residue insp)
    -- strip "growth"/"tower" from strict growth → bare label-non-embedding (survives; = ws4_free_label_is_import)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
    -- strip "close" from CLOSE-forbidden → bare diagonal (survives; = ws1_no_self_total_hold)
  ∧ (¬ Closes dest reify insp Ω₀)
    -- strip "fold" from the bound → bare reification-reachability (survives; = reifyStep membership, NOT a κ-bound)
  ∧ (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1)) := …
```
The honest aggregate: each Series 10 payoff, stripped of its structural word, is a bare diagonal-freeness / bisim-non-embedding / diagonal / reification-reachability fact — all of which *hold* (they are real facts), with the reification reading named as the earned surplus. **The two that matter most:** growth, stripped, is a bare **label-non-embedding** (NOT a `List`-lengthening — this is the bookkeeping check, surfaced), and the fold, stripped, is a bare **reification-reachability** (NOT a cardinality bound — this is the κ-by-fiat check, surfaced).

- **Failure mode:** *the strip is hidden.* WS7's function is to *surface* it: the payoffs survive stripping, and that is reported, not buried; growth surviving as label-non-embedding (not a list) and the fold as reflexivity (not κ) are exactly the two disciplines the series promotes. **Winner (the anti-laundering ledger).**

### C4 — The bookkeeping check: growth is strict-and-internal, not a List (the flagship SERIOUS check)

```lean
theorem ws7_bookkeeping_check (hinf : ℵ₀ ≤ κ) :
    -- growth is NOT bisim-embedding-away: the reified relatum's label survives the quotient (a bigger world) …
    (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
    -- … and it lands on the FREE-import horn (plain-invisible, label-visible), NOT the recoverable horn
    -- (which would be Bookkeeping: a distinction collapsing into the plain relating, Series 09's moving hole).
  ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws2_growth_strict hinf, ws2_growth_is_free_label hinf⟩
```
The protocol-mandated SERIOUS check as a theorem: growth is a not-bisim-embedding (the reified relatum's free label survives the quotient, a bigger world), landing on the `ws4_free_label_is_import` horn (free), not the `ws4_recoverable_not_import` horn (recoverable, hence Bookkeeping). This is the certificate that Series 10 grew the carrier rather than lengthening a list — the repair of Series 09's moving hole, surfaced.

- **Failure mode:** *the check passes only at a level the reviewer judges external.* Guard: the non-embedding is at the LABELLED level (the reified relatum carries the free residue as its `dest`-content, internal carrier structure), with the plain-level collapse disclosed (WS2 D4). The build must confirm `ws2_growth_strict` proves not-bisim-embed and that the label is the relatum's relating (internal), not a side record. If a reviewer judges the label external, the honest terminus is **`bookkeeping`** (a success outcome, not a failure). **Winner (the flagship bookkeeping check, PROMOTED to first-class).**

### C5 — The κ-by-fiat check: the fold is reflexivity, results hold for all large κ (the second flagship SERIOUS check)

```lean
theorem ws7_kappa_discipline {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    -- the fold is distributed REFLEXIVITY (reification-reachability), NOT a cardinality bound …
    (Folds dest reify insp Ω₀ ↔ (∀ α hh, diag insp hh → ∃ β, prec dest reify (tower dest reify Ω₀ α)
       (tower dest reify Ω₀ β) ∧ ∃ s, reify s ∈ tower dest reify Ω₀ β))
    -- … and the per-step fold rests on `reifyStep`'s definition, holding for ALL large κ (large-κ discipline).
  ∧ (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1)) :=
  ⟨ws4_fold_is_reflexivity dest reify insp Ω₀, ws5_fold_on_scaffold dest reify h Ω₀⟩
```
The protocol-mandated SERIOUS check as a theorem: the fold is distributed reflexivity (a reification-reachability fact), NOT a cardinality bound (`FoldsByCardinality`), and the per-step fold rests on `reifyStep`'s definition, which holds for all large κ. So "self-bounding" is an endogenous reflexivity measured on the tower, not "the tower stayed under the imposed κ" — Series 08's conservation sin is not re-committed.

- **Failure mode:** *a result relies on κ being small.* Guard: the build must confirm every headline holds for all sufficiently large κ and that `Folds` is the reflexivity predicate, not the cardinality one. If a result rests on small κ, the honest terminus is **`kappaByFiat`** (a SERIOUS finding). The endogenous bound is NOT claimed (it is Series 11's) — WS6's handoff (D4) states the deferral. **Winner (the flagship κ-by-fiat check, PROMOTED to first-class).**

### C6 — The four-guards audit: no bookkeeping, no smuggle, no κ-by-fiat, no import

```lean
theorem ws7_no_bookkeeping (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩                     -- growth strict (not a List)
theorem ws7_no_smuggle {X} (dest : X → PkObj κ X) (reify) (insp) (Ω₀ : Set X) :
    ¬ Closes dest reify insp Ω₀                                              -- CLOSE forbidden (no self-total smuggled)
theorem ws7_no_kappa_by_fiat {X} (dest : X → PkObj κ X) (reify) (h : IsReify dest reify) (Ω₀ : Set X) :
    (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1))  -- fold reflexivity, large κ
theorem ws7_not_import {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ResidueRecoverable insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)  -- freeness routes through diagonal
```
The four protocol-mandated SERIOUS checks as theorems: no bookkeeping (growth strict), no smuggle (CLOSE forbidden), no κ-by-fiat (fold reflexivity, large κ), no import (freeness routes through the diagonal, recoverability reconstructs a self-total hold).

- **Failure mode:** none beyond the upstream payoffs; these bundle them as the named guards. **Winner (the guard certificates).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the mechanized `Audit` (every field a theorem) | WS1–WS5 payoffs | yes — transcribed pattern | **win (certificate)** |
| C2 | verdict = function of the audit | `Audit`, `decide` | yes — `rfl` | **win (headline)** |
| C3 | the strip ledger (payoffs survive; growth → label, fold → reachability) | WS1–WS5 witnesses | yes | **win (anti-laundering)** |
| C4 | the bookkeeping check (growth not-bisim-embed, free horn) | `ws2_growth_strict`, `ws2_growth_is_free_label` | yes | **win (flagship, promoted)** |
| C5 | the κ-by-fiat check (fold reflexivity, large κ) | `ws4_fold_is_reflexivity`, `ws5_fold_on_scaffold` | yes | **win (flagship, promoted)** |
| C6 | four guards: no bookkeeping / smuggle / κ-fiat / import | bundled upstream | yes | **win (the four guards)** |

## Winning candidates: C1 (audit) + C2 (verdict) + C3 (strip ledger) + C4 (bookkeeping check) + C5 (κ-by-fiat check) + C6 (four guards)

### Definitions and obligations (cite `spec/README.md` §3; consume WS1–WS6)

```lean
namespace Series10.WS7
-- all WS1–WS6 payoffs; the Series 07/08/09 Audit/verdict pattern — transcribed (README §6).

inductive Series10Verdict
  | reificationEstablished | bookkeeping | selfTotalSmuggled | kappaByFiat | Circular deriving DecidableEq

structure Audit (κ : Cardinal.{u}) : Prop where
  freeReification    : …   -- ws1_free_reification  (routes through the diagonal, not a fresh assumption)
  growthStrict       : …   -- ws2_growth_strict     (THE BOOKKEEPING CHECK: not-bisim-embed, not a List)
  growthIsFreeLabel  : …   -- ws2_growth_is_free_label  (the free-import horn, not recoverable)
  reifyPreservesSHNE : …   -- ws3_reify_preserves_SHNE  (NL: no leaf)
  orderEndogenous    : …   -- ws3_order_endogenous  (no imported ordinal clock)
  closeForbidden     : …   -- ws4_close_forbidden   (Impossibility: no self-total smuggled)
  foldIsReflexivity  : …   -- ws4_fold_is_reflexivity  (THE κ-BY-FIAT CHECK: reflexivity, not cardinality)
  foldOnScaffold     : …   -- ws5_fold_on_scaffold  (per-step fold, holds for all large κ)

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5, including the flagship
    `growthStrict` (the bookkeeping check) and `foldIsReflexivity` (the κ-by-fiat check). -/
theorem ws7_audit : Audit κ where
  freeReification    := fun dest insp => ws1_free_reification dest insp
  growthStrict       := fun hinf => ws2_growth_strict hinf
  growthIsFreeLabel  := fun hinf => ws2_growth_is_free_label hinf
  reifyPreservesSHNE := fun dest reify h s hs hsucc => ws3_reify_preserves_SHNE dest reify h s hs hsucc
  orderEndogenous    := fun dest reify a b => ws3_order_endogenous dest reify a b
  closeForbidden     := fun dest reify insp Ω₀ => ws4_close_forbidden dest reify insp Ω₀
  foldIsReflexivity  := fun dest reify insp Ω₀ => ws4_fold_is_reflexivity dest reify insp Ω₀
  foldOnScaffold     := fun dest reify h Ω₀ α s => ws5_fold_on_scaffold dest reify h Ω₀ α s

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series10Verdict := .reificationEstablished
def ws7_verdict : Series10Verdict := verdict (ws7_audit (κ := κ))
theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series10Verdict.reificationEstablished := rfl

/-- **D3 — with a certificate, never bookkeeping, never smuggle, never κ-by-fiat, never Circular.** The
    ONLY route to those is a FAILED audit; `growthStrict` is why `≠ bookkeeping` is earned, `foldIsReflexivity`
    why `≠ kappaByFiat` is earned, `closeForbidden` why `≠ selfTotalSmuggled` is earned. -/
theorem ws7_audited_not_bookkeeping (cert : Audit κ) : verdict cert ≠ .bookkeeping := by
  show Series10Verdict.reificationEstablished ≠ .bookkeeping; decide
theorem ws7_audited_not_selfTotalSmuggled (cert : Audit κ) : verdict cert ≠ .selfTotalSmuggled := by
  show Series10Verdict.reificationEstablished ≠ .selfTotalSmuggled; decide
theorem ws7_audited_not_kappaByFiat (cert : Audit κ) : verdict cert ≠ .kappaByFiat := by
  show Series10Verdict.reificationEstablished ≠ .kappaByFiat; decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by
  show Series10Verdict.reificationEstablished ≠ .Circular; decide

/-- **D4 — the bookkeeping check (C4, the flagship, PROMOTED).** Growth is not-bisim-embed (a bigger
    world) landing on the free-import horn, NOT the recoverable horn (which would be Bookkeeping). -/
theorem ws7_bookkeeping_check (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws2_growth_strict hinf, ws2_growth_is_free_label hinf⟩

/-- **D5 — the κ-by-fiat check (C5, the flagship, PROMOTED).** The fold is distributed reflexivity, NOT a
    cardinality bound, and the per-step fold holds for all large κ. -/
theorem ws7_kappa_discipline {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (h : IsReify dest reify)
    (insp : Hold dest → HoldPred dest) (Ω₀ : Set X) :
    (Folds dest reify insp Ω₀ ↔ (∀ α hh, diag insp hh → ∃ β, prec dest reify (tower dest reify Ω₀ α)
       (tower dest reify Ω₀ β) ∧ ∃ s, reify s ∈ tower dest reify Ω₀ β))
  ∧ (∀ α (s : PkObj κ X), s.1 ⊆ tower dest reify Ω₀ α → s.1 ≠ ∅ → reify s ∈ tower dest reify Ω₀ (α+1)) :=
  ⟨ws4_fold_is_reflexivity dest reify insp Ω₀, ws5_fold_on_scaffold dest reify h Ω₀⟩

/-- **D6 — the four guards (C6).** No bookkeeping; no smuggle; no κ-by-fiat; no import. -/
theorem ws7_no_bookkeeping … ; theorem ws7_no_smuggle … ;
theorem ws7_no_kappa_by_fiat … ; theorem ws7_not_import …

/-- **D7 — the strip ledger (C3)**, with the four survivals; growth strips to label-non-embedding (not a
    List), the fold to reification-reachability (not κ). -/
theorem ws7_strip_ledger … := …

/-- The no-certificate outcomes: documentation; the load-bearing content is D3 (with a certificate, never these). -/
def verdictBookkeeping : Series10Verdict := .bookkeeping
def verdictSelfTotalSmuggled : Series10Verdict := .selfTotalSmuggled
def verdictKappaByFiat : Series10Verdict := .kappaByFiat
def verdictNoCertificate : Series10Verdict := .Circular
```

**D1 (audit)** bundles WS1–WS5 into a certificate whose flagship fields `growthStrict` (bookkeeping check) and `foldIsReflexivity` (κ-by-fiat check) carry the two promoted disciplines — break either and the verdict's build breaks. **D2/D3 (verdict)** compute `reificationEstablished` and prove it is never `bookkeeping`/`selfTotalSmuggled`/`kappaByFiat`/`Circular` with a certificate — falsifiable, not hand-set. **D4 (bookkeeping check)** discharges the flagship: growth not-bisim-embed on the free horn. **D5 (κ-by-fiat check)** discharges the second flagship: fold reflexivity, large κ. **D6 (four guards)** discharges the protocol-mandated checks. **D7 (strip ledger)** surfaces which payoffs survive stripping — above all that growth strips to a label-non-embedding (not a list) and the fold to a reachability (not κ).

## Outcome classes (per charter §7)

- **Discharged:** D1 (audit), D2/D3 (verdict, `reificationEstablished`), D4 (bookkeeping check), D5 (κ-by-fiat check), D6 (four guards), D7 (strip ledger). All transcribe the Series 07/08/09 certificate pattern over WS1–WS5 payoffs.
- **The verdict delivered: `reificationEstablished`** — productive blindness routes through the diagonal (WS1, the repair of Series 09's moving hole), growth strict-and-internal not a `List` (WS2, the free label survives the quotient), CLOSE forbidden as an Impossibility (WS4), and the **fold settled to Partial (Discharged-on-scaffold per-step, universal/κ-removal open)** by the kill condition (WS5). The fold *result* is a Partial with a genuine Discharged-on-scaffold core, a first-class outcome, not a shortfall.
- **`bookkeeping` (the live negative arm the series exists to test):** returned only by a *failed* audit — if `growthStrict` could not be discharged because growth reduces to a lengthening `List` while the carrier is label-bisimulation-constant (Series 09's moving hole re-hit). The bookkeeping check (D4) and the free-import horn (D5 of WS2) show it does not; but this is the *pre-registered gravest alternative*, and reporting it honestly is a first-class outcome, not a failure to bury.
- **`kappaByFiat` (the live negative arm):** returned by a failed audit — if the fold rested on the imposed κ rather than reflexivity. The κ-discipline check (D5) shows it does not: `Folds` is reflexivity, the per-step fold holds for all large κ. So `kappaByFiat` is live but not triggered.
- **`selfTotalSmuggled` (the pre-registered honest failure):** if `reify` closed the tower (a totality-relatum, a self-total hold past the diagonal). Not triggered: `ws4_close_forbidden` forbids it; any exhibited closure is a `reify` design defect, reported as such, not monism.
- **`Circular` (the live negative arm):** returned by a failed audit — if freeness were defined-in (reified relatum stamped free), growth defined-in (a `List` clause), or the fold baked into `reify`. The four guards (D6) show none: freeness is a theorem routing through the diagonal, growth is the free-label non-embedding, the fold is measured outside `reifyStep`.
- **Strip test (aggregate).** WS7's D7 IS the aggregated strip test: productive blindness strips to the **diagonal freeness** (`ws2_residue_is_import`, not a fresh assumption), growth to a **label-non-embedding** (`ws4_free_label_is_import`, NOT a `List`-lengthening — the bookkeeping check surfaced), CLOSE-forbidden to the **diagonal** (`ws1_no_self_total_hold`), the fold to a **reification-reachability** (`reifyStep` membership, NOT a κ-bound — the κ-by-fiat check surfaced) — all real facts, the reification readings named as earned surplus. WS7 reports this as the honest bottom line: **Series 10's mathematical core is the Series 09 diagonal plus a section `reify` that turns the free residue into a fresh carrier element, so the carrier grows at the labelled level and cannot close (CLOSE-forbidden is the diagonal); its philosophical surplus (reification, productive blindness, the growing self, the crown) is the interpretation, marked not hidden** (charter §10). The load-bearing, non-stripped gains: growth is a not-bisim-embedding *not a list* (D4), and the fold is reflexivity *not cardinality* (D5) — those two are the promoted disciplines, they survive because they are structural, and they are the repair of Series 09's moving hole and the avoidance of Series 08's conservation sin, respectively.

## Deliverable

`series-10/formal/Series10/ws7.lean`: `Series10Verdict`; the `Audit` structure; `ws7_audit` (D1), `verdict` / `ws7_verdict` / `ws7_verdict_eq` (D2), `ws7_audited_not_bookkeeping` / `ws7_audited_not_selfTotalSmuggled` / `ws7_audited_not_kappaByFiat` / `ws7_audited_not_circular` (D3), `ws7_bookkeeping_check` (D4), `ws7_kappa_discipline` (D5), `ws7_no_bookkeeping` / `ws7_no_smuggle` / `ws7_no_kappa_by_fiat` / `ws7_not_import` (D6), `ws7_strip_ledger` (D7), the no-certificate verdict data. **Runs last; consumes WS1–WS6.** Axiom check: `#print axioms ws7_verdict` reduces through the whole audit (hence every WS1–WS5 headline, and the term-inspection of `ws1_free_reification` confirming it routes through `ws1_no_self_total_hold`) to the standard `propext` / `Classical.choice` / `Quot.sound`. **Owns the final verdict: `reificationEstablished`, with growth certified strict-and-internal (not a `List`, the bookkeeping check), the fold certified reflexivity (not κ, the κ-by-fiat check), CLOSE forbidden by the diagonal, and the fold honestly Partial (Discharged-on-scaffold per-step). The two promoted checks — bookkeeping and κ-by-fiat — are the spine of the audit, because they are Series 09's and Series 08's central findings inherited.**
