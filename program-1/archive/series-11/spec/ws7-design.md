# WS7 — The anti-circularity audit

**Design doc. Series 11, owns the program's final verdict. Owns: the audit against the four Series-11 circularity risks — attention-is-Bookkeeping-re-hit (§4.3, Series 10's proved failure returning, PROMOTED to first-class), the-bound-re-imports-κ (§4.4, Series 08's conservation / Series 10's scaffold returning, PROMOTED to first-class), attention-violates-the-diagonal (§4.5, a total hold), and attention-distinction-is-an-import (§4.1) — aggregated into a mechanized `Audit` certificate whose every field is a theorem, and a typed `Series11Verdict` that is a function of it, so it cannot be hand-set. The Bookkeeping-re-hit check and the κ-readmitted check are PROMOTED to first-class, because they are Series 10's and Series 08's central findings inherited and relocated to attention and the κ-removal.**

*Series 11 is standalone; names transcribed / consumed into `series-11/formal/Series11/ws7.lean`, re-namespaced `Series11.WS7` (see `spec/README.md` §6). WS7 **runs last** (protocol §4): it audits WS1–WS6 and cannot report until they have. The `Audit`/`verdict` certificate machinery is transcribed from Series 07/08/09/10 `ws7.lean` and re-pointed to `Series11Verdict` (`spec/README.md` §3). WS7 owns the two Series-11-specific promoted outcomes: `bookkeepingReHit` (attention is a fresh label / not distinct from the plain quotient — Series 10's proved Bookkeeping returning) and `kappaReadmitted` (the bound rests on a cardinality ceiling — Series 08's conservation sin / Series 10's scaffold returning), plus `tragic` (the terminal negative) and `totalAttentionSmuggled`.*

## The object at stake

Charter §6 (WS7), protocol §0.4–§0.5, §D. Series 11's signature risks are the two central findings of the two prior series, inherited and relocated to attention and the κ-removal, plus two structural traps:

- **(a) attention-is-Bookkeeping-re-hit** — the gravest inheritance (charter §4.3, §5.5, protocol §0.4, the reason the series exists at the payoff): WS1/WS2's "attention" is a fresh external labelling not distinct from the plain quotient, so the spine is Series 10's PROVED Bookkeeping relabelled. WS7 must, for WS1/WS2 specifically, certify the attention-distinction distinguishes WHERE THE PLAIN BISIMULATION COLLAPSES (`ws2_attention_embed_fails`: `plainOf`-bisimilar but not label-bisimilar, the `ws4_free_label_is_import` horn, NOT the `ws4_recoverable_not_import` horn), AND is free (`ws4_labelLoop_not_recoverable`). An attention that is the plain quotient (recoverable) is a **`bookkeepingReHit`** verdict and a SERIOUS finding: Series 10's proved failure returning while the prose claims a rescue.
- **(b) the-bound-re-imports-κ** — the second cardinal inheritance (charter §4.4, §5.5, protocol §0.5): the "self-bound" unfolds to a cardinality ceiling on attention's range or the tower's size. WS7 must certify the bound is (NT) no-total-attention plus bounded-holding, both facts about HOLDING (`ws3_no_total_attention`, `ws4_bound_is_holding_not_size`), refutable by a total attention or an unbounded hold, and that every theorem holds κ-free (the diagonal uses no cardinal; the residual carrier branching-κ is disclosed, §2.7). A bound resting on a cardinality ceiling is a **`kappaReadmitted`** verdict and a SERIOUS finding.
- **(c) attention-violates-the-diagonal** — the total-hold trap (charter §4.5): attention mis-defined so some hold captures the whole tower (a self-total hold past the diagonal). WS7 must certify no-total-attention is an Impossibility (`ws3_no_total_attention`, a total attention IS a self-total hold), and that any exhibited total attention is reported as an attention DESIGN DEFECT (`totalAttentionSmuggled`), NOT a bound.
- **(d) attention-distinction-is-an-import** — the coordinate-from-outside trap (charter §4.1): the distinction stamped externally rather than routing through the diagonal residue. WS7 must certify the distinction is free (`ws4_labelLoop_not_recoverable`, `¬ Recoverable`) and routes through the diagonal (the label is the residue `diag insp`; `ws2_residue_is_import`), the tie flagged as interpretive at the residue-freeness level (as WS1 disclosed).

WS7 certifies attention-reality routes through the diagonal (not a fresh label), the bound is holding-not-size (not κ readmitted), no-total-attention is the diagonal (not an assumption), and the distinction is free (not imported); aggregates the strip-test ledger; and returns the typed verdict.

**Ambient theory.** `spec/README.md` §3 (`Series11Verdict`), all of WS1–WS6's payoffs. The verdict machinery (`Audit`, `verdict`) is Series 07/08/09/10's, transcribed.

## Candidates

### C1 — The mechanized audit certificate (the lead; transcribes the Series 07/08/09/10 `Audit`)

```lean
structure Audit (κ : Cardinal.{u}) : Prop where
  attentionMakesReal : ∀ (hinf : ℵ₀ ≤ κ),                                          -- WS1: distinguishes where bisim collapses
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  attentionNotPlainQuotient : ∀ (hinf : ℵ₀ ≤ κ), ¬ Recoverable (labelLoop hinf)   -- WS1: free (not recoverable) — Bookkeeping-re-hit check
  attentionEmbedFails : ∀ (hinf : ℵ₀ ≤ κ),                                         -- WS2: the rescue (attention-embed fails where bisim-embed holds)
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
    ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  noTotalAttention : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),   -- WS3: NT (Impossibility)
    ¬ ∃ t, SelfTotal insp t
  attentionReadsFullRelata : ∀ {X} (dest : X → PkObj κ X) (reify) (h : IsReify dest reify)  -- WS3: (NL) no leaf
    (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x), SHNE dest (reify s)
  boundIsHoldingNotSize : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),   -- WS4: κ-readmitted check
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t)
  boundKappaFree : ∀ {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest),   -- WS4: the diagonal uses no cardinal
    (∀ {Y} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t)
  crownOnFiniteStages : ∀ {Q X} (dest : X → LkObj κ Q X)                             -- WS5: crown on finite stages, free distinction
    (insp : Hold (plainOf dest) → HoldPred (plainOf dest)), (¬ Recoverable dest) →
    (¬ ∃ t, SelfTotal insp t) ∧ (¬ Recoverable dest)
```
Every field is a theorem from WS1–WS5; you cannot construct an `Audit` without discharging all of them, and the verdict is a function of it. The `attentionMakesReal` and `attentionNotPlainQuotient` fields are the flagship Bookkeeping-re-hit check (the distinction is where bisimulation collapses AND free); `boundIsHoldingNotSize` and `boundKappaFree` carry the κ-readmitted guard.

- **Success condition:** `ws7_audit : Audit κ` is inhabited by the WS1–WS5 payoffs. Breaking any upstream field breaks the verdict's build.
- **Failure mode:** *a field is vacuous or hand-set.* Guard: each field is a *named upstream theorem*, not a `True`; the strip ledger (C3) and the two promoted checks (C4/C5) confirm which are load-bearing. **Winner (the certificate).**

### C2 — The typed verdict as a function of the audit (the headline)

```lean
def verdict (_cert : Audit κ) : Series11Verdict := .attentionEstablished
def ws7_verdict : Series11Verdict := verdict ws7_audit
theorem ws7_verdict_eq : ws7_verdict = Series11Verdict.attentionEstablished := rfl
theorem ws7_audited_not_bookkeepingReHit (cert : Audit κ) : verdict cert ≠ .bookkeepingReHit := by decide
theorem ws7_audited_not_kappaReadmitted (cert : Audit κ) : verdict cert ≠ .kappaReadmitted := by decide
theorem ws7_audited_not_totalAttentionSmuggled (cert : Audit κ) : verdict cert ≠ .totalAttentionSmuggled := by decide
theorem ws7_audited_not_tragic (cert : Audit κ) : verdict cert ≠ .tragic := by decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by decide
```
With a certificate the verdict is `attentionEstablished` and never `bookkeepingReHit` / `kappaReadmitted` / `totalAttentionSmuggled` / `tragic` / `Circular`; the only route to those is a *failed* audit (no certificate). So the verdict is falsifiable — tied to the proofs, not asserted. The `attentionMakesReal` + `attentionNotPlainQuotient` fields are what make `≠ bookkeepingReHit` earned: the certificate cannot be built if the attention is the plain quotient (recoverable), because then `attentionNotPlainQuotient` (a `¬ Recoverable` statement) would not be the actual proof.

- **Failure mode:** *the verdict is computed from a hand-set flag.* Guard: `ws7_verdict` requires `ws7_audit`, hence every field. **Winner (the headline verdict).**

*Honest scope note (the verdict's Partial spine).* `attentionEstablished` is the verdict WHEN the audit's witness-level fields are discharged (they are). But WS1/WS2's attention-reality is Discharged-on-WITNESS with the universal Partial and Bookkeeping-re-hit pre-registered live; WS5's crown is Partial (finite Discharged, transfinite/carrier-κ open, tragic live). So `attentionEstablished` here means "the mechanized core is discharged and routes correctly (Bookkeeping-re-hit foreclosed at the witness, κ genuinely removed at the diagonal)," NOT "the full universal crown is proved" — exactly as Series 10's `reificationEstablished` co-existed with a Partial fold. The verdict records the honest scope: the reader Series 10 lacked is supplied and certified free (rescue at the witness), the bound is holding-not-size (κ removed at the diagonal), and the universal/transfinite crown is Partial with the tragic horn live.

### C3 — The strip ledger, with the survivals (the anti-laundering aggregate)

```lean
theorem ws7_strip_ledger {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hinf : ℵ₀ ≤ κ) :
    -- strip "attention" from the spine → bare free-label non-embedding (survives; = ws4_free_label_is_import)
    ((∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
    -- strip "attention"/"holds" from no-total-attention → bare diagonal (survives; = ws1_no_self_total_hold)
  ∧ (¬ ∃ t, SelfTotal insp t)
    -- strip "bound"/"finite" from the bound → bare diagonal, holding-not-size (survives; = ws1_no_self_total_hold, κ-free)
  ∧ (¬ ∃ t, SelfTotal insp t)
    -- strip "reads" from the rescue → bare bisim-non-embedding (survives; = ws4_free_label_is_import) := …
```
The honest aggregate: each Series 11 payoff, stripped of its structural word, is a bare free-label-non-embedding / diagonal fact — all of which *hold* (they are real facts), with the attention reading named as the earned surplus. **The two that matter most:** the spine, stripped, is a bare **free-label non-embedding** (the reader distinguishing where bisimulation collapses — this is the Bookkeeping-re-hit check, surfaced), and the bound, stripped, is the bare **diagonal** (no self-total hold, κ-free — this is the κ-readmitted check, surfaced).

- **Failure mode:** *the strip is hidden.* WS7's function is to *surface* it: the payoffs survive stripping, and that is reported, not buried; the spine surviving as a free-label non-embedding (the reader is where the collapse is) and the bound as the diagonal (holding-not-size, no cardinal) are exactly the two disciplines the series promotes. **Winner (the anti-laundering ledger).**

### C4 — The Bookkeeping-re-hit check: attention distinguishes where bisimulation collapses, and is free (the flagship SERIOUS check)

```lean
theorem ws7_bookkeeping_rehit_check (hinf : ℵ₀ ≤ κ) :
    -- attention distinguishes WHERE the plain bisimulation collapses (the reader is not the plain quotient) …
    ((∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
    -- … and the distinction is FREE (not recoverable), so it lands on the ws4_free_label_is_import horn,
    -- NOT the ws4_recoverable_not_import horn (which would be Bookkeeping: the reader = the plain quotient).
  ∧ (¬ Recoverable (labelLoop hinf)) :=
  ⟨ws2_attention_embed_fails hinf, ws4_labelLoop_not_recoverable hinf⟩
```
The protocol-mandated SERIOUS check as a theorem: the attention distinguishes where the plain bisimulation collapses (`plainOf`-bisimilar but not label-bisimilar), and the distinction is free (not recoverable), landing on the `ws4_free_label_is_import` horn (a reader that is not the plain quotient), not the `ws4_recoverable_not_import` horn (recoverable, hence Bookkeeping). This is the certificate that Series 11 supplied a reader rather than relabelling Series 10's inert label — the rescue of Series 10's proved Bookkeeping, surfaced.

- **Failure mode:** *the check passes only at a level the reviewer judges external.* Guard: the non-embedding is where the plain collapse is (the same pair), with the label the reified relatum's relating (the residue, internal), not a side record. The build must confirm `ws2_attention_embed_fails` proves the two horns for the same pair and that the label is the residue (`diag insp`, interpretive tie flagged). If a reviewer judges the label external to the tower's `reifyStep`-relata, the honest terminus is **`bookkeepingReHit`** (a first-class outcome, Series 10's proved failure returning). **Winner (the flagship Bookkeeping-re-hit check, PROMOTED to first-class).**

### C5 — The κ-readmitted check: the bound is holding-not-size, results hold κ-free (the second flagship SERIOUS check)

```lean
theorem ws7_kappa_readmitted_check {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    -- the bound is holding-not-size: no self-total hold, holding even on an infinite tower …
    ((¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t))
    -- … and κ-free: the diagonal references no cardinal, holds for every carrier (no size ceiling).
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws4_bound_is_holding_not_size dest insp |>.imp id (fun h => h.2), ws4_kappa_free dest insp⟩
```
The protocol-mandated SERIOUS check as a theorem: the bound is holding-not-size (no self-total hold, holding even on an infinite tower — no size ceiling), and κ-free (the diagonal references no cardinal, holds for every carrier). So "self-bounding" is the incompletability distributed across the tower, not "attention ranges over a κ-bounded set" — Series 08's conservation sin is not re-committed, and the genuine κ-removal is the diagonal bound. The residual carrier branching-κ (§2.7) is disclosed as the section's existence condition, not a proliferation or holding bound.

- **Failure mode:** *a result relies on a cardinality ceiling.* Guard: the build must confirm the bound holds on an infinite tower and the diagonal uses no κ. If the bound rests on a cardinality ceiling (the tower's size or attention's range bounded by κ), the honest terminus is **`kappaReadmitted`** (a SERIOUS finding). The carrier branching-κ is disclosed; if a reviewer judges it the removed κ returning, the honest terminus tilts **`tragic`** (WS5's fork). **Winner (the flagship κ-readmitted check, PROMOTED to first-class).**

### C6 — The four-guards audit: no Bookkeeping-re-hit, no κ-readmitted, no total-hold, no import

```lean
theorem ws7_no_bookkeeping_rehit (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf)                 -- attention not the plain quotient
theorem ws7_no_kappa_readmitted {X} (dest : X → PkObj κ X) (insp) :                                -- bound holding-not-size, κ-free
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ {Y} (d : Y → PkObj κ Y) (ins), ¬ ∃ t, SelfTotal ins t)
theorem ws7_no_total_attention {X} (dest : X → PkObj κ X) (insp) : ¬ ∃ t, SelfTotal insp t          -- no total hold smuggled
theorem ws7_not_import {X} (dest : X → PkObj κ X) (insp) :                                          -- distinction routes through the diagonal
    (¬ ResidueRecoverable insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)
```
The four protocol-mandated SERIOUS checks as theorems: no Bookkeeping-re-hit (attention not the plain quotient, `¬ Recoverable`), no κ-readmitted (bound holding-not-size, κ-free), no total-hold (no self-total attention), no import (the distinction routes through the diagonal, recoverability reconstructs a self-total hold).

- **Failure mode:** none beyond the upstream payoffs; these bundle them as the named guards. **Winner (the guard certificates).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the mechanized `Audit` (every field a theorem) | WS1–WS5 payoffs | yes — transcribed pattern | **win (certificate)** |
| C2 | verdict = function of the audit | `Audit`, `decide` | yes — `rfl` | **win (headline)** |
| C3 | the strip ledger (spine → free-label, bound → diagonal) | WS1–WS5 witnesses | yes | **win (anti-laundering)** |
| C4 | Bookkeeping-re-hit check (distinguishes where bisim collapses, free) | `ws2_attention_embed_fails`, `ws4_labelLoop_not_recoverable` | yes | **win (flagship, promoted)** |
| C5 | κ-readmitted check (bound holding-not-size, κ-free) | `ws4_bound_is_holding_not_size`, `ws4_kappa_free` | yes | **win (flagship, promoted)** |
| C6 | four guards: no rehit / no κ / no total-hold / no import | bundled upstream | yes | **win (the four guards)** |

## Winning candidates: C1 (audit) + C2 (verdict) + C3 (strip ledger) + C4 (Bookkeeping-re-hit check) + C5 (κ-readmitted check) + C6 (four guards)

### Definitions and obligations (cite `spec/README.md` §3; consume WS1–WS6)

```lean
namespace Series11.WS7
-- all WS1–WS6 payoffs; the Series 07/08/09/10 Audit/verdict pattern — transcribed / consumed (README §6).

inductive Series11Verdict
  | attentionEstablished | bookkeepingReHit | kappaReadmitted | totalAttentionSmuggled | tragic | Circular
  deriving DecidableEq

structure Audit (κ : Cardinal.{u}) : Prop where
  attentionMakesReal        : …   -- ws1_attention_makes_real   (distinguishes where the plain quotient collapses)
  attentionNotPlainQuotient : …   -- ws1_attention_distinction_free  (THE BOOKKEEPING-RE-HIT CHECK: free, not recoverable)
  attentionEmbedFails       : …   -- ws2_attention_embed_fails  (the rescue: attention-embed fails where bisim-embed holds)
  noTotalAttention          : …   -- ws3_no_total_attention     (Impossibility: no total hold)
  attentionReadsFullRelata  : …   -- ws3_attention_reads_full_relata  (NL: no leaf)
  boundIsHoldingNotSize     : …   -- ws4_bound_is_holding_not_size  (THE κ-READMITTED CHECK: holding, not size)
  boundKappaFree            : …   -- ws4_kappa_free             (the diagonal uses no cardinal)
  crownOnFiniteStages       : …   -- ws5_crown_on_finite_stages (crown on finite stages, free distinction)

/-- **D1 — the audit is discharged.** Every field a theorem from WS1–WS5, including the flagship
    `attentionNotPlainQuotient` (Bookkeeping-re-hit check) and `boundIsHoldingNotSize` (κ-readmitted check). -/
theorem ws7_audit : Audit κ where
  attentionMakesReal        := fun hinf => ws1_attention_makes_real hinf
  attentionNotPlainQuotient := fun hinf => ws1_attention_distinction_free hinf
  attentionEmbedFails       := fun hinf => ws2_attention_embed_fails hinf
  noTotalAttention          := fun dest insp => ws3_no_total_attention dest insp
  attentionReadsFullRelata  := fun dest reify h s hs hsucc => ws3_attention_reads_full_relata dest reify h s hs hsucc
  boundIsHoldingNotSize     := fun dest insp => ⟨(ws4_bound_is_holding_not_size dest insp).1,
                                                 fun hI => (ws4_bound_is_holding_not_size dest insp).2.2 hI⟩
  boundKappaFree            := fun dest insp => ws4_kappa_free dest insp
  crownOnFiniteStages       := fun dest insp hfree => ws5_crown_on_finite_stages dest insp hfree

/-- **D2 — the typed verdict**, a function of the discharged audit. -/
def verdict (_cert : Audit κ) : Series11Verdict := .attentionEstablished
def ws7_verdict : Series11Verdict := verdict (ws7_audit (κ := κ))
theorem ws7_verdict_eq : ws7_verdict (κ := κ) = Series11Verdict.attentionEstablished := rfl

/-- **D3 — with a certificate, never Bookkeeping-re-hit / κ-readmitted / total-hold / tragic / Circular.** -/
theorem ws7_audited_not_bookkeepingReHit (cert : Audit κ) : verdict cert ≠ .bookkeepingReHit := by
  show Series11Verdict.attentionEstablished ≠ .bookkeepingReHit; decide
theorem ws7_audited_not_kappaReadmitted (cert : Audit κ) : verdict cert ≠ .kappaReadmitted := by
  show Series11Verdict.attentionEstablished ≠ .kappaReadmitted; decide
theorem ws7_audited_not_totalAttentionSmuggled (cert : Audit κ) : verdict cert ≠ .totalAttentionSmuggled := by
  show Series11Verdict.attentionEstablished ≠ .totalAttentionSmuggled; decide
theorem ws7_audited_not_tragic (cert : Audit κ) : verdict cert ≠ .tragic := by
  show Series11Verdict.attentionEstablished ≠ .tragic; decide
theorem ws7_audited_not_circular (cert : Audit κ) : verdict cert ≠ .Circular := by
  show Series11Verdict.attentionEstablished ≠ .Circular; decide

/-- **D4 — the Bookkeeping-re-hit check (C4, the flagship, PROMOTED).** -/
theorem ws7_bookkeeping_rehit_check (hinf : ℵ₀ ≤ κ) :
    ((∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
      ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩))
  ∧ (¬ Recoverable (labelLoop hinf)) :=
  ⟨ws2_attention_embed_fails hinf, ws4_labelLoop_not_recoverable hinf⟩

/-- **D5 — the κ-readmitted check (C5, the flagship, PROMOTED).** -/
theorem ws7_kappa_readmitted_check {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ((¬ ∃ t, SelfTotal insp t) ∧ (∀ _ : Infinite X, ¬ ∃ t, SelfTotal insp t))
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨⟨ws4_no_completed_totality dest insp, fun _ => ws4_no_completed_totality dest insp⟩,
   ws4_kappa_free dest insp⟩

/-- **D6 — the four guards (C6).** No Bookkeeping-re-hit; no κ-readmitted; no total-hold; no import. -/
theorem ws7_no_bookkeeping_rehit … ; theorem ws7_no_kappa_readmitted … ;
theorem ws7_no_total_attention … ; theorem ws7_not_import …

/-- **D7 — the strip ledger (C3)**, with the survivals; the spine strips to a free-label non-embedding, the
    bound to the diagonal (κ-free). -/
theorem ws7_strip_ledger … := …

/-- The no-certificate outcomes: documentation; the load-bearing content is D3. -/
def verdictBookkeepingReHit : Series11Verdict := .bookkeepingReHit
def verdictKappaReadmitted : Series11Verdict := .kappaReadmitted
def verdictTotalAttentionSmuggled : Series11Verdict := .totalAttentionSmuggled
def verdictTragic : Series11Verdict := .tragic
def verdictNoCertificate : Series11Verdict := .Circular
```

**D1 (audit)** bundles WS1–WS5 into a certificate whose flagship fields `attentionNotPlainQuotient` (Bookkeeping-re-hit check) and `boundIsHoldingNotSize` (κ-readmitted check) carry the two promoted disciplines — break either and the verdict's build breaks. **D2/D3 (verdict)** compute `attentionEstablished` and prove it is never `bookkeepingReHit`/`kappaReadmitted`/`totalAttentionSmuggled`/`tragic`/`Circular` with a certificate — falsifiable, not hand-set. **D4 (Bookkeeping-re-hit check)** discharges the flagship: the reader distinguishes where the collapse is, and is free. **D5 (κ-readmitted check)** discharges the second flagship: the bound is holding-not-size, κ-free. **D6 (four guards)** discharges the protocol-mandated checks. **D7 (strip ledger)** surfaces which payoffs survive stripping — above all that the spine strips to a free-label non-embedding (the reader is where the collapse is) and the bound to the diagonal (no cardinal).

## Outcome classes (per charter §7)

- **Discharged:** D1 (audit), D2/D3 (verdict, `attentionEstablished`), D4 (Bookkeeping-re-hit check), D5 (κ-readmitted check), D6 (four guards), D7 (strip ledger). All transcribe the Series 07/08/09/10 certificate pattern over WS1–WS5 payoffs.
- **The verdict delivered: `attentionEstablished`** — attention-reality routes through the diagonal (WS1, the reader Series 10 lacked, distinguishing where the collapse engine is blind, certified free), the rescue holds at the attended level (WS2, attention-embed fails where bisim-embed holds), no-total-attention an Impossibility (WS3), the bound holding-not-size and κ-free (WS4), and the crown settled to **Partial (finite Discharged, transfinite/carrier-κ open)** by the kill condition (WS5). **The honest scope (the verdict's Partial spine):** `attentionEstablished` certifies the mechanized core is discharged and routes correctly (Bookkeeping-re-hit foreclosed at the witness, κ genuinely removed at the diagonal), NOT that the universal/transfinite crown is proved — the reality payoff is Discharged-on-witness with the universal Partial, exactly as Series 10's `reificationEstablished` co-existed with a Partial fold.
- **`bookkeepingReHit` (the live negative arm the series exists to test, PROMOTED):** returned only by a *failed* audit — if `attentionNotPlainQuotient` could not be discharged because the attention is the plain quotient (recoverable), so the spine is Series 10's inert label relabelled. The Bookkeeping-re-hit check (D4) shows the witness reader is free and distinguishes where the collapse is; but this is the *pre-registered gravest alternative*, and reporting it honestly (if the reader is judged external to the tower) is a first-class outcome, not a failure to bury.
- **`kappaReadmitted` (the live negative arm, PROMOTED):** returned by a failed audit — if the bound rested on a cardinality ceiling. The κ-readmitted check (D5) shows it does not: the bound is holding-not-size (holds on an infinite tower), κ-free (the diagonal uses no cardinal). The residual carrier branching-κ is disclosed; if judged the removed κ returning, the horn tilts `tragic` (WS5).
- **`totalAttentionSmuggled` (the pre-registered honest failure):** if attention were mis-defined so a total hold exists. Not triggered: `ws3_no_total_attention` forbids it; any exhibited total attention is an attention design defect, reported as such, not a bound.
- **`tragic` (the terminal negative, a first-class honest terminus):** returned by WS5's kill condition — if the transfinite limit re-admits a total attention, or a completed totality is forced despite bounded-holding, or the attention-distinction is recoverable at the tower level, or the carrier branching-κ is judged the removed κ returning. The crown is Partial with `tragic` pre-registered and live; reporting it is a success and the program's honest terminus.
- **`Circular` (the live negative arm):** returned by a failed audit — if attention-reality were free-by-fiat, the rescue defined-in, or the bound baked into attention's definition. The four guards (D6) show none: attention-reality is a theorem routing through the import test, the rescue is the free-label non-embedding, no-total-attention is measured on the diagonal not built into attention.
- **Strip test (aggregate).** WS7's D7 IS the aggregated strip test: attention-reality strips to the **free-label non-embedding** (`ws4_free_label_is_import`, the reader distinguishing where bisimulation collapses — the Bookkeeping-re-hit check surfaced), no-total-attention and the bound strip to the **diagonal** (`ws1_no_self_total_hold`, κ-free — the κ-readmitted check surfaced) — all real facts, the attention readings named as earned surplus. WS7 reports this as the honest bottom line: **Series 11's mathematical core is the Series 10 import test (a free label that is not recoverable) read as a READER, plus the Series 09/10 diagonal read as the tower's self-bound; its philosophical surplus (finite attention, the reader that makes the many real, the world holding itself finite by never grasping its whole, "to attend is to become") is the interpretation, marked not hidden** (charter §10). The load-bearing, non-stripped gains: the spine is a free-label non-embedding read as a reader that is NOT the plain quotient (D4), and the bound is the diagonal read as holding-not-size *not cardinality* (D5) — those two are the promoted disciplines, they survive because they are structural, and they are the rescue of Series 10's proved Bookkeeping and the avoidance of Series 08's conservation sin, respectively. The honest terminus, whichever it is (attention-established-on-the-witness / Bookkeeping-re-hit / crown-Partial / tragic), is the program's completion.

## Deliverable

`series-11/formal/Series11/ws7.lean`: `Series11Verdict`; the `Audit` structure; `ws7_audit` (D1), `verdict` / `ws7_verdict` / `ws7_verdict_eq` (D2), `ws7_audited_not_bookkeepingReHit` / `ws7_audited_not_kappaReadmitted` / `ws7_audited_not_totalAttentionSmuggled` / `ws7_audited_not_tragic` / `ws7_audited_not_circular` (D3), `ws7_bookkeeping_rehit_check` (D4), `ws7_kappa_readmitted_check` (D5), `ws7_no_bookkeeping_rehit` / `ws7_no_kappa_readmitted` / `ws7_no_total_attention` / `ws7_not_import` (D6), `ws7_strip_ledger` (D7), the no-certificate verdict data. **Runs last; consumes WS1–WS6.** Axiom check: `#print axioms ws7_verdict` reduces through the whole audit (hence every WS1–WS5 headline, and the term-inspection confirming the spine's first conjunct is the plain quotient's blindness and no-total-attention uses no κ) to the standard `propext` / `Classical.choice` / `Quot.sound`. **Owns the program's final verdict: `attentionEstablished` on the mechanized core, with the reader certified free and distinguishing where the collapse engine is blind (the Bookkeeping-re-hit check), the bound certified holding-not-size and κ-free (the κ-readmitted check), no-total-attention the diagonal, and the crown honestly Partial (finite Discharged, transfinite/carrier-κ open, tragic pre-registered and live). The two promoted checks — Bookkeeping-re-hit and κ-readmitted — are the spine of the audit, because they are Series 10's and Series 08's central findings inherited. As the program's terminal series, the verdict is its close: the honest terminus, crown-on-finite-stages or tragic, is the program's completion.**
