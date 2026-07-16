# WS5, The verdict, and the audit folded in

**Design doc. Series 13, the computed verdict. Owns: the verdict COMPUTED from WS1–WS4 (never hand-set), DUAL (orders non-trivial + transport with exogeneity + connection with a genuine non-identity round trip + defect structural) / TOTAL (the mint essentially surjective, reported in its direction) / DISCONNECTED (the WS1 orders vacuous, obstruction precise) / PARTIAL, AND the audit folded in: the fork-open check (no theorem sorts an out-of-image import into given/chosen), the genuine-connection check (orders non-trivial, round trip non-identity), the exogeneity check (`ws2_mint_exogenous` a proof term), the structural-defect check (the label excludes), the strip test on every payoff, and the names-not-terms check. The verdict BRANCHES on a certified fork and cannot be hand-set.**

*Series 13 is standalone; the verdict type `Series13Verdict` (README §2.8) is defined here. WS5 CONSUMES the WS1–WS4 payoffs (`ws1_orders_nontrivial`, `ws2_mint_lands_in_opening`, `ws2_mint_exogenous`, `ws3_galois`, `ws3_roundtrip_not_identity`, `ws4_mint_not_surjective`, `ws4_exclusion_structural`) and computes the verdict as a function of a mechanized `Audit` certificate whose every field is one of those theorems; it does not re-prove them. The genuinely new Lean is `FitFork`, `verdictOfFit`, the `Audit`, `ws5_verdict`, `ws5_verdict_eq`, and the audit checks. WS5 depends on WS4 settling (the verdict cannot be computed until the defect, or TOTAL, is in hand). The signature risks: the verdict a returned constant ignoring its certificate, and a discipline breached (any of the four) or a name a term.*

## The object at stake

The charter's WS5 (§2): compute the verdict from WS1–WS4 as a function, never hand-set, on the model of Series 12's `verdictOfFork`; fold in the audit checks promoted from the standing set. Two obligations. (1) **The verdict as a function:** a `FitFork` carrying WHICH outcome the code delivered (each constructor holding its proof), and `verdictOfFit` casing on it, so the verdict tracks WS4's honest outcome and cannot be hand-set. (2) **The audit:** the five checks (fork-open, genuine-connection, exogeneity, structural-defect, names-not-terms) plus the strip test, each a check the review runs, several first-class here.

**Ambient theory.** `spec/README.md` §2.8 (`Series13Verdict`); the WS1–WS4 payoffs; the `Audit`/`verdict` certificate pattern (Series 07–12).

## The verdict type and the fork (README §2.8)

```lean
inductive Series13Verdict
  | Dual | Total | Disconnected | Partial | Refuted | Circular
  deriving DecidableEq

/-- **The fit fork (data-level).** WHICH outcome the code discharged, each constructor carrying its proof
    AT THE HONEST RESOLUTION (mintability up to `≈`, WS4). Data-level (a `Type`-valued inductive) so the
    verdict can CASE on it. On `|Hold| ≥ 2` (carriers of interest) WS4 discharges `defectStructural` via
    `outWit` (an import `≈` no mint); on `|Hold| = 1` (degenerate) it discharges `mintSurjective` (every
    import `≈` a mint); had WS1 landed vacuous, `ordersTrivial`. NEITHER branch is the lead; the verdict is
    computed from which the carrier satisfies. -/
inductive FitFork {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) : Type u
  | defectStructural                                                        -- DUAL: some import ≈ no mint (|Hold| ≥ 2)
      (h₁ : Hold dest) (hne : h₁ ≠ h₀)
      (hd : ¬ Recoverable (outWit dest h₀ h₁ hinf)
            ∧ ¬ ∃ insp, labEquiv dest h₀ (mintL dest h₀ insp) (outWit dest h₀ h₁ hinf))
  | mintSurjective                                                          -- TOTAL: every import ≈ a mint (|Hold| = 1)
      (hs : ∀ b : Lab dest, (¬ Recoverable b) → ∃ insp, labEquiv dest h₀ (mintL dest h₀ insp) b)
  | ordersTrivial                                                           -- DISCONNECTED: an order is trivial
      (ht : (∀ a b : Insp dest, a ≤ b) ∨ (∀ a b : Insp dest, a ≤ b → a = b))
  | perInstance (hp : True)                                                 -- PARTIAL: an obligation degenerate

def verdictOfFit {X} {dest} {h₀} {hinf} : FitFork dest h₀ hinf → Series13Verdict
  | .defectStructural _ _ _ => .Dual
  | .mintSurjective   _     => .Total
  | .ordersTrivial    _     => .Disconnected
  | .perInstance      _     => .Partial
```

**The verdict is computed, not led.** The `FitFork` is discharged by CASING ON THE CARRIER: `if ∃ h₁, h₁ ≠ h₀ then .defectStructural … else .mintSurjective …`. On carriers of interest (`|Hold| ≥ 2`) the first branch fires and the verdict is `Dual`, BECAUSE the TOTAL target `∀ ¬Recoverable b, ∃ insp, mintL insp ≈ b` was attempted (WS4 D-C3) and REFUTED by `outWit`. On the degenerate single-hold carrier the second fires and the verdict is `Total`. The verdict tracks the math, not a preference.

## Candidates

### V-C1, the verdict as a function of a mechanized audit (the lead)

```lean
/-- **The audit certificate.** Every field is a WS1–WS4 theorem, so the verdict is a FUNCTION of the audit,
    falsifiable, never hand-set. The `fork` field carries WHICH outcome WS4 delivered (Finding-style). -/
structure Audit {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) where
  orders_nontrivial   : (∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b)
                        ∧ (∃ a b : Lab dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest, ¬ a ≤ b)   -- WS1
  transport           : ∀ insp, ¬ Recoverable (mintL dest h₀ insp)                          -- WS2 transport
  exogenous           : ∃ i₁ i₂, plainOf (mintL dest h₀ i₁) = plainOf (mintL dest h₀ i₂)
                                 ∧ mintL dest h₀ i₁ ≠ mintL dest h₀ i₂                        -- WS2 exogeneity
  connection          : GaloisConnection (mintL dest h₀) (fun b => readInsp dest h₀ b)        -- WS3
  roundtrip_defect    : mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)) ≤ bRefActive dest hinf
                        ∧ ¬ (bRefActive dest hinf ≤ mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)))  -- WS3 non-identity
  fork                : FitFork dest h₀ hinf                                                  -- WS4: which outcome, COMPUTED

/-- **The verdict BRANCHES on the certified fork**, not a returned constant. -/
def verdict {X} {dest} {h₀} {hinf} (cert : Audit dest h₀ hinf) : Series13Verdict := verdictOfFit cert.fork

/-- **The fork is discharged by CASING ON THE CARRIER** (the hold count), so the verdict is computed, not led.
    If the carrier has a second hold, the DUAL branch fires (the TOTAL target was refuted by `outWit`); if it
    is single-hold, the TOTAL branch fires. Neither is assumed. -/
noncomputable def ws5_fork {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) : FitFork dest h₀ hinf := by
  by_cases hsecond : ∃ h₁ : Hold dest, h₁ ≠ h₀
  · obtain ⟨h₁, hne⟩ := hsecond
    exact .defectStructural h₁ hne (ws4_mint_not_surjective dest h₀ h₁ hne hinf)   -- |Hold| ≥ 2 ⟹ DUAL
  · exact .mintSurjective                                                          -- |Hold| = 1 ⟹ TOTAL
      (ws4_mint_essentially_surjective_degenerate dest h₀ (fun h => by
        by_contra hh; exact hsecond ⟨h, hh⟩) hinf)

noncomputable def ws5_audit {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) : Audit dest h₀ hinf where
  orders_nontrivial := ⟨(ws1_orders_insp_nontrivial dest h₀).1, (ws1_orders_insp_nontrivial dest h₀).2,
                        (ws1_orders_lab_nontrivial dest h₀ hinf).1, (ws1_orders_lab_nontrivial dest h₀ hinf).2⟩
  transport         := ws2_transport_forall dest h₀ hinf
  exogenous         := ws2_mint_exogenous dest h₀ hinf
  connection        := ws3_galois dest h₀ hinf
  roundtrip_defect  := ws3_roundtrip_not_identity dest h₀ hinf
  fork              := ws5_fork dest h₀ hinf

noncomputable def ws5_verdict {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) : Series13Verdict :=
  verdict (ws5_audit dest h₀ hinf)

/-- **The verdict on a carrier of interest is `Dual`, as a THEOREM** (computed): given a second hold, the
    fork is `defectStructural` and `verdictOfFit` maps it to `Dual`, BECAUSE the TOTAL target was refuted by
    `outWit`. On a single-hold carrier `ws5_verdict = Total` (the companion `ws5_verdict_degenerate`). Neither
    is hand-set; the verdict follows the carrier. -/
theorem ws5_verdict_eq {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    ws5_verdict dest h₀ hinf = Series13Verdict.Dual := by
  unfold ws5_verdict verdict ws5_audit ws5_fork
  rw [dif_pos ⟨h₁, hne⟩]; rfl        -- the second-hold branch fires; verdictOfFit (.defectStructural …) = .Dual

theorem ws5_verdict_degenerate {X} (dest) (h₀ : Hold dest) (hone : ∀ h : Hold dest, h = h₀) (hinf : ℵ₀ ≤ κ) :
    ws5_verdict dest h₀ hinf = Series13Verdict.Total := by
  unfold ws5_verdict verdict ws5_audit ws5_fork
  rw [dif_neg (by rintro ⟨h₁, hne⟩; exact hne (hone h₁))]; rfl
```

- **Ambient:** the WS1–WS4 payoffs; `FitFork`/`verdictOfFit` (README §2.8); the `Audit` pattern.
- **Success condition (Dual):** `verdict` cases on the fork; `ws5_verdict = Dual` is a theorem via the `defectStructural` fork; `Total`/`Disconnected`/`Partial` reachable via the other constructors.
- **Failure mode:** *the verdict a returned constant ignoring its certificate.* Foreclosed: `verdict := verdictOfFit cert.fork` inspects the fork; the alternatives are reachable. **Winner (the computed verdict, branching).**

**Paper triage.** Decidable: `verdictOfFit (.defectStructural _) = .Dual` by `rfl`; the audit supplies the fork from WS4. **Winner.**

### V-C2, the concrete verdict is never the alternatives (the falsifiability certificate)

```lean
theorem ws5_verdict_not_total {X} (dest) (h₀ h₁) (hne : h₁ ≠ h₀) (hinf) :
    ws5_verdict dest h₀ hinf ≠ .Total := by rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide
theorem ws5_verdict_not_disconnected … : ws5_verdict dest h₀ hinf ≠ .Disconnected := by
  rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide
theorem ws5_verdict_not_partial … : ws5_verdict dest h₀ hinf ≠ .Partial := by
  rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide
```
On a carrier of interest (a second hold `h₁ ≠ h₀`), the verdict is `Dual` and provably not `Total`, `Disconnected`, `Partial`, `Refuted`, or `Circular`. Falsifiable because it routes through `ws5_verdict_eq`, which fires the DUAL branch ONLY because that carrier has a second hold and the TOTAL target was refuted: on a single-hold carrier `ws5_verdict = Total` (`ws5_verdict_degenerate`), a different value, so the verdict genuinely tracks the carrier and is not the constant `Dual`.

- **Success condition (computed):** the verdict on a second-hold carrier is `Dual` and never the others; the verdict on a single-hold carrier is `Total`; both theorems, neither the lead. **Winner (falsifiability, computed).**

### V-C3, the audit checks as theorems (the folded-in audit, first-class)

```lean
/-- **THE AUDIT (folded in).** The five disciplines as checkable theorems over the concrete build.
    (a) genuine-connection: orders non-trivial AND a non-identity round trip.
    (b) exogeneity: the mint above the plain layer, a proof term.
    (c) structural-defect: the label (diagonal link) excludes.
    (d) fork-open: the defect only LOCATES (its type is `¬ ∃ insp, mintL insp ≈ outWit`, a membership-up-to-`≈`
        negation), never a classification, witnessed by the ABSENCE of any given/chosen sorting term.
    (e) names-not-terms: inherited, checked by grep (no proof term named given/chosen/…). -/
theorem ws5_audit_genuine_connection {X} (dest) (h₀) (hinf) :
    ((∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b))          -- orders non-trivial …
  ∧ (mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)) ≤ bRefActive dest hinf
     ∧ ¬ (bRefActive dest hinf ≤ mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)))) := …  -- … round trip non-identity
theorem ws5_audit_exogeneity {X} (dest) (h₀) (hinf) :
    ∃ i₁ i₂, plainOf (mintL dest h₀ i₁) = plainOf (mintL dest h₀ i₂) ∧ mintL dest h₀ i₁ ≠ mintL dest h₀ i₂ :=
  ws2_mint_exogenous dest h₀ hinf
theorem ws5_audit_structural_defect {X} (dest) (h₀ h₁) (hne : h₁ ≠ h₀) (hinf) :  -- on a second-hold carrier
    (∀ b b' : Lab dest, labEquiv dest h₀ b b' → (bT b = bT b') ∧ (bF b h₀ ↔ bF b' h₀))  -- ≈ preserves link data …
  ∧ (∀ insp, bT (mintL dest h₀ insp) h₀ = ¬ bF (mintL dest h₀ insp) h₀)                 -- … mints ON the link …
  ∧ (bT (outWit dest h₀ h₁ hinf) h₀ = bF (outWit dest h₀ h₁ hinf) h₀) :=                 -- … outWit OFF it
  ws4_exclusion_structural dest h₀ h₁ hne hinf
```
Each audit check is a theorem over the concrete build, consuming the WS1–WS4 payoffs. The fork-open check (a) has no theorem to assert (it is the ABSENCE of a sorting term); WS5 records it as a review obligation and confirms the core defines no `Origin`/`genealogy`.

- **Ambient:** the WS1–WS4 payoffs.
- **Success condition (Dual):** the audit checks typecheck as the WS1–WS4 payoffs; the fork-open and names checks pass by inspection (no sorting term, no name a term). **Winner (the folded-in audit).**

### V-C4, the DISCONNECTED / TOTAL routing (the honest alternatives, first-class)

```lean
/-- If WS1 lands DISCONNECTED, the audit's `fork := ordersTrivial …` and `ws5_verdict = Disconnected`; WS2–WS4
    are not built and the audit fields degrade to the obstruction. If WS4 lands TOTAL, `fork := mintSurjective
    …` and `ws5_verdict = Total`. The verdict FOLLOWS the fork into whichever branch the build lands, never
    overriding it. -/
example : verdictOfFit (FitFork.ordersTrivial (dest := dest) …) = .Disconnected := rfl
example : verdictOfFit (FitFork.mintSurjective (dest := dest) …) = .Total := rfl
```
The pre-registered alternatives made expressible: the verdict branches into `Disconnected`/`Total` if the build lands there, so the honest outcome is computed, never manufactured past a real obstruction.

- **Success condition:** the alternatives are reachable constructors of `FitFork`, each mapping to its verdict by `rfl`. **Winner (the honest-alternative routing).**

### V-C5, a hand-set verdict (the sin, rejected)

```lean
def ws5_verdict : Series13Verdict := .Dual   -- a constant, ignoring WS1–WS4
```
Return `Dual` as a constant.

- **Failure mode:** *the verdict hand-set, ignoring its certificate, SERIOUS.* A constant cannot track WS4's outcome; it would report `Dual` even if the defect failed. **Reject.** The verdict is `verdictOfFit cert.fork` (V-C1), branching on the certified fork; `ws5_verdict = Dual` is then a THEOREM (`ws5_verdict_eq`), not a definition.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| V-C1 | verdict BRANCHES on the certified fork | `verdictOfFit`, WS4 fork | yes, `defectStructural ↦ Dual` | **win (computed verdict)** |
| V-C2 | concrete verdict never the alternatives | `noConfusion`/`decide`, `ws5_verdict_eq` | yes, via the fork | **win (falsifiability)** |
| V-C3 | the audit checks as theorems | WS1–WS4 payoffs | yes | **win (folded-in audit)** |
| V-C4 | DISCONNECTED/TOTAL routing | `FitFork` constructors | yes, `rfl` | **win (honest alternatives)** |
| V-C5 | hand-set constant | — | yes, ignores certificate | **reject (SERIOUS)** |

## Winning candidates: V-C1 + V-C2 + V-C3 + V-C4

### Definitions and obligations (cite `spec/README.md` §2.8; consume WS1–WS4)

```lean
namespace Series13.WS5
-- Series13Verdict, FitFork, verdictOfFit (README §2.8); the Audit pattern; WS1–WS4 payoffs — consumed.
-- Audit, verdict, ws5_audit, ws5_verdict, ws5_verdict_eq (V-C1); ws5_verdict_not_* (V-C2);
-- ws5_audit_genuine_connection, ws5_audit_exogeneity, ws5_audit_structural_defect (V-C3);
-- the DISCONNECTED/TOTAL routing examples (V-C4).
```

**Proof architecture.** V-C1 assembles the `Audit` (fields = the WS1–WS4 theorems, `fork := defectStructural (ws4_mint_not_surjective …)`) and computes `verdict cert = verdictOfFit cert.fork`; with the fork `defectStructural`, `ws5_verdict_eq : ws5_verdict = Dual` is a THEOREM (`rfl`). V-C2 certifies falsifiability via the fork. V-C3 folds in the audit: the genuine-connection, exogeneity, and structural-defect checks are the WS1/WS2/WS3/WS4 payoffs; the fork-open and names checks pass by the ABSENCE of any sorting term or name-as-term. V-C4 makes DISCONNECTED/TOTAL expressible via the other `FitFork` constructors. **Dependencies:** WS1–WS4 (the audit fields, so WS5 cannot compute until WS4 settles). **The verdict branches on the audit's fork (never a returned constant) and the audit folds the four disciplines into checkable theorems plus two by-inspection checks.**

## Outcome classes (per charter §5), COMPUTED

- **Dual (`|Hold| ≥ 2`, carriers of interest):** `ws5_verdict = Dual` (`ws5_verdict_eq`), the fork discharged at `defectStructural` BECAUSE the carrier has a second hold and the TOTAL target was refuted by `outWit` (WS4 D-C3). V-C2 (falsifiability), V-C3 (the audit checks). The verdict computed from a discharged audit, the fork left open. **This is not the lead; it is what the math gives on carriers with ≥2 holds.**
- **Total (`|Hold| = 1`, degenerate):** `ws5_verdict = Total` (`ws5_verdict_degenerate`), the fork discharged at `mintSurjective` via `ws4_mint_essentially_surjective_degenerate`. On a single-hold carrier the mint is essentially surjective (every import `≈` a mint), so self-reference manufactures the whole rescue. Reported honestly; if a carrier of interest were single-hold, this would be the finding.
- **Disconnected (first-class, V-C4):** if WS1 reports the orders vacuous, `fork := ordersTrivial …`, `verdictOfFit` computes `Disconnected`, and WS2–WS4 are not built (the obstruction is the result).
- **Partial (pre-registered):** if any obligation degenerates (an iso-in-disguise connection, an artifactual defect), the corresponding fork/field fails and the verdict is `Partial`.
- **Circular (WS5-audit-only):** if any discipline is breached (the fork sorted, the connection by fiat, the mint recoverable, the defect artifactual, or a name a proof term), WS5 records `Circular` and names the breach.

### The named open (the single-layer scope), stated not silenced

Series 13's carrier is FLAT: the reification tower (`IsReify`, `reifyStep`, `towerN`, `prec`) is deliberately outside the transcription (WS1), so the whole fit, the orders, the mint, the connection, and the defect, is drawn at the flat layer. WS5 records this as an explicit open, not a silent omission, and the close (Phase F) states it:

> **The layer-stability open.** Whether the mint COMMUTES WITH REIFICATION, and whether any TOWER-CARRYING import survives outside the mint's image up to `≈`, is untestable in this flat carrier and is left OPEN as a theorem-shaped question, exactly as Series 12's permanent opens were left. The verdict, whichever way it falls, is a FLAT-LAYER verdict: DUAL at the flat layer (a flat import `≈` no mint) or, on a degenerate carrier, TOTAL at the flat layer (the mint essentially surjective over FLAT imports, the tower unexamined). A flat mint essentially surjective over flat imports, with the tower unexamined, is a BOUNDED finding whose bound is the tower.

This open is prose and docstring only (a `-- OPEN:` note in `ws5.lean`), never a proof term; naming it does not sort the fork or classify any import, it bounds Series 13's claim.
- **Strip test (aggregated here, protocol §0.3).** WS5 runs the strip on every payoff: transport strips to the `ws2_residue_distinct`-driven non-recoverability fact; exogeneity to the `plainOf`-constancy fact; connection to the `GaloisConnection`-with-non-identity-round-trip fact; defect to the out-of-image `¬ Recoverable` fact with the diagonal-link exclusion. `ws5_verdict` itself strips to *"the verdict inductive's value computed by casing on which outcome (defect / surjective / trivial-order / degenerate) the build discharged"*, a certificate-branching fact. No payoff survives as something other than its named fact; no name is a term.

## Deliverable

`series-13/formal/Series13/ws5.lean`: `Series13Verdict`, `FitFork`, `verdictOfFit` (README §2.8); the WS1–WS4 payoffs consumed; `Audit`, `verdict`, `ws5_audit`, `ws5_verdict`, `ws5_verdict_eq` (V-C1), `ws5_verdict_not_*` (V-C2), the audit checks (V-C3), the DISCONNECTED/TOTAL routing (V-C4). **WS5 consumes WS1–WS4; cannot compute until WS4 settles; the verdict branches on the fork.** Axiom check: `#print axioms ws5_verdict` and each audit check reduce through the WS1–WS4 payoffs to the standard three. **The verdict is computed from a discharged audit and branches on the certified fork (never hand-set), the fork left open (the defect locates, never sorts), and the four disciplines are folded into the audit: the series' verdict, computed.**
