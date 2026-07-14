# WS5, The verdict, and the audit folded in

**Design doc. Series 13, the computed terminus. Owns: the verdict COMPUTED from WS1–WS4 (never hand-set), DUAL (orders non-trivial + transport with exogeneity + connection with a genuine non-identity round trip + defect structural) / TOTAL (the mint essentially surjective, reported in its direction) / DISCONNECTED (the WS1 orders vacuous, obstruction precise) / PARTIAL, AND the audit folded in: the fork-open check (no theorem sorts an out-of-image import into given/chosen), the genuine-connection check (orders non-trivial, round trip non-identity), the exogeneity check (`ws2_mint_exogenous` a proof term), the structural-defect check (the label excludes), the strip test on every payoff, and the names-not-terms check. The verdict BRANCHES on a certified fork and cannot be hand-set.**

*Series 13 is standalone; the verdict type `Series13Verdict` (README §2.8) is defined here. WS5 CONSUMES the WS1–WS4 payoffs (`ws1_orders_nontrivial`, `ws2_mint_lands_in_opening`, `ws2_mint_exogenous`, `ws3_galois`, `ws3_roundtrip_not_identity`, `ws4_mint_not_surjective`, `ws4_exclusion_structural`) and computes the verdict as a function of a mechanized `Audit` certificate whose every field is one of those theorems; it does not re-prove them. The genuinely new Lean is `FitFork`, `verdictOfFit`, the `Audit`, `ws5_verdict`, `ws5_verdict_eq`, and the audit checks. WS5 depends on WS4 settling (the verdict cannot be computed until the defect, or TOTAL, is in hand). The signature risks: the verdict a returned constant ignoring its certificate, and a discipline breached (any of the four) or a name a term.*

## The object at stake

The charter's WS5 (§2): compute the verdict from WS1–WS4 as a function, never hand-set, on the model of Series 12's `verdictOfFork`; fold in the audit checks promoted from the standing set. Two obligations. (1) **The verdict as a function:** a `FitFork` carrying WHICH outcome the code delivered (each constructor holding its proof), and `verdictOfFit` casing on it, so the verdict tracks WS4's honest terminus and cannot be hand-set. (2) **The audit:** the five checks (fork-open, genuine-connection, exogeneity, structural-defect, names-not-terms) plus the strip test, each a check the review runs, several first-class here.

**Ambient theory.** `spec/README.md` §2.8 (`Series13Verdict`); the WS1–WS4 payoffs; the `Audit`/`verdict` certificate pattern (Series 07–12).

## The verdict type and the fork (README §2.8)

```lean
inductive Series13Verdict
  | Dual | Total | Disconnected | Partial | Refuted | Circular
  deriving DecidableEq

/-- **The fit fork (data-level).** WHICH terminus the code discharged, each constructor carrying its proof.
    Data-level (a `Type`-valued inductive) so the verdict can CASE on it. WS4 discharges `defectStructural`
    via `outWit`; had it landed TOTAL, `mintSurjective` would carry that proof; had WS1 landed vacuous,
    `ordersTrivial` would. -/
inductive FitFork {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hinf : ℵ₀ ≤ κ) : Type u
  | defectStructural                                                        -- DUAL: the defect is structural
      (hd : ¬ Recoverable (outWit dest h₀ h₁ hinf)
            ∧ ¬ ∃ insp, mintL dest h₀ insp = outWit dest h₀ h₁ hinf)
  | mintSurjective                                                          -- TOTAL: every import mintable
      (hs : ∀ b : Lab dest, (¬ Recoverable b) → ∃ insp, mintL dest h₀ insp = b)
  | ordersTrivial                                                           -- DISCONNECTED: an order is trivial
      (ht : (∀ a b : Insp dest, a ≤ b) ∨ (∀ a b : Insp dest, a ≤ b → a = b))
  | perInstance (hp : True)                                                 -- PARTIAL: an obligation degenerate

def verdictOfFit {X} {dest} {h₀ h₁} {hinf} : FitFork dest h₀ h₁ hinf → Series13Verdict
  | .defectStructural _ => .Dual
  | .mintSurjective   _ => .Total
  | .ordersTrivial    _ => .Disconnected
  | .perInstance      _ => .Partial
```

## Candidates

### V-C1, the verdict as a function of a mechanized audit (the lead)

```lean
/-- **The audit certificate.** Every field is a WS1–WS4 theorem, so the verdict is a FUNCTION of the audit,
    falsifiable, never hand-set. The `fork` field carries WHICH terminus WS4 delivered (Finding-style). -/
structure Audit {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hinf : ℵ₀ ≤ κ) where
  orders_nontrivial   : (∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b)
                        ∧ (∃ a b : Lab dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest, ¬ a ≤ b)   -- WS1
  transport           : ∀ insp, ¬ Recoverable (mintL dest h₀ insp)                          -- WS2 transport
  exogenous           : ∃ i₁ i₂, plainOf (mintL dest h₀ i₁) = plainOf (mintL dest h₀ i₂)
                                 ∧ mintL dest h₀ i₁ ≠ mintL dest h₀ i₂                        -- WS2 exogeneity
  connection          : GaloisConnection (mintL dest h₀) (fun b => readInsp dest h₀ b)        -- WS3
  roundtrip_defect    : mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)) ≤ bRefActive dest hinf
                        ∧ ¬ (bRefActive dest hinf ≤ mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)))  -- WS3 non-identity
  fork                : FitFork dest h₀ h₁ hinf                                               -- WS4: which terminus

/-- **The verdict BRANCHES on the certified fork**, not a returned constant. -/
def verdict {X} {dest} {h₀ h₁} {hinf} (cert : Audit dest h₀ h₁ hinf) : Series13Verdict := verdictOfFit cert.fork

/-- The assembled audit for the concrete carrier: every field a WS1–WS4 theorem, `fork := defectStructural`. -/
noncomputable def ws5_audit {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    Audit dest h₀ h₁ hinf where
  orders_nontrivial := ⟨(ws1_orders_insp_nontrivial dest h₀).1, (ws1_orders_insp_nontrivial dest h₀).2,
                        (ws1_orders_lab_nontrivial dest h₀ hinf).1, (ws1_orders_lab_nontrivial dest h₀ hinf).2⟩
  transport         := ws2_transport_forall dest h₀ hinf
  exogenous         := ws2_mint_exogenous dest h₀ hinf
  connection        := ws3_galois dest h₀ hinf
  roundtrip_defect  := ws3_roundtrip_not_identity dest h₀ hinf
  fork              := .defectStructural (ws4_mint_not_surjective dest h₀ h₁ hne hinf)

def ws5_verdict {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) : Series13Verdict :=
  verdict (ws5_audit dest h₀ h₁ hne hinf)

/-- `ws5_verdict = Dual` is a THEOREM: the audit's fork is `defectStructural`, and `verdictOfFit` maps it to
    `Dual`. Not a definitional constant; had WS4 landed TOTAL, the fork would be `mintSurjective` and the
    verdict `Total`. -/
theorem ws5_verdict_eq {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    ws5_verdict dest h₀ h₁ hne hinf = Series13Verdict.Dual := rfl
```

- **Ambient:** the WS1–WS4 payoffs; `FitFork`/`verdictOfFit` (README §2.8); the `Audit` pattern.
- **Success condition (Dual):** `verdict` cases on the fork; `ws5_verdict = Dual` is a theorem via the `defectStructural` fork; `Total`/`Disconnected`/`Partial` reachable via the other constructors.
- **Failure mode:** *the verdict a returned constant ignoring its certificate.* Foreclosed: `verdict := verdictOfFit cert.fork` inspects the fork; the alternatives are reachable. **Winner (the computed verdict, branching).**

**Paper triage.** Decidable: `verdictOfFit (.defectStructural _) = .Dual` by `rfl`; the audit supplies the fork from WS4. **Winner.**

### V-C2, the concrete verdict is never the alternatives (the falsifiability certificate)

```lean
theorem ws5_verdict_not_total {X} (dest) (h₀ h₁) (hne) (hinf) :
    ws5_verdict dest h₀ h₁ hne hinf ≠ .Total := by rw [ws5_verdict_eq]; decide
theorem ws5_verdict_not_disconnected … ≠ .Disconnected := by rw [ws5_verdict_eq]; decide
theorem ws5_verdict_not_partial … ≠ .Partial := by rw [ws5_verdict_eq]; decide
```
The concrete verdict, whose fork WS4 discharged at `defectStructural`, is `Dual` and provably not `Total`, `Disconnected`, `Partial`, `Refuted`, or `Circular`. Falsifiable because it routes through `ws5_verdict_eq` (the fork is `defectStructural`, the defect): had WS4 landed TOTAL, the fork would be `mintSurjective` and the verdict `Total`.

- **Success condition (Dual):** the concrete verdict is `Dual` and never the others, via its fork. **Winner (falsifiability).**

### V-C3, the audit checks as theorems (the folded-in audit, first-class)

```lean
/-- **THE AUDIT (folded in).** The five disciplines as checkable theorems over the concrete build.
    (a) genuine-connection: orders non-trivial AND a non-identity round trip.
    (b) exogeneity: the mint above the plain layer, a proof term.
    (c) structural-defect: the label (diagonal link) excludes.
    (d) fork-open: the defect only LOCATES (its type is `¬ ∃ insp, mintL insp = outWit`, an image-membership
        negation), never a classification, witnessed by the ABSENCE of any given/chosen sorting term.
    (e) names-not-terms: inherited, checked by grep (no proof term named given/chosen/…). -/
theorem ws5_audit_genuine_connection {X} (dest) (h₀ h₁) (hne) (hinf) :
    ((∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b))          -- orders non-trivial …
  ∧ (mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)) ≤ bRefActive dest hinf
     ∧ ¬ (bRefActive dest hinf ≤ mintL dest h₀ (readInsp dest h₀ (bRefActive dest hinf)))) := …  -- … round trip non-identity
theorem ws5_audit_exogeneity {X} (dest) (h₀ h₁) (hne) (hinf) :
    ∃ i₁ i₂, plainOf (mintL dest h₀ i₁) = plainOf (mintL dest h₀ i₂) ∧ mintL dest h₀ i₁ ≠ mintL dest h₀ i₂ :=
  ws2_mint_exogenous dest h₀ hinf
theorem ws5_audit_structural_defect {X} (dest) (h₀ h₁) (hne) (hinf) :
    (∀ insp, bT (mintL dest h₀ insp) h₀ = ¬ bF (mintL dest h₀ insp) h₀)
  ∧ (bT (outWit dest h₀ h₁ hinf) h₀ = bF (outWit dest h₀ h₁ hinf) h₀) :=
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

- **Failure mode:** *the verdict hand-set, ignoring its certificate, SERIOUS.* A constant cannot track WS4's terminus; it would report `Dual` even if the defect failed. **Reject.** The verdict is `verdictOfFit cert.fork` (V-C1), branching on the certified fork; `ws5_verdict = Dual` is then a THEOREM (`ws5_verdict_eq`), not a definition.

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

## Outcome classes (per charter §5)

- **Dual (the WS5 payoff):** `ws5_verdict = Dual` (V-C1, computed by casing on the `defectStructural` fork, a theorem), V-C2 (falsifiability), V-C3 (the audit checks), V-C4 (the alternatives expressible). The verdict computed from a discharged audit, the fork left open.
- **Total (pre-registered, first-class, V-C4):** if WS4 reports TOTAL, the audit's `fork := mintSurjective …` and `verdictOfFit` computes `Total`. The verdict follows the audit's fork; the fork makes the alternative expressible.
- **Disconnected (pre-registered, first-class, V-C4):** if WS1 reports the orders vacuous, `fork := ordersTrivial …`, `verdictOfFit` computes `Disconnected`, and WS2–WS4 are not built (the obstruction is the result).
- **Partial (pre-registered):** if any obligation degenerates (an iso-in-disguise connection, an artifactual defect), the corresponding fork/field fails and the verdict is `Partial`.
- **Circular (WS5-audit-only):** if any discipline is breached (the fork sorted, the connection by fiat, the mint recoverable, the defect artifactual, or a name a proof term), WS5 records `Circular` and names the breach.
- **Strip test (aggregated here, protocol §0.3).** WS5 runs the strip on every payoff: transport strips to the `ws2_residue_distinct`-driven non-recoverability fact; exogeneity to the `plainOf`-constancy fact; connection to the `GaloisConnection`-with-non-identity-round-trip fact; defect to the out-of-image `¬ Recoverable` fact with the diagonal-link exclusion. `ws5_verdict` itself strips to *"the verdict inductive's value computed by casing on which terminus (defect / surjective / trivial-order / degenerate) the build discharged"*, a certificate-branching fact. No payoff survives as something other than its named fact; no name is a term.

## Deliverable

`series-13/formal/Series13/ws5.lean`: `Series13Verdict`, `FitFork`, `verdictOfFit` (README §2.8); the WS1–WS4 payoffs consumed; `Audit`, `verdict`, `ws5_audit`, `ws5_verdict`, `ws5_verdict_eq` (V-C1), `ws5_verdict_not_*` (V-C2), the audit checks (V-C3), the DISCONNECTED/TOTAL routing (V-C4). **WS5 consumes WS1–WS4; cannot compute until WS4 settles; the verdict branches on the fork.** Axiom check: `#print axioms ws5_verdict` and each audit check reduce through the WS1–WS4 payoffs to the standard three. **The verdict is computed from a discharged audit and branches on the certified fork (never hand-set), the fork left open (the defect locates, never sorts), and the four disciplines are folded into the audit: the coda's terminus, computed.**
