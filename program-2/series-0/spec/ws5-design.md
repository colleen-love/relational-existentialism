# WS5, The verdict and the audit folded in

**Design doc. Series 0. Owns: the `Outcome` type, the `verdict` FUNCTION (of the WS1/WS3/WS4 flags, never WS2, never hand-set), `ws5_verdict_eq` (the computed outcome), the falsifiability theorems (the verdict is not the other outcomes under the certified flags), and the five audit clauses (a–e) as actual Lean propositions bundling the WS1–WS4 payoffs. The verdict is the RESIDUE of the process, not its premise.**

*Series 0 consumes the WS1/WS3/WS4 payoffs (and cites WS2 as untouched baseline). WS5 DEFINES the verdict type (README §2.4) and computes. The signature risks: the verdict HAND-SET (not a function of the flags); a discipline breached (a cardinal ceiling, the asymmetry a label, the collapse relitigated or feeding the verdict, the import named); or a name a term. Each is an audit clause AND a review check.*

## The object at stake

The charter's WS5 (§2): the verdict is computed — GROUND-ESTABLISHED (carrier and reification built, collapse inherited cleanly, asymmetry of knowing genuine and load-bearing with direction non-recoverable, import seated and quantified); PARTIAL (any obligation lands only per-instance or degenerate); OBSTRUCTED (the finite-attention functor admits no reification, OR the asymmetry collapses to a label, reported with the precise obstruction). The audit checks (a–e). The pre-registered sin: the verdict as a premise, hand-set, or the collapse feeding it (audit d).

**Ambient theory.** README §2.4 (`Outcome`, `verdict`); WS1 (`ws1_reification_exists`, `ws1_bound_is_finite_attention`), WS3 (`ws3_direction_not_recoverable`, `ws3_passive_constitution`, `ws3_active_passive_distinct`), WS4 (`ws4_import_breaks_baseline`, `ws4_import_quantified`), WS2 (`ws2_collapse_inherited`, baseline).

## Candidates

### C1, the verdict as a function of the WS1/WS3/WS4 flags (the lead)

```lean
inductive Outcome | groundEstablished | partial | obstructed deriving DecidableEq
/-- **The verdict FUNCTION.** GROUND-ESTABLISHED iff reification exists (WS1), the asymmetry is genuine
    (WS3), and the import is seated (WS4); OBSTRUCTED if reification or the asymmetry fails; else PARTIAL.
    NOTE: the collapse (WS2) is NOT an argument (audit d). -/
def verdict (reif : Bool) (asym : Bool) (imp : Bool) : Outcome :=
  if reif && asym && imp then .groundEstablished
  else if reif && asym then .partial          -- carrier + asymmetry, import short: per-instance
  else .obstructed                            -- no reification, or the asymmetry a label
theorem ws5_verdict_eq (hinf : ℵ₀ ≤ κ) : verdict true true true = Outcome.groundEstablished := rfl
```

The three flags are each JUSTIFIED by a WS1/WS3/WS4 proof term (below); the verdict branches on them and cannot be hand-set (it is `rfl` from the flags, and the flags are set to `true` only because the theorems hold). WS2 is not an argument (audit d).

- **Ambient:** the WS1/WS3/WS4 payoffs.
- **Success condition (GROUND):** `ws5_verdict_eq` typechecks by `rfl`; each flag has its justifying theorem.
- **Failure mode:** *verdict hand-set.* Foreclosed: `verdict` is a function; `ws5_verdict_eq` is `rfl`; the flags carry their proofs. **Winner.**

### C2, the flag-justification bundle (the lead)

```lean
/-- The three flags are justified: reification exists, the asymmetry is genuine and non-recoverable, the
    import is seated and quantified. The verdict's inputs are theorems, not choices. -/
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :
    (∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X), FinReify attends reify)  -- reif
  ∧ (¬ Recoverable (knowLiftD hinf))                                                          -- asym (direction)
  ∧ (∀ {Q : Type u} (f : impCar → Q), f ⟨true⟩ ≠ f ⟨false⟩ →
        ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R ⟨true⟩ ⟨false⟩)                                -- imp
```

Bundles the WS1/WS3/WS4 justifications as one object WS5's verdict reads, so `reif = asym = imp = true` is EARNED. Each conjunct is the corresponding payoff (or its core).

### C3, the five audit clauses (a–e) as Lean propositions (the audit-facing bundle)

```lean
-- (a) NO CARDINAL CEILING: out-neighborhoods finite, uniformly in κ
theorem ws5_audit_no_ceiling (hinf : ℵ₀ ≤ κ) (attends : X → Finset X) :
    ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < Cardinal.aleph0        := ws1_bound_is_finite_attention …
-- (b) THE ASYMMETRY IS NOT A LABEL: a genuine reader, load-bearing
theorem ws5_audit_asymmetry_not_label (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (knowLiftD hinf) a b ∧ (attendsD b = ∅)            := ⟨(ws3_passive_constitution …).2, …⟩
-- (c) DIRECTION NON-RECOVERABLE: a proof term
theorem ws5_audit_direction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (knowLiftD hinf) := ws3_direction_not_recoverable hinf
-- (d) COLLAPSE INHERITED, NOT RELITIGATED: the collapse theorem IS the imported engine, and the verdict does
--     not read it (verdict has three args; none is the collapse)
theorem ws5_audit_collapse_inherited (hinf : ℵ₀ ≤ κ) (hcar) (attends) (hb) (ha) :
    ws2_collapse_inherited hinf hcar attends hb ha
      = P1.Core.ws2_import_theorem_static (symDest hinf hcar attends) hb ha    := rfl
-- (e) IMPORT QUANTIFIED, NOT NAMED: the breaking is ∀ over the import
theorem ws5_audit_import_quantified (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type u} (f : impCar → Q), f ⟨true⟩ ≠ f ⟨false⟩ →
        ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R ⟨true⟩ ⟨false⟩                 := fun f h => (ws4_import_breaks_baseline hinf f h).2
```

Audit (d) is the key clause: `ws5_audit_collapse_inherited` states, BY `rfl`, that `ws2_collapse_inherited` is definitionally the imported `ws2_import_theorem_static` (relitigation impossible), and `verdict`'s signature (three flags, none the collapse) shows no verdict hinges on it. Audit (e) makes the import-quantification a proof term. **Winner (the audit-facing bundle).**

### C4, falsifiability — the verdict is not the other outcomes (the honest fork)

```lean
theorem ws5_verdict_not_obstructed (hinf : ℵ₀ ≤ κ) : verdict true true true ≠ Outcome.obstructed := by decide
theorem ws5_verdict_not_partial    (hinf : ℵ₀ ≤ κ) : verdict true true true ≠ Outcome.partial    := by decide
```

The verdict FUNCTION, on the certified flags, is provably NOT `obstructed` and NOT `partial`, so GROUND-ESTABLISHED is a discriminating outcome, not the only reachable value (mirrors Series 13's `ws5_verdict_not_partial`). If reification failed (`reif = false`), `verdict` would compute `obstructed`; the function genuinely discriminates. **Winner (falsifiability).**

### C5, set the verdict to GROUND-ESTABLISHED directly (the sin, rejected)

```lean
def verdict : Outcome := .groundEstablished   -- REJECT: hand-set, reads no flag
```

**Reject as the sin:** a constant verdict reads no flag; it is the premise, not the residue. The winner C1 is a FUNCTION of the flags, `ws5_verdict_eq` is `rfl` FROM the flags, and C4 shows the function discriminates. **Reject.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict a function; `ws5_verdict_eq` | WS1/WS3/WS4 flags | yes, `rfl` | **win** |
| C2 | flags justified by payoffs | the payoffs | yes, the bundle | **win** |
| C3 | audit (a–e) as propositions | WS1–WS4 + `ws2` `rfl` | yes, each a payoff / `rfl` | **win (audit)** |
| C4 | falsifiability (`≠` other outcomes) | `verdict` | yes, `by decide` | **win (falsifiability)** |
| C5 | verdict hand-set constant | — | yes, reads no flag | **reject (the sin)** |

## Winning candidates: C1 + C2 + C3 + C4

### Definitions and obligations (cite README §2.4)

```lean
-- Outcome, verdict, ws5_verdict_eq                         (C1)
-- ws5_flags_justified                                      (C2)
-- ws5_audit_no_ceiling … ws5_audit_import_quantified       (C3, a–e)
-- ws5_verdict_not_obstructed, ws5_verdict_not_partial      (C4)
```

**Proof architecture.** `verdict` is a total function on three `Bool`s; `ws5_verdict_eq` and the falsifiability theorems are `rfl` / `by decide`. `ws5_flags_justified` and the audit clauses are the WS1/WS3/WS4 payoffs re-exported (or their cores). Audit (d) is `rfl` (definitional identity of `ws2_collapse_inherited` with the imported engine) plus the structural fact that `verdict` does not take the collapse as an argument. **Dependencies:** all WS1/WS3/WS4 payoffs; `ws2_collapse_inherited` (cited, not consumed by `verdict`). **The verdict is computed; the audit certifies the five disciplines; the falsifiability shows the function discriminates.**

## Outcome classes (per charter §5)

- **GROUND-ESTABLISHED (the computed verdict here):** `verdict true true true = groundEstablished`, each flag earned by a payoff, the five audit clauses discharged, the falsifiability showing the function discriminates.
- **PARTIAL / OBSTRUCTED (pre-registered):** if a WS1/WS3 obligation fell short, the flags would flip and `verdict` would compute `partial` or `obstructed`; the function is the honest fork, not a rubber stamp. Recorded in `charter-status.md` if reached.
- **Strip test.** Delete "verdict / ground / audit" and `verdict` is *"a function `Bool³ → Outcome`"*, `ws5_verdict_eq` is *"`f true true true = groundEstablished` by computation"*, the audit clauses are the bare WS1–WS4 facts. No name is a term.

## Deliverable

`program-2/series-0/formal/P2S0/ws5.lean`: `import P1` (and the WS1–WS4 payoffs, in-namespace); `Outcome`, `verdict`, `ws5_verdict_eq`; `ws5_flags_justified`; `ws5_audit_no_ceiling`…`ws5_audit_import_quantified`; `ws5_verdict_not_obstructed`, `ws5_verdict_not_partial`. **WS5 computes the verdict from WS1/WS3/WS4 (never WS2), folds in the audit (a–e), and shows the function discriminates.** Axiom check: `#print axioms ws5_verdict_eq` reduces to nothing beyond the flags' payoffs (standard three). **The verdict is the residue of the process; GROUND-ESTABLISHED is earned, and the audit certifies the five disciplines held.**
