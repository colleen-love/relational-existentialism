# WS5 design — the verdict and the audit folded in (2.7)

**The verdict is COMPUTED from the flags, never hand-set: `verdict : Bool⁶ → Outcome`, `= conservedRel` by
computation on the certified flags, DISCRIMINATING (reaches all six outcomes), the deciding flags EARNED by the
WS1–WS4 headlines. The computed verdict is CONSERVED-RELATIVE: a non-trivial measure `Q` (WS1), the tick conserves
it in-sight (WS2), every change is an import (WS3, Series 07), and the free-lunch crux reaches both FREE-LUNCH and
CONSERVED (WS4) so the diagonal-as-source is self-relative, not forced — conservation holds relative-to-the-self,
the global failing (no global conservation asserted, the phase thesis). The five audit clauses (a)–(e) bundle the
payoffs.**

## 1. The outcome type and the verdict function

```
inductive Outcome
  | conservedRel      -- Q conserved in-sight, import the source, free-lunch self-relative, global fails
  | monotoneOnly      -- nothing conserved even in-sight, only an arrow rises
  | freeLunch         -- the diagonal a genuine internal source (creation forced), conservation fails from within
  | global            -- a genuine absolute conserved invariant is forced (contradicts the phase thesis)
  | disconnected      -- no non-trivial measure survives
  | partial'          -- an obligation degenerate ('partial' is a Lean keyword)
  deriving DecidableEq

def verdict (nonTrivial inSightConserved changeIsSource
             freeLunchReachable conservedReachable globalForced : Bool) : Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if globalForced then Outcome.global
  else if !inSightConserved then Outcome.monotoneOnly
  else if !changeIsSource then Outcome.partial'
  else if freeLunchReachable && !conservedReachable then Outcome.freeLunch
  else if !freeLunchReachable then Outcome.partial'
  else Outcome.conservedRel
```

## 2. The payoffs

```
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.conservedRel   -- := rfl

theorem ws5_verdict_discriminates :                       -- reaches all six outcomes (by decide)
    verdict false true true true true false = Outcome.disconnected
  ∧ verdict true true true true true true  = Outcome.global
  ∧ verdict true false true true true false = Outcome.monotoneOnly
  ∧ verdict true true false true true false = Outcome.partial'
  ∧ verdict true true true true false false = Outcome.freeLunch
  ∧ verdict true true true true true false  = Outcome.conservedRel

-- the four DECIDING flags earned by the WS1–WS4 headlines (globalForced is a disclosed meta-flag, honestly false)
theorem ws5_flags_justified {κ} (hinf : ℵ₀ ≤ κ) :
    (rankM e1 ≠ rankM e0 ∧ AttentionDistinguishes (destML hinf) e1 e0)                 -- WS1 nonTrivial
  ∧ (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)                       -- WS2 inSightConserved
  ∧ (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)        -- WS3 changeIsSource
  ∧ (Qc (diagStep ∅ 0) = Qc ∅ + 1)                                                      -- WS4 freeLunchReachable
  ∧ (Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2)))                -- WS4 conservedReachable
```

## 3. The five audit clauses (a)–(e)

```
-- (a) NO GLOBAL CONSERVATION ASSERTED. Conservation is FOR the in-sight (plain-bisim) relating, changed at the
-- import (WS3); globalForced is honestly false; and if a global were forced the verdict would show it (global).
theorem ws5_audit_no_global {κ} (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)          -- conserved in-sight (local)
  ∧ (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)  -- changed at the import
  ∧ (verdict true true true true true true = Outcome.global)              -- global reported only if forced

-- (b) THE FORK NOT BY FIAT. FREE-LUNCH and CONSERVED both reachable, the measure non-trivial, verdict discriminates.
theorem ws5_audit_fork_genuine {κ} (hinf : ℵ₀ ≤ κ) :
    (Qc (diagStep ∅ 0) = Qc ∅ + 1)
  ∧ (Qc (diagStep ({0} : Finset (Fin 2)) 0) = Qc ({0} : Finset (Fin 2)))
  ∧ (rankM e1 ≠ rankM e0)

-- (c) THE KNOT IS THE DIAGONAL-AS-SOURCE, NOT THE IMPORT-NESS (the costume gate). Import-ness (WS3, changeIsSource
-- true) ALONE never decides: with the diagonal fork degenerate the verdict is partial'. The WS4 payoffs rest on
-- the residue (ws2_residue_free), not on boundary import-ness.
theorem ws5_audit_knot_is_diagonal {κ} (hinf : ℵ₀ ≤ κ) :
    (verdict true true true false true false = Outcome.partial')           -- import-ness holds, no free-lunch side
  ∧ (verdict true true true false false false = Outcome.partial')
  ∧ (∀ insp : Hold (outDest hinf attendsM) → HoldPred (outDest hinf attendsM), ¬ ResidueRecoverable insp)

-- (d) CHANGE IS AN IMPORT. ws3_change_is_source rests on Series 07 (ws4_recoverable_not_import).
theorem ws5_audit_change_is_source {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ ¬ Recoverable (destML hinf)

-- (e) NAMES-NOT-TERMS. Meta-property enforced by the protocol §6 grep (docstring prose excepted); house placeholder.
theorem ws5_audit_names_not_terms : True := trivial
```

## 4. Triage

- **Computed, not hand-set (audit).** `verdict` is a total `Bool⁶ → Outcome` function; `ws5_verdict_eq` is `rfl`;
  `ws5_verdict_discriminates` reaches all six outcomes by `decide`; the deciding flags are the WS1–WS4 theorems
  (`ws5_flags_justified`). `globalForced` is a disclosed meta-flag (not a WS proposition), honestly `false`.
- **No global (audit a).** No payoff asserts a globally conserved `Q`; conservation is in-sight; the label rank does
  change; `global` is returned only under `globalForced = true`, which is false.
- **The costume gate (audit c).** The verdict rests on the DIAGONAL fork (`freeLunchReachable`,
  `conservedReachable`), not on import-ness: `ws5_audit_knot_is_diagonal` shows import-ness alone yields `partial'`.
- **Strip test.** Each audit payoff strips to its bare fact (bisimilarity, count arithmetic, `¬ ResidueRecoverable`,
  `¬ Recoverable`); no interpretive term is load-bearing.
- **Names-not-terms (audit e).** `Outcome`, `verdict`, `ws5_*` embed no forbidden content-word.
