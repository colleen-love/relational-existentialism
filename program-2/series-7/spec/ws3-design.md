# WS3 design — the import is the sole source (conservation modulo the import) (2.7)

**Prove that every change in `Q` is an IMPORT: any two configurations the self's sight identifies (plain-bisimilar)
that carry different `Q` differ by a `¬ Recoverable` distinction. So `Q` is conserved in the closed subsystem
(in-sight) and moves ONLY when an import crosses the boundary — the import the sole source, the only outside work
on the ledger, resting on Series 07 (`ws4_recoverable_not_import`). A genuine import that DOES change `Q` exists
(the source is non-vacuous). This is the general-relativity shape made precise: locally conserved, globally not,
the import the exogenous term (charter §2 WS3, §4.a).**

## 1. Candidate constructions

1. **`Q` changes ⇒ leaf (a descent difference).** REJECTED: on the atomless carrier every state is `SHNE`, so a
   change is never a leaf; ruling out the leaf forces the import (Series 07, `ws3_atomless_distinct_is_import`).
2. **`Q` changes ⇒ import, quantified over all in-sight-identified pairs (CHOSEN).** For any `x, y` with `rankM x ≠
   rankM y`, the rank lift plain-identifies them (collapse engine) yet is label-separated (the rank gap forces the
   labelled edges apart), so the distinction is NOT recoverable from the plain relating (`ws4_recoverable_not_import`,
   the negative horn contrapositive). The whole measure-lift is an import (`¬ Recoverable (destML hinf)`). The change
   is the import; the in-sight relating is the same.

## 2. Triage

- **The source is the import, resting on Series 07 (audit d).** `ws3_change_is_source` uses
  `ws4_recoverable_not_import` (transitively `P1.Core`): a recoverable label is not an import, contrapositive a
  label-separated plain-bisimilar pair is not recoverable. The import is quantified, never named (audit e, §4.e).
- **No global conservation (audit a).** The claim is "change ⇒ import," a LOCAL statement about the in-sight
  quotient; it does NOT assert `Q` globally conserved (the label rank does change). The import is the exogenous term.
- **Non-vacuous source (audit b, no fiat).** A genuine import that changes `Q` exists: `e1` vs `e0`
  (`AttentionDistinguishes`, `rankM e1 ≠ rankM e0`). The source is not empty.
- **Strip test.** `ws3_change_is_source` → "any two states with different rank that are plain-bisimilar are not
  label-bisimilar (`¬ Recoverable`)" — a bare separation fact resting on Series 07 (charter §0.3, WS3 annotation).
- **Names-not-terms (audit e).** `ws3_change_is_source`, `ws3_source_nonvacuous` embed no forbidden content-word.

## 3. Winning construction — typed signatures

```
-- the general rank-separation: a Q-change over the in-sight quotient is a label-import
theorem rankM_sep_general {κ} (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) (x y : MCar)
    (hlab : lab x ≠ lab y) (hne : (dest x).1 ≠ ∅) :
    ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y

-- THE PAYOFF: every change in Q is an import (plain-alike, label-apart, not recoverable), resting on Series 07
theorem ws3_change_is_source {κ} (hinf : ℵ₀ ≤ κ) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ ¬ Recoverable (destML hinf)

-- the source is non-vacuous: a genuine import that changes Q
theorem ws3_source_nonvacuous {κ} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (destML hinf) e1 e0 ∧ rankM e1 ≠ rankM e0
```

`rankM_sep_general` proved as in `ws4_linearization_import` / `firstOther_label_sep`: an outgoing edge of `x`
carries first-coordinate `lab x`; forward-matching under a label-bisim forces some edge of `y` with first-coordinate
`lab x`, but every edge of `y` carries `lab y`, so `lab x = lab y`, contradiction (needs `(dest x).1 ≠ ∅`). The
`AttentionDistinguishes` combines it with `ws1_atomless_bisim` on the plain quotient (`plainOf_rankLiftM`).
`¬ Recoverable (destML hinf)` from any one import via `ws4_recoverable_not_import` (contrapositive), using the `e1`,
`e0` witness.

## 4. Outcome classes

- `changeIsSource` is a WS5 flag. `!changeIsSource` in `verdict` returns `partial'` (the measure moves but not by an
  import — a degenerate, non-Series-07 source).
- If a `Q`-change were recoverable (in-sight visible, not an import), the conserved-relative reading would fail:
  the measure would move without an import — toward GLOBAL (a source the structure does not localize). Pre-registered,
  not reached.
