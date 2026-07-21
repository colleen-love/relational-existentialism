# WS5 design — The verdict and the audit folded in (2.5)

**The verdict is COMPUTED from the WS1–WS4 flags, never hand-set: `verdict : Bool⁵ → Outcome`, `= acyclic` by
`rfl` on the certified flags, DISCRIMINATING (reaches all outcomes), the flags EARNED by the WS1–WS4 headlines.
The five audit clauses (a)–(e) bundle the payoffs. The verdict rests on the COEXISTENCE (cyclic relating +
acyclic causation + the fold's uniqueness), not on well-foundedness alone (audit c).**

## 1. The outcome type and the verdict function

```
inductive Outcome | acyclic | looped | shapeDrawn | partial'   -- neutral names; no forbidden content-name
  deriving DecidableEq

-- Flags: relatingCycles (WS2), causationAcyclic (WS3), loopOnlyAtFold (WS4), loopedReachable (WS4 fiat-guard),
-- foldRealizedOnTower (whether the genuine tower realizes a self-membered fold point; FALSE on the tick carrier).
def verdict (relatingCycles causationAcyclic loopOnlyAtFold loopedReachable foldRealizedOnTower : Bool) :
    Outcome :=
  if !relatingCycles then Outcome.partial'          -- no cyclic relating: the coexistence is empty
  else if !(causationAcyclic && loopOnlyAtFold) then Outcome.shapeDrawn  -- tower not shown acyclic / loop not localized
  else if !loopedReachable then Outcome.partial'    -- LOOPED excluded by construction: a fiat
  else if foldRealizedOnTower then Outcome.looped   -- the genuine tower realizes the self-loop: time closes
  else Outcome.acyclic                              -- the coexistence: relating loops, causation acyclic, fold not realized
```

## 2. The theorems

```
theorem ws5_verdict_eq : verdict true true true true false = Outcome.acyclic          -- by rfl, computed
theorem ws5_verdict_discriminates :
    verdict true true true true true = Outcome.looped
  ∧ verdict true false true true false = Outcome.shapeDrawn
  ∧ verdict false true true true false = Outcome.partial'
  ∧ verdict true true true false false = Outcome.partial'                             -- by decide

theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ( (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ attendsT (reifyT cycleA) = cycleA )     -- relatingCycles (WS2)
  ∧ ( ¬ ∃ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x )               -- causationAcyclic (WS3)
  ∧ ( ∀ x : TCar, Relation.TransGen (causalDep attendsT isTick) x x
        → ∃ z, causalDep attendsT isTick z z )                                        -- loopOnlyAtFold (WS4)
  ∧ ( Relation.TransGen (causalDep attendsF compF) om om )                            -- loopedReachable (WS4)
  ∧ ( ¬ ∃ x : TCar, causalDep attendsT isTick x x )                                   -- foldRealizedOnTower = false
```

Each of the five conjuncts is the proposition EARNING the corresponding boolean input to `verdict`:
`relatingCycles` (WS2), `causationAcyclic` (WS3), `loopOnlyAtFold` (WS4, a causal loop forces a self-constituting
relatum, via `loop_forces_selfloop` on the WS3 rank-lift), `loopedReachable` (WS4), and `foldRealizedOnTower = false`
(the tick carrier has no self-membered composite). WS1's fold-as-diagonal is NOT a verdict flag; it grounds the
MEANING of "the fold" and enters the verdict story through audit (d) (`ws5_audit_fold_is_diagonal`,
resting on `ws1_fold`), which certifies that the sole loop candidate the verdict localizes is the diagonal's
self-membered point. (Phase D / finding C7-S1: the `loopOnlyAtFold` slot is now justified by the genuine
loop-forces-self-edge content, not by the rank-lift, and the WS1 entry point is named explicitly.)

## 3. Why the verdict is not the costume (audit c)

The verdict is ACYCLIC only when `relatingCycles = true` (else `partial'`) AND `loopedReachable = true` (else
`partial'`). So the ACYCLIC outcome genuinely combines the WS2 cyclic relating with the WS3 acyclic causation
and the WS4 fold uniqueness: delete the cyclic-relating flag and the function does not return ACYCLIC. It does
NOT strip to "a well-founded relation is acyclic" — that would need only `causationAcyclic`. The coexistence and
the fold's reachability are load-bearing inputs, not decoration.

## 4. The audit clauses (a)–(e)

- **(a) NO POLES DECIDED ABSOLUTELY.** `ws1_no_pole_below` (`SHNE`, reachability-relative) and `ws1_no_pole_above`
  (the reification section, no absolute ceiling); the fold is the only place ascent stops, named in prose only.
- **(b) THE FORK NOT BY FIAT.** `ws4_looped_reachable` (LOOPED a reachable structure) and `ws4_fold_no_rank`
  (the fold admits no rank-lift); `causalDep` is structural, its acyclicity PROVED (`ws3_causal_rank_lift`).
- **(c) THE KNOT IS THE COEXISTENCE.** `ws5_flags_justified` earns `relatingCycles` (WS2) beside
  `causationAcyclic` (WS3); the verdict demands both, so it rests on the coexistence, not rank alone.
- **(d) THE FOLD IS THE DIAGONAL.** `ws1_fold` and the second conjunct of `ws4_loop_only_at_fold` are
  `ws2_residue_distinct` / `ws1_no_self_total_hold`; no import theorem is invoked.
- **(e) NAMES-NOT-TERMS.** A meta-property, enforced by the protocol §6 grep (hits are docstring prose only),
  carried as the accepted `True` house placeholder; the grep is the teeth.

```
theorem ws5_audit_no_absolute_frame ...        -- (a) bundles ws1_no_pole_below, ws1_no_pole_above
theorem ws5_audit_fork_genuine ...             -- (b) bundles ws4_looped_reachable, ws4_fold_no_rank
theorem ws5_audit_knot_is_coexistence ...      -- (c) bundles ws2_relating_cycles, ws3_causation_acyclic
theorem ws5_audit_fold_is_diagonal ...         -- (d) bundles ws1_fold, ws4_loop_only_at_fold's diagonal conjunct
theorem ws5_audit_names_not_terms : True       -- (e) grep-certified placeholder
```

## 5. Outcome classes

- **ACYCLIC (expected):** the computed verdict on the certified flags (relatingCycles, causationAcyclic,
  loopOnlyAtFold, loopedReachable true; foldRealizedOnTower false).
- **LOOPED / SHAPE-DRAWN / PARTIAL' (pre-registered):** reached by the discriminating function when a flag
  flips; reported in direction, never by relabel.

## 6. Strip annotation

- `verdict` / `ws5_verdict_eq` → "an `Outcome`-valued function of five booleans, `= acyclic` by computation."
- `ws5_verdict_discriminates` → "the function reaches all four outcomes."
- `ws5_flags_justified` → "the five boolean inputs are the WS1–WS4 headline propositions, none hand-set."
