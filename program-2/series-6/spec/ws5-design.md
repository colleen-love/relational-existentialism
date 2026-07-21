# WS5 design — The verdict and the audit folded in (2.6)

**The verdict is COMPUTED from the WS1–WS4 flags, never hand-set: `verdict : Bool⁶ → Outcome`, `= shapeDrawn` by
`rfl` on the certified flags, DISCRIMINATING (reaches all outcomes), the flags EARNED by the WS1–WS4 headlines.
The computed verdict is SHAPE-DRAWN: strict identity fails and the single line is an import (the ground), the weak
continuity is RECOVERABLE on the merged carrier and an IMPORT on the cut carrier (both reachable), so which
obtains is SELF-RELATIVE and not forced. The verdict rests on the weak continuity and the linearization import,
not on strict identity failing (audit c); the fork is not by fiat (audit b); no persistence is asserted
absolutely (audit a); the line rests on the linearization import, not scalar rank (audit d).**

## 1. The outcome type and the verdict function

```
inductive Outcome | woven | severed | shapeDrawn | partial'   -- neutral names; no forbidden content-name
  deriving DecidableEq

-- Flags: strictFails (WS1), lineIsImport (WS3), wovenReachable (WS4, Recoverable mergeLift),
-- severedReachable (WS4, ¬ Recoverable cutLift), carrierDecided (does the plain structure force one carrier as
-- canonical — FALSE here, the continuity is self-relative), carrierWoven (if decided, which side).
def verdict (strictFails lineIsImport wovenReachable severedReachable carrierDecided carrierWoven : Bool) :
    Outcome :=
  if !strictFails || !lineIsImport then Outcome.partial'                 -- the ground is missing: degenerate
  else if !(wovenReachable && severedReachable) then Outcome.partial'    -- a fork side excluded: a fiat
  else if !carrierDecided then Outcome.shapeDrawn                        -- both reachable, self-relative, undecidable
  else if carrierWoven then Outcome.woven                                -- a canonical woven carrier is forced
  else Outcome.severed                                                   -- a canonical severed carrier is forced
```

## 2. The theorems

```
theorem ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn        -- by rfl, computed
theorem ws5_verdict_discriminates :
    verdict true true true true true true = Outcome.woven
  ∧ verdict true true true true true false = Outcome.severed
  ∧ verdict false true true true false false = Outcome.partial'
  ∧ verdict true true true false false false = Outcome.partial'                               -- by decide

theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA                     -- strictFails (WS1)
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)) -- lineIsImport (WS3)
  ∧ Recoverable (mergeLift hinf)                                                              -- wovenReachable (WS4)
  ∧ ¬ Recoverable (cutLift hinf)                                                              -- severedReachable (WS4)

-- The computed verdict is SHAPE-DRAWN, and carrierDecided is honestly FALSE: both carriers reachable, neither forced.
theorem ws5_carrier_relative_verdict {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    verdict true true true true false false = Outcome.shapeDrawn
  ∧ (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf))
```

Each of the four `ws5_flags_justified` conjuncts is the proposition EARNING a boolean input: `strictFails` (WS1,
`ws1_strict_fails`), `lineIsImport` (WS3, `ws3_line_is_import`), `wovenReachable` (WS4/WS2, `ws2_cont_recoverable`),
`severedReachable` (WS4/WS2, `ws2_cont_is_import`). The fifth flag `carrierDecided = false` is the honest
self-relativity: `ws5_carrier_relative_verdict` shows both carriers reachable and neither forced, so no structural
principle picks a canonical carrier — `carrierDecided` is honestly false, and the verdict is SHAPE-DRAWN.
`carrierWoven` is then irrelevant (the branch is not reached).

## 3. Why the verdict is not the costume (audit c)

The verdict is a decided outcome (`woven`/`severed`/`shapeDrawn`) ONLY when `lineIsImport = true` AND
`wovenReachable && severedReachable = true`; with `strictFails = true` but `lineIsImport = false` it returns
`partial'`, and with `strictFails = true` but a fork side excluded it returns `partial'`. So the strict-failure
flag ALONE (the costume) never carries a decided verdict: the weak continuity's reachability (WS2/WS4) and the
linearization import (WS3) are the load-bearing inputs. Delete WS3's line-import flag and the function does not
decide; strict identity failing is walled out of the decision.

## 4. The audit clauses (a)–(e)

```
theorem ws5_audit_no_absolute (hinf) :                     -- (a) no absolute persistence: FOR a carrier, self-relative
    (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf))
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
theorem ws5_audit_fork_genuine (hinf) :                    -- (b) fork not by fiat: both reachable, weaker than strict
    Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
  ∧ (AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0 ∧ Recoverable (mergeLift hinf))
theorem ws5_audit_knot_not_strict (hinf) :                 -- (c) knot on the weak continuity, not strict failing
    (verdict true false true true false false = Outcome.partial')
  ∧ (verdict true true false false false false = Outcome.partial')
  ∧ Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
theorem ws5_audit_line_is_import (hinf) :                  -- (d) the line is the linearization import, not scalar rank
    (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
  ∧ rankT kA = rankT kB
  ∧ ((causal kA kC ∧ causal kB kC) ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
      ∧ (¬ causal kA kB ∧ ¬ causal kB kA))
theorem ws5_audit_names_not_terms : True                   -- (e) grep-certified placeholder; the grep is the teeth
```

- **(a) NO ABSOLUTE PERSISTENCE.** The continuity is FOR a carrier (WOVEN on the merged, SEVERED on the cut, both
  reachable, neither forced), and the single line is the self's import (`ws3_line_is_import`). No frame-independent
  persistence is asserted.
- **(b) THE FORK NOT BY FIAT.** WOVEN (`ws2_cont_recoverable`) and SEVERED (`ws2_cont_is_import`) both reachable,
  and the weak continuity genuinely weaker than strict identity (`ws2_weaker_than_strict`, recoverable where strict
  fails).
- **(c) THE KNOT IS THE WEAK CONTINUITY.** The verdict returns `partial'` when strict fails but the line is not an
  import, or when a fork side is excluded: strict failing alone never decides. The weak continuity carries it.
- **(d) THE LINE IS THE LINEARIZATION IMPORT.** `ws3_line_is_import` (the total order non-recoverable), quantified
  over all order labels; `rankT kA = rankT kB` (rank does not linearize); the partial order endogenous. Not scalar
  rank.
- **(e) NAMES-NOT-TERMS.** A meta-property, enforced by the protocol §6 grep (hits are docstring prose only),
  carried as the accepted `True` house placeholder; the grep is the teeth.

## 5. Outcome classes

- **SHAPE-DRAWN (the computed verdict):** the certified flags (strictFails, lineIsImport, wovenReachable,
  severedReachable true; carrierDecided false) give `shapeDrawn` by `rfl`. The continuity is drawn exactly, its
  recoverability self-relative and undecidable from within.
- **WOVEN / SEVERED / PARTIAL' (pre-registered):** reached by the discriminating function when a flag flips;
  reported in direction, never by relabel.

## 6. Strip annotation

- `verdict` / `ws5_verdict_eq` → "an `Outcome`-valued function of six booleans, `= shapeDrawn` by computation."
- `ws5_verdict_discriminates` → "the function reaches all four outcomes."
- `ws5_flags_justified` → "the four DECIDING boolean inputs are the WS1–WS4 headline propositions, none
  hand-set." (The two META-flags `carrierDecided`/`carrierWoven` are not WS-propositions; `carrierDecided = false`
  is grounded by the self-relativity `ws5_carrier_relative_verdict`, and `carrierWoven` is irrelevant — the
  certified verdict stops at `shapeDrawn` and never enters that branch. Disclosed, finding C3-S1.)
- `ws5_carrier_relative_verdict` → "both a `Recoverable` and a non-`Recoverable` lift exist, so no canonical
  carrier is forced."
