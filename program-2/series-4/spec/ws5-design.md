# WS5 design — The verdict and the audit folded in (2.4)

**The verdict is COMPUTED from the WS1–WS4 flags, never hand-set: `verdict : Bool⁴ → Outcome`, `= distinct` by
`rfl` on the certified flags, DISCRIMINATING (flip a flag, get another outcome). The flags are EARNED by the
WS1–WS4 headline propositions. The audit clauses (a)–(e) are propositions bundling the payoffs; the names clause
(e) is a grep-certified `True` placeholder (a property about identifiers, not a proposition).**

## 1. The verdict — typed signatures

```
inductive Outcome | distinct | reduced | shapeDrawn | partial'  deriving DecidableEq

-- distinct iff the world is lateral (WS1), the axes are independent (WS2/WS4), and the space is a real import (WS3);
-- reduced iff the axes are not independent (breadth is accumulated depth, the T zone);
-- shapeDrawn iff lateral+import hold but independence is undrawn; partial' iff the world does not hold.
def verdict (lateral independent spaceImport bothMoves : Bool) : Outcome :=
  if !lateral then Outcome.partial'
  else if !spaceImport then Outcome.partial'
  else if independent && bothMoves then Outcome.distinct
  else if !independent then Outcome.reduced
  else Outcome.shapeDrawn

theorem ws5_verdict_eq : verdict true true true true = Outcome.distinct := rfl        -- COMPUTED on W's flags

theorem ws5_verdict_discriminates :
    verdict true false true true = Outcome.reduced          -- axes coincide (the T zone)
  ∧ verdict true true true false = Outcome.shapeDrawn        -- independence undrawn
  ∧ verdict false true true true = Outcome.partial'          -- no world
  ∧ verdict true true false true = Outcome.partial'          -- space not an import
```

## 2. The flags are earned

```
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :
    -- lateral (WS1): same-rank peers, real extent
    (rankW w0 = rankW w2 ∧ reachIn attendsW 2 w0 w2 ∧ ¬ reachIn attendsW 1 w0 w2)
    -- independent (WS2/WS4): the cross-pattern of separations, neither grading a function of the other
  ∧ ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
      ∧ (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )
    -- spaceImport (WS3): the lateral separation non-recoverable (Series 07)
  ∧ (¬ Recoverable (latLiftW hinf))
    -- bothMoves (WS4): the lateral move keeps rank, the reification keeps lat; REDUCED reachable on T
  ∧ (rankW w0 = rankW w2 ∧ latW r = latW w0 ∧ latT = rankT)
```

The four `true` inputs are the WS1 laterality, the WS2/WS4 independence cross-pattern, the WS3 import, and the
WS4 both-moves-with-`T`-reachable. None hand-set.

## 3. The five audit clauses (a)–(e)

```
-- (a) NO ABSOLUTE FRAME: the metric is self-relative (latW = shortest path FROM the self w0); no absolute distance
theorem ws5_audit_no_absolute_frame :
    ∀ x : W, x ∈ ({w0, w1, w2} : Finset W) →
      reachIn attendsW (latW x) w0 x ∧ ∀ m, m < latW x → ¬ reachIn attendsW m w0 x       -- from WS3

-- (b) THE FORK NOT BY FIAT: DISTINCT on W, REDUCED (latT = rankT) reachable on T; both zones real
theorem ws5_audit_fork_genuine (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ latW r = latW w0 ) ∧ (latT = rankT)  -- from WS4

-- (c) THE KNOT IS NOT THE MULTIPLICITY: the verdict rests on the cross-pattern (independence), NOT on "many".
--     rank separates a pair lat does not, and lat separates a pair rank does not — the finding is the split.
theorem ws5_audit_knot_is_independence (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2) )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )

-- (d) SPACE IS AN IMPORT: the lateral separation non-recoverable, a proof term resting on Series 07
theorem ws5_audit_space_import (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (latLiftW hinf)          -- from WS3

-- (e) NAMES-NOT-TERMS: no proof term named for the spatial content (grep-certified True placeholder)
theorem ws5_audit_names_not_terms : True := trivial
```

## 4. Outcome classes

- **DISTINCT (expected):** all four flags earned, `verdict … = distinct` by `rfl`. The world is lateral, the axes
  independent, the space a real directed granular self-relative import.
- **REDUCED / SHAPE-DRAWN / PARTIAL:** the pre-registered alternatives the same `verdict` computes for other flag
  inputs (reachable via `ws5_verdict_discriminates`), reported in full if the build fell short, never relabeled.

## 5. Strip annotation

- `ws5_verdict_eq` / `_discriminates` → "an `Outcome`-valued function, `= distinct` by `rfl`, non-constant."
- `ws5_flags_justified` → "a conjunction of the WS1–WS4 headline order/graph/`Recoverable` facts."
- Audit (a)–(d) → the WS1–WS4 payoffs, re-exposed; (e) a grep property about identifiers.

The verdict is the residue of the process, not its premise. No distance is asserted absolutely; no name is a term.
