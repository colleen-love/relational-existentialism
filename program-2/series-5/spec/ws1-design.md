# WS1 design — The fold and the poles (the ground) (2.5)

**Prove the topology of the whole: NO SMALLEST (atomlessness, nothing bottoms out), NO LARGEST (unbounded
reification, from any relatum a higher reified relatum), THE FOLD (the totalizing self-inspection yields a
residue point it cannot contain, so the largest bends into the smallest through the diagonal, the seam the
self-membered point), and the NUMBER-FACE (the whole cannot count itself). The fold rests on the P1 diagonal
(`ws2_residue_free` / `ws1_no_self_total_hold`), NOT on a seated import (audit d).**

## 1. Candidate constructions

1. **The fold via the Series 07 import theorem (a subsingleton collapse).** REJECTED: that is the import's
   engine, not the diagonal's, and audit (d) forbids resting the fold on a seated import. The fold is generated
   from within (self-inspection's residue), not required from without.
2. **No-largest by an absolute rank ceiling on a finite witness.** REJECTED: a finite carrier has a maximal
   rank, so "no largest" would be false there; and a ceiling is exactly the pole the charter denies. The honest
   "no largest" is the UNBOUNDEDNESS of reification: from any relatum you can reify again.
3. **The fold as the diagonal's residue, the poles as atomlessness + unbounded reification (CHOSEN).** No
   smallest is `SHNE` on the tick carrier (every reachable node has a nonempty successor: nothing bottoms out).
   No largest is the reification section: from any `x`, `reify {x}` is a higher relatum whose sole constituent
   is `x`, coinciding with `x` ONLY at a self-membered fold point. The fold is `ws2_residue_distinct` +
   `ws1_no_self_total_hold` (the largest self-inspection misses the residue point; the self-total seam is
   unrealizable). The number-face is `ws1_insp_not_surjective` (Cantor: no inspection enumerates all contents).

## 2. Triage

- **No pole decided absolutely (audit a).** No-smallest is `SHNE` (a structural, reachability-relative
  property), no-largest is the reification section producing a fresh relatum from any pattern; neither asserts a
  topological quantity frame-independently. The one place ascent can stop is a self-membered point (the fold),
  named in prose only.
- **The fold on the diagonal (audit d).** `ws1_fold` is `ws2_residue_distinct` conjoined with
  `ws1_no_self_total_hold`; `ws1_no_total_count` is `ws1_insp_not_surjective`. All three are the P1 diagonal,
  no import.
- **Strip test.** `ws1_no_pole_below` strips to "every reachable node has a nonempty successor set" (no leaf);
  `ws1_no_pole_above` to "a section of the finite functor sends `x` to a relatum whose sole constituent is `x`,
  equal to `x` only when `x` is self-membered"; `ws1_fold` to "no hold realises the residue, and no self-total
  hold exists" (a bare self-membership/diagonal fact); `ws1_no_total_count` to "no map onto its content-space is
  surjective" (Cantor). None mentions time, loop, or the fold as a term.

## 3. Winning construction — typed signatures

```
-- No smallest: nothing bottoms out (atomless), on the tick carrier `TCar` (P2S1, transitive).
theorem ws1_no_pole_below {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) (x : TCar) :
    SHNE (outDest hinf attendsT) x

-- No largest: from any relatum, reification yields a higher relatum (sole constituent x),
-- coinciding with x only at a self-membered fold point.
theorem ws1_no_pole_above {X : Type u} (attends : X → Finset X) (reify : Finset X → X)
    (h : FinReify attends reify) (x : X) :
    attends (reify {x}) = {x} ∧ (reify {x} = x → attends x = {x})

-- The section the poles use exists non-vacuously (P2S0 `ws1_reification_exists`).
theorem ws1_reify_nonvacuous :
    ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X),
      FinReify attends reify ∧ Function.Injective reify

-- The fold, drawn by the diagonal: the largest self-inspection misses the residue point
-- (the largest bends into the smallest), and the self-total seam is unrealizable.
theorem ws1_fold {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ h, insp h ≠ residue insp) ∧ (¬ ∃ t, SelfTotal insp t)

-- The number-face: the whole cannot count itself (Cantor; no inspection enumerates all contents).
theorem ws1_no_total_count {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ Function.Surjective insp
```

## 4. Why the fold is the diagonal, not the import (audit d)

The fold is "the largest bending into the smallest": the totalizing act (a self-inspection over all holds)
produces a residue — a single content (the smallest, a point) — that NO hold realises (`ws2_residue_distinct`),
and the self-total seam Ω = {Ω} at the level of inspection is unrealizable (`ws1_no_self_total_hold`). Both are
`P1.Core`'s diagonal, proved with no bisimulation and no atomlessness hypothesis and no import theorem. The
Series 07 import (`ws2_import_theorem`) is never invoked in WS1.

## 5. Outcome classes

- **The fold exhibited (expected):** `ws1_fold` and the two poles hold; the ground is drawn, and the loop lives
  on it (WS4).
- **OBSTRUCTED (pre-registered, honest):** if the fold could not be exhibited without importing a distinction,
  that is reported as the obstruction, never relabeled.

## 6. Strip annotation

- `ws1_no_pole_below` → "no reachable node bottoms out" (no leaf).
- `ws1_no_pole_above` → "a finite section yields, from any `x`, a relatum whose only constituent is `x`,
  equal to `x` only at a self-membered point."
- `ws1_fold` → "no hold realises the residue; no self-total hold exists" (self-membership / diagonal).
- `ws1_no_total_count` → "no inspection is surjective onto contents" (Cantor).
