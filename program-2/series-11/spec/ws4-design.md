# WS4 design — the fork (INTERFERING vs ADDITIVE-ONLY, the knot)

**Target: prove the fork on two carriers, both genuine, neither by fiat. The frustrated cycle (odd holonomy) destructively interferes (combined weight below the parts); the gluable cycle (even holonomy) is additive (combined weight the constructive sum, not below the parts). Both from the SAME `amp`/weight — only the directed attention differs. The same fork Series 2.8 found (frustrated vs gluable) now decides interference vs classical.**

## The construction (typed signatures)

```
-- INTERFERING-reachable: the frustrated ring (hol = 3, odd) — opposite signs, weight strictly below parts.
theorem ws4_interfering_reachable :
    combinedWeight P2S8.attTri < partsWeight P2S8.attTri            -- 0 < 2

-- ADDITIVE-reachable: the gluable star (hol = 0, even) — equal signs, weight NOT below parts (constructive).
theorem ws4_additive_reachable :
    partsWeight P2S8.attStar ≤ combinedWeight P2S8.attStar         -- 2 ≤ 4
  ∧ combinedWeight P2S8.attStar = 4 ∧ partsWeight P2S8.attStar = 2
```

## Paper check
- INTERFERING: `attTri`, `loopAmp = amp 3 = -1`, `directAmp = 1`; `combined = (1-1)^2 = 0 < 2 = 1 + 1 = parts`. ✓
- ADDITIVE: `attStar`, `loopAmp = amp 0 = +1`, `directAmp = 1`; `combined = (1+1)^2 = 4`; `parts = 1 + 1 = 2`; `2 ≤ 4` and NOT below (the constructive factor `4 = 2·2`). ✓

## The fork is genuine, not by fiat
Interference is not built into `amp`/weight — the star (`attStar`) gives no cancellation (`4 ≥ 2`); the additive pole is not built in — the ring (`attTri`) cancels (`0 < 2`). Same `amp`, same `combinedWeight`/`partsWeight`, only the directed attention differs (`attTri` vs `attStar`). By `ws3_destructive_iff`, destructive happens EXACTLY on odd relative holonomy — a fact about which world you are in, decided by the built directedness, not a construction choice. This is Series 2.8's frustrated/gluable fork read one level up: the holonomy that made the common good frustrated now makes two paths cancel.

## Outcome classes
- **both reachable → INTERFERING:** interference genuine, the fork genuine. The expected close.
- interference reachable but additive not → fork by fiat → `partial'` (degenerate). (Not reached.)
- additive reachable, interference not → **ADDITIVE-ONLY**. (Not reached: `attTri` interferes.)
- neither → **shapeDrawn**.

## Strip test
Delete the words: "odd holonomy ⇒ weight below the parts; even holonomy ⇒ weight the sum." A bare pair of squared-sum inequalities on the built holonomy, one strict-below, one not-below. Survives.

## Audit clauses touched
- (b) fork not by fiat: both poles reachable from the same `amp`/weight, only the attention differing.
- (c) destructive not additive: the interfering side strict-below, the additive side not-below — the two are genuinely opposite, not the same fact relabelled.
