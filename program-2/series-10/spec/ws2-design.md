# Series 2.10 WS2 design (`spec/ws2-design.md`) — the full tick is not invertible (the irreversible headline)

**Prove the FULL tick is NOT a measure-preserving bijection: it is non-injective under the collapse (distinct configurations identified) AND it raises the built rank (not measure-preserving). This is the honest starting point — the top-level dynamics is one-way — and WS3/WS4 ask whether a CORE escapes it.**

## 1. The two obstructions (both `decide`-checkable on the built tick)

From the derisking table (§1): `tick e0' = e0` and `tick e2 = e0` with `e0' ≠ e2` (two distinct states collapse to one — non-injective); and `mu (tick e0) = 1 ≠ 0 = mu e0` (the rank rises — not measure-preserving).

## 2. The payoff signature

```
/-- **THE FULL TICK IS NOT A MEASURE-PRESERVING BIJECTION (WS2).** (i) NOT injective: two distinct configurations
`e0' ≠ e2` are identified (`tick e0' = tick e2 = e0`) — the collapse engine's identification, so not a bijection.
(ii) NOT measure-preserving: the tick RAISES the built rank (`mu (tick e0) = mu e0 + 1`), so it cannot be run
backward as it stands. Either obstruction alone defeats invertibility; both hold. -/
theorem ws2_tick_not_invertible :
    ¬ Function.Injective tick
  ∧ (∃ x : Cfg, mu (tick x) ≠ mu x)
  ∧ mu (tick e0) = mu e0 + 1 := by
  refine ⟨?_, ⟨e0, by decide⟩, by decide⟩
  intro h
  have : e0' = e2 := h (by decide)     -- tick e0' = tick e2, but e0' ≠ e2
  exact absurd this (by decide)
```

The third conjunct is the explicit rank-rise (audit d), the same fact as `P2S7.ws2_tick_raises.1`.

## 3. Strip test and outcome classes

- **Strip test.** Delete "tick," "invertible": the bare facts are "a built map `f` is not injective" and "`rankM (f e0) ≠ rankM e0`." Plain injectivity / arithmetic facts; no interpretive term carries them.
- The verdict function returns `partial'` on `¬notInvertible` (a top-level-invertible tick would be incoherent with the raising rank); it does not materialise.

## 4. Audit hooks

- (a) NO INVERSE SMUGGLED — WS2 asserts the tick is NOT invertible; it introduces no inverse map.
- (c) DECODABILITY IS NOT REVERSAL — WS2 is about the tick as a STATE map (injectivity, measure), independent of the pattern-level section (WS3).
- (d) THE MEASURE IS THE BUILT RANK — `mu = rankM`; the rise is `ws2_tick_raises.1`.
- (e) NAMES-NOT-TERMS — `ws2_tick_not_invertible` ("invertible" is not a forbidden word) carries no forbidden content-word.
