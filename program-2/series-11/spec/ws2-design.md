# WS2 design — cancellation (the raw material)

**Target: prove two contributions with opposite sign SUM TO ZERO — genuine subtraction, carried from Series 2.8's antisymmetry (`incr x y + incr y x = 0`) up to the sign. The first subtraction in the program's dynamics carried to a weight-bearing sign.**

## The construction (typed signatures)

```
-- Concrete: the direct and loop paths in the frustrated world carry opposite signs and cancel.
theorem ws2_amp_cancels :
    directAmp + loopAmp P2S8.attTri = 0            -- (+1) + (-1) = 0

-- General (earned, not two hand-picked values): opposite parity ⇒ the signs cancel.
theorem ws2_amp_cancels_general (m n : ℤ) (h : (m + n) % 2 = 1) :
    amp m + amp n = 0
```

## Paper check
`directAmp = amp 0 = +1`, `loopAmp attTri = amp 3 = -1`; `(+1) + (-1) = 0`. General: if `(m+n)%2 = 1` then one of `m,n` is even (sign `+1`) and the other odd (sign `-1`), so `amp m + amp n = 0` (parity cases, `omega`). The concrete is the instance `m = 0, n = 3` (`(0+3)%2 = 1`).

## Outcome classes
- **cancels:** opposite signs sum to zero → the raw material for interference present. Necessary but NOT sufficient (WS3 supplies the weight).
- If `amp` never took opposite signs → no cancellation → ADDITIVE-ONLY. (Not reached; WS1 signed.)

## Strip test
Delete "phase"/"amplitude"/"interference": "two opposite signs sum to zero"; general form "opposite-parity integers give signs summing to zero." A bare sign fact. Survives.

## Audit clauses touched
- (c) the costume watch: WS2 alone (sign sum = 0) is NOT interference — it is only the raw material; the WEIGHT below the parts (WS3) is required. WS2 is explicitly labelled necessary-but-not-sufficient.
