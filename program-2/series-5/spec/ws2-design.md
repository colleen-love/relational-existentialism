# WS2 design — The relating loops (attention is cyclic) (2.5)

**Prove the RELATING genuinely cycles: a directed attention cycle exists (a attends b attends a), and the cycle
reifies into its own relatum. So at the level of bare relating there are genuine loops; whether they are CAUSAL
is WS3/WS4. Built on Series 2.0/2.1's `ws1_cycle_reifies`.**

## 1. Candidate constructions

1. **A fresh 3-cycle carrier `a → b → c → a`.** Coherent, but re-forges what Series 2.1 already built and
   re-proves its `SHNE` / reification facts; the cycle-reification is not new content here.
2. **Reuse the Series 2.1 tick witness `TCar` (CHOSEN).** `TCar` (transitive, via `P2S4`) already carries a
   GENUINE directed cycle `p0 ⇄ p1` (`p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1`) that reifies into the composite
   `kA = reifyT cycleA`, sectioning its pattern (`attendsT (reifyT cycleA) = cycleA`). The SAME carrier serves
   WS3 (the causal relation is acyclic on it) and WS4 (no fold point on it), so the coexistence — cyclic relating
   with acyclic causation — is witnessed on ONE structure, not split across carriers.

## 2. Triage

- **Genuine cycle, not a self-loop artifact.** `p0 ⇄ p1` is a length-2 directed cycle between DISTINCT base
  relata (`p0 ≠ p1`), forged in Series 2.1, not a degenerate self-loop.
- **The cycle reifies.** `reifyT cycleA = kA` and `attendsT (reifyT cycleA) = cycleA`: the loop becomes a
  relatum of the SAME field, attending exactly its cycle. This is the reification the causal question needs.
- **Coexistence ground (audit c).** The cycle `p0 ⇄ p1` is in the RELATING (`attendsT`), and the base relata
  `p0`, `p1` are NOT reified composites, so they carry NO causal edge (WS3's `causalDep` requires the target be
  a composite). The relating loops where causation does not: the two live on one carrier.
- **Strip test.** The payoff strips to "a directed 2-cycle in a relation, which reifies to a relatum sectioning
  its pattern." No "time," "loop," or "cycle" as a proof term; the cycle is `p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1`.

## 3. Winning construction — typed signatures

```
-- The relating genuinely cycles: a directed attention cycle exists and reifies (on TCar, from `ws1_cycle_reifies`).
theorem ws2_relating_cycles :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1)          -- a directed 2-cycle between distinct base relata
  ∧ reifyT cycleA = kA                              -- the cycle reifies to the composite
  ∧ attendsT (reifyT cycleA) = cycleA              -- the composite attends exactly its cycle (a real section)
```

## 4. Why this is the relating loop, not the causal one

The edges `p0 → p1 → p0` are WITHIN-cycle relating: `p0` and `p1` are base relata, not composites, so no causal
(reification-dependency) edge runs among them (WS3's `causalDep attendsT isTick` requires `isTick u`, and
neither `p0` nor `p1` is a tick). The cycle reifies UPWARD into `kA` (a composite), and the causal edges run
`p0 → kA`, `p1 → kA` (rank 0 → rank 1), which do NOT close. So the relating loop and the causal non-loop coexist
on the one carrier: exactly the WS4 knot's ground.

## 5. Outcome classes

- **The relating cycles (expected):** `ws2_relating_cycles` holds; the loop at the level of bare relating is
  genuine, and the question passes to whether it is causal (WS3/WS4).
- **DEGENERATE (pre-registered):** if no genuine directed cycle could be exhibited (only self-loops), the
  relating would not "genuinely cycle," reported as the obstruction.

## 6. Strip annotation

- `ws2_relating_cycles` → "a directed 2-cycle in a relation that reifies into a relatum sectioning its pattern."
  A bare cycle-plus-reification fact, no temporal content.
