# WS3 design — Space is real-as-import; directed, granular, self-relative (2.4)

**Prove the lateral separation between peers is a genuine IMPORT (Series 07): two peers at breadth-distance
greater than one are non-recoverable over the plain relating, so collapsing space into time would require
recovering the lateral labels the relating cannot carry. Prove the metric is DIRECTED, GRANULAR, and stated
FOR a self (self-relative), grounded in the attention path (audit d), never absolute (audit a).**

## 1. Candidate constructions

1. **Distance as the count of import-labels between peers.** REJECTED: this is distance-as-number (audit d) —
   a facet of counting, not a geometry. The charter forbids it.
2. **Path-based metric on the local attention graph, grounded in `reachIn` (CHOSEN).** The breadth-distance is
   the directed attention-path length (`reachIn`), and the lateral coordinate `latW` is PROVED to equal the
   shortest such path length from the self `w0` — so the label is grounded in the graph, not a free count. The
   import is `¬ Recoverable latLiftW` (the lateral label survives the plain quotient, Series 07). See
   `spec/README.md` §2–3.

## 2. Triage

- **The import rests on Series 07.** `ws3_lateral_is_import := ¬ Recoverable latLiftW`, proved by exhibiting the
  plain bisimulation (`ws1_atomless_bisim`, the collapse engine — Series 07's wall) relating `w0,w2`, which is
  NOT a `lat`-bisimulation (the labels separate them). Same mechanism as `P2S0.ws3_direction_not_recoverable`.
- **Directed.** The metric inherits the knowing-asymmetry: there is a pair reachable in `n` forward but not in
  `n` backward (`reachIn attendsW 1 w0 w1 ∧ ¬ reachIn attendsW 1 w1 w0`), so the path metric is asymmetric.
- **Granular.** Step 0 is identity and there is a least positive step of length 1 (a smallest step, the spatial
  twin of the tick); ℕ-valued distance is discrete by construction.
- **Self-relative (audit a).** `latW` is the shortest path length FROM the named self `w0`; there is NO global
  two-argument absolute distance. A global metric would be the view from nowhere (the One), and is not asserted.
- **Not counting (audit d).** `reachIn` is genuine path reachability on the LOCAL (non-complete) graph
  (`w2 ∉ attendsW w0`); the grounding lemma ties `latW` to it, so the label is the path length, not a raw count.

## 3. Winning construction — typed signatures

```
-- (A) the lateral separation is a genuine import (Series 07): the lateral label is non-recoverable
theorem ws3_lateral_is_import (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (latLiftW hinf)

-- (B) the metric is DIRECTED: some pair is reachable forward but not backward at the same length
theorem ws3_directed :
    reachIn attendsW 1 w0 w1 ∧ ¬ reachIn attendsW 1 w1 w0 ∧ reachIn attendsW 2 w1 w0

-- (C) the metric is GRANULAR: step 0 is identity, and a smallest positive step (length 1) exists
theorem ws3_granular :
    (∀ x y : W, reachIn attendsW 0 x y ↔ x = y)
  ∧ (∃ x y : W, reachIn attendsW 1 x y ∧ x ≠ y)

-- (D) the metric is SELF-RELATIVE and path-grounded: latW is the shortest attention-path length from the self w0
theorem ws3_metric_grounded :
    ∀ x : W, x ∈ ({w0, w1, w2} : Finset W) →
      reachIn attendsW (latW x) w0 x ∧ ∀ m : ℕ, m < latW x → ¬ reachIn attendsW m w0 x
```

## 4. Directedness and the imported knowing-asymmetry

The world's directedness is the Series 2.0 knowing-asymmetry lifted to breadth: knowing runs one way, so the
attention path runs one way, so `dist` need not equal its reverse. `ws3_directed` witnesses this at the path
level; the connection to `P2S0.ws3_direction_not_recoverable` is prose (the imported ground the directedness
inherits), not a re-proof.

## 5. Outcome classes

- **Built (expected):** import + directed + granular + self-relative all discharged → the space is real-as-import
  and genuinely metric.
- **PARTIAL (pre-registered):** if directedness or granularity landed only degenerate (e.g. the metric symmetric,
  or no least step), reported as PARTIAL, not relabeled.

## 6. Strip annotation

- `ws3_lateral_is_import` → "a distance-greater-than-one pair is `¬ Recoverable`." A `Recoverable` fact (Series 07).
- `ws3_directed` → "the reachability relation is asymmetric." A bare relation fact.
- `ws3_granular` → "the length-0 reach is identity; a length-1 reach of distinct states exists." A bare graph fact.
- `ws3_metric_grounded` → "a labelling equals the shortest path length from a fixed basepoint." A graph-metric fact.
