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

## 7. EXT-A1 — LOAD-BEARING self-relativity (Charter Extension 1)

The landed audit (a) is SINGLE-BASEPOINT: `ws3_metric_grounded` grounds `latW` as the shortest path FROM `w0`,
and asserts no absolute two-argument metric — the NEGATIVE content. Charter Extension 1 raises the bar to the
POSITIVE, load-bearing content: the metric genuinely VARIES by self, with no absolute frame reconciling the
selves. This is the Phase-2 thesis (every quantity is for a self) made a theorem. The DIRECTED ring already
carries it: distance from `w0` is `(w0,w1,w2) = (0,1,2)`; distance from `w1` is `(w1,w2,w0) = (0,1,2)`, i.e.
`w2` is FAR from `w0` (2) but NEAR `w1` (1). Nothing already proved is weakened; one payoff is added and audit
(a) is restated. `stepsFrom w0` grounds `latW` on the peers, so `ws3_metric_grounded` and the DISTINCT verdict
are preserved verbatim.

### New signature

```
-- the self-relative distance: shortest directed attention-path length FROM the self (arg 1) TO arg 2
noncomputable def stepsFrom (x y : W) : ℕ := sInf {n | reachIn attendsW n x y}

-- stepsFrom x y = k  iff  a path of length k exists and none shorter (the shortest-path characterization)
lemma stepsFrom_eq (x y : W) (k : ℕ) (hk : reachIn attendsW k x y)
    (hmin : ∀ m, m < k → ¬ reachIn attendsW m x y) : stepsFrom x y = k

theorem ws3_metric_source_relative :
    -- (1) the metric VARIES by self: two selves disagree at w2 (far from w0, near w1), so as functions differ
    ( stepsFrom w0 w2 = 2 ∧ stepsFrom w1 w2 = 1 ∧ stepsFrom w0 ≠ stepsFrom w1 )
    -- (2) directed: stepsFrom is not symmetric, so no undirected absolute d(x,y) exists either
  ∧ ( stepsFrom w0 w1 = 1 ∧ stepsFrom w1 w0 = 2 ∧ stepsFrom w0 w1 ≠ stepsFrom w1 w0 )
    -- (3) NO ABSOLUTE FRAME (load-bearing): no single g : W → ℕ is the distance for every self
  ∧ ( ¬ ∃ g : W → ℕ, ∀ x : W, stepsFrom x = g )
    -- (4) grounding: stepsFrom w0 IS latW on the peers, so ws3_metric_grounded / DISTINCT are preserved verbatim
  ∧ ( ∀ x : W, x ∈ ({w0, w1, w2} : Finset W) → stepsFrom w0 x = latW x )
```

### Triage

- **Load-bearing, not a dressed single basepoint (the EXT-A1 catch to avoid).** Conjunct (1) exhibits TWO selves
  whose distance functions genuinely DIFFER (not one self re-read); conjunct (3) proves no `g` reconciles them.
  Conjunct (2) makes it sharp via directedness — no symmetric absolute metric either. Conjunct (4) keeps the old
  grounding, so nothing is reopened.
- **Strip test.** Delete "distance," "self": "an indexed family of graph-distance functions that is non-constant
  in its index, with no single function equal to every member." A bare graph fact.
- **Audit (a), strengthened.** `ws5_audit_no_absolute_frame` is restated to conjoin `ws3_metric_grounded` (the
  kept negation) with `ws3_metric_source_relative`'s (1)+(3) (the added positive). Rests on both, none hand-set.

### Outcome classes (EXT-A1)

- **Fixed (expected):** `ws3_metric_source_relative` and the strengthened `ws5_audit_no_absolute_frame` built; the
  self-relativity load-bearing.
- **Relabeled (pre-registered):** if the self-varying metric could not be built (the directed ring forced a
  reconcilable frame), the obstruction is recorded and audit (a) demoted to the single-basepoint form. Not
  expected — the two distance functions above differ by inspection.
