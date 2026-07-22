# WS2 design — the baseline: the distance is a function of the adjacency (2.13)

**Prove that Series 2.4's distance is determined by the ADJACENCY (the directed reachability) — the geometry the model built reads the connections. This fixes what "the grain sources the distance" would ADD: a dependence on the measure beyond the adjacency. And prove the distance genuinely RESPONDS to the adjacency (it is not a rigged constant), so the INERT verdict of WS3/WS4 is substantive: the distance is alive to the connections, blind to the grain.**

## Imported / prior objects

- WS1: `pathDist`, `adjDist`, `aChain`, `aStar`, `Config`. `adjDist c := pathDist c.1` (the imported distance read over configurations; reads the adjacency component only).

```lean
-- the imported distance as a distance over configurations: reads the adjacency component ONLY.
def adjDist (c : Config) (x y : S) : ℕ := pathDist c.1 x y
```

## Signatures

```lean
-- THE DISTANCE IS A FUNCTION OF THE ADJACENCY (WS2). Two configurations with the same adjacency have the
-- same imported distance: the geometry reads the connections, nothing else about the configuration.
theorem ws2_metric_from_adjacency (c1 c2 : Config) (h : c1.1 = c2.1) :
    ∀ x y, adjDist c1 x y = adjDist c2 x y

-- THE DISTANCE GENUINELY RESPONDS TO THE ADJACENCY (WS2). It is not a rigged constant: a different
-- adjacency gives a different distance (`pathDist aChain p0 p3 = 3 ≠ 1 = pathDist aStar p0 p3`). The
-- distance is ALIVE to the connections — which makes its blindness to the grain (WS3) a real finding.
theorem ws2_metric_reads_adjacency : ∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y
```

## Proofs

- `ws2_metric_from_adjacency`: `intro x y; simp only [adjDist, h]`. Since `adjDist c = pathDist c.1` and `c1.1 = c2.1`, the two sides are equal. Verified in the prototype.
- `ws2_metric_reads_adjacency`: `⟨p0, p3, by decide⟩` (`3 ≠ 1`). Verified.

## Strip test

Delete "distance," "adjacency," "geometry": `ws2_metric_from_adjacency` reads as `(c1.1 = c2.1) → ∀ x y, pathDist c1.1 x y = pathDist c2.1 x y` — a bare congruence of `pathDist` under equality of its argument. `ws2_metric_reads_adjacency` reads as `pathDist` is non-constant across two arguments. Both survive as arithmetic facts.

## Costume watch

`ws2_metric_from_adjacency` is the baseline the grain-dependence would have to EXCEED, and `ws2_metric_reads_adjacency` forecloses the fiat "the distance is inert because it is a dead constant." Together: the distance reads the adjacency and genuinely varies with it, so its invariance under the grain (WS3) is a substantive decoupling, not a triviality. This is the code-level face of Series 2.4's `ws4_two_axes`: the lateral axis (the distance) is a real, live grading distinct from the vertical one (the grain).
