# WS1 design — The world and the two gradings (2.4)

**Build THE WORLD: a genuine lateral population of same-rank peers over the attention carrier, with a LOCAL
attention graph, and the two gradings on it. Prove the world is genuinely lateral and populated (same-rank
peers at breadth-distance greater than one), non-recoverable, and not a tower.**

## 1. Candidate constructions

The two key design objects are the WORLD (a lateral population with a local attention graph) and the
breadth-DISTANCE. Candidates weighed:

1. **Complete graph of same-rank peers.** REJECTED: a complete attention graph makes every pair adjacent
   (distance 1), so distance carries no structure — it collapses to bare label-counting (audit d fails). No
   "far," only "near." Not a geometry.
2. **Undirected line/path of peers.** REJECTED: an undirected graph gives a symmetric metric, contradicting
   the directedness the charter requires (the metric must inherit the Series 2.0 knowing-asymmetry, WS3). A
   symmetric distance would be a weaker object than the directed knowing already forces.
3. **Directed ring of same-rank peers + a reified peer (CHOSEN).** A directed 3-ring `w0 → w1 → w2 → w0`
   (local: each attends only its successor, so `w2` is two steps from `w0`, real extent) with all peers at rank
   0 (same-rank, lateral), plus one reified peer `r` at rank 1 sharing the self's lateral coordinate (the
   vertical witness). Directed (the ring is one-way), granular (ℕ-valued path length, smallest step 1),
   local/non-complete (`w2 ∉ attendsW w0`), and same-rank (the lateral population). This is the minimal carrier
   carrying real extent, directedness, same-rank multiplicity, and a vertical witness. See `spec/README.md` §2.

## 2. Triage (against non-triviality, strip test, costume gate, audit)

- **Non-triviality.** The world has ≥ 2 same-rank peers at path-distance exactly 2 (`w0`, `w2`), witnessed by
  `reachIn`, not posited. The graph is non-complete (`w2 ∉ attendsW w0`), so distance is genuine.
- **Strip test.** Delete "world," "space": the payoff is "a set of same-rank states (`rankW w0 = rankW w2`),
  pairwise non-recoverable (`AttentionDistinguishes latLiftW w0 w2`), with a non-complete reachability relation
  (`w2 ∉ attendsW w0 ∧ reachIn attendsW 2 w0 w2`)." Survives as a bare graph/order fact.
- **Costume gate.** WS1 builds the multiplicity, which is the Series 07 import — the acknowledged GROUND, not
  the finding. WS1 does NOT claim the verdict; it lays the world. The finding (axis-independence) is WS2/WS4.
- **Audit d.** The metric is path-based (`reachIn`) on a local graph, not a label-count.

## 3. Winning construction — typed signatures

```
abbrev W : Type := Fin 4
def w0 : W := 0   def w1 : W := 1   def w2 : W := 2   def r : W := 3
def attendsW : W → Finset W          -- w0↦{w1}, w1↦{w2}, w2↦{w0}, r↦{w1}
def rankW : W → ℕ                    -- w0,w1,w2 ↦ 0 ; r ↦ 1     (the vertical grading)
def latW  : W → ℕ                    -- w0↦0, w1↦1, w2↦2, r↦0     (the lateral coordinate)
def reachIn (att : W → Finset W) : ℕ → W → W → Prop   -- length-indexed directed reach
noncomputable def rankLiftW (hinf : ℵ₀ ≤ κ) : W → LkObj κ (ULift ℕ) W := rankLift (outDest hinf attendsW) rankW
noncomputable def latLiftW  (hinf : ℵ₀ ≤ κ) : W → LkObj κ (ULift ℕ) W := rankLift (outDest hinf attendsW) latW

-- every node SHNE (so any two nodes are plain-bisimilar via ws1_atomless_bisim)
lemma ws1_W_SHNE (hinf : ℵ₀ ≤ κ) (x : W) : SHNE (outDest hinf attendsW) x

-- (A) the world is genuinely lateral: two same-rank peers at path-distance exactly 2 (> 1), real extent
theorem ws1_world_is_lateral :
    rankW w0 = rankW w2 ∧ w0 ≠ w2
  ∧ reachIn attendsW 2 w0 w2 ∧ ¬ reachIn attendsW 1 w0 w2 ∧ ¬ reachIn attendsW 0 w0 w2

-- (B) the peers are non-recoverable from each other (the lateral separation an import, Series 07)
theorem ws1_peers_non_recoverable (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (latLiftW hinf) w0 w2

-- (C) not a tower: the attention graph is LOCAL (non-complete) and rank is non-injective (same-rank multiplicity)
theorem ws1_not_collapsed (hinf : ℵ₀ ≤ κ) :
    (w2 ∉ attendsW w0 ∧ reachIn attendsW 2 w0 w2)
  ∧ (rankW w0 = rankW w2 ∧ w0 ≠ w2)
  ∧ (∀ x : W, Cardinal.mk (↥((outDest hinf attendsW x).1)) < Cardinal.aleph0)   -- finite bound, S0
```

## 4. Outcome classes

- **Built (expected):** `ws1_world_is_lateral`, `ws1_peers_non_recoverable`, `ws1_not_collapsed` all discharged.
  The world holds; it is genuinely lateral, non-recoverable, not a tower.
- **REDUCED-toward (pre-registered obstruction):** if a genuine lateral population could not be built without a
  tower — same-rank peers forced to collapse — that is reported toward REDUCED, not relabeled. (Not expected:
  same-rank peers already exist in the Series 2.2 texture; the ring lifts them to real extent.)

## 5. Strip annotation (what each payoff SHOULD strip to)

- `ws1_world_is_lateral` → "two same-rank states at reachability-distance 2, not adjacent." A graph-metric fact.
- `ws1_peers_non_recoverable` → "a distinct pair, plain-bisimilar yet label-separated." A `Recoverable` fact.
- `ws1_not_collapsed` → "a non-complete reachability relation with non-injective rank." An order/graph fact.

Nothing here asserts a distance absolutely, decides the reduction, or rests on multiplicity as the finding.
