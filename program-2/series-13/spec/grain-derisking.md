# The paper hunt (`spec/grain-derisking.md`) — THE CURVE

**Read this first. The Phase B gate: before any workstream design, take the imported directed distance (Series 2.4's `stepsFrom`, the path-length metric) and the imported measure of distinction (Series 2.7's `rankM`, the grain), construct by hand two configurations with the SAME adjacency but DIFFERENT grain, and test whether the imported distance differs (GRAVITATIONAL) or is equal (INERT). Series 2.4's proof that space (the lateral axis) and the measure (the vertical rank) are DISTINCT axes is the prior for INERT. Only if the imported distance genuinely varies with the grain does GRAVITATIONAL earn the WS designs; if it is invariant, the series lands INERT (record the obstruction, skip to that verdict at WS5). No grain-weighted distance is built as the recovered object.**

---

## 1. The two imported objects, quantified

- **The distance** (Series 2.4, `P2S4.stepsFrom x y := sInf {n | reachIn attendsW n x y}`). It is the shortest DIRECTED attention-path length from `x` to `y`: a function of the ADJACENCY `attendsW` (the directed reachability) and NOTHING else. `stepsFrom` takes no rank/grain argument; its entire input is the adjacency. Re-seated for this series as `pathDist : Adj → S → S → ℕ` (a fuel-computed least-path-length, decidable on `Fin 4`), definitionally the same object and, like `stepsFrom`, a function of the adjacency alone.

- **The grain** (Series 2.7, `P2S7.rankM : MCar → ℕ`, the reification rank, the measure of distinction — `ws1_rank_nontrivial`: non-constant, the difference a genuine import). Re-seated as `grain : S → ℕ`, a measure over the relata, genuinely non-constant.

- **The adjacency** is the directed reachability structure over the relata — exactly the input `stepsFrom`/`pathDist` reads.

## 2. The construction (same adjacency, different grain)

Fix one adjacency, the forward chain `aChain : p0 → p1 → p2 → p3`. Put two grains on it:

- `gFlat := fun _ => 0` (every relatum carries no distinction);
- `gBump := fun x => if x = p3 then 1 else 0` (the far relatum `p3` carries one unit of distinction).

`gFlat ≠ gBump` (they differ at `p3`), so the grain genuinely changes, and `gBump` is non-constant (`gBump p3 = 1 ≠ 0 = gBump p0`). The two configurations `cfgFlat := (aChain, gFlat)` and `cfgBump := (aChain, gBump)` have the SAME adjacency (`aChain`) and DIFFERENT grain. This is the exact experiment the charter poses: pack more of the measure into a region (bump `p3`), hold the connections fixed, and ask whether the distances around it bend.

## 3. The test by hand

Compute the imported distance on both configurations. Because `pathDist` reads only the adjacency component, and the adjacency is identical (`aChain`), the distance is IDENTICAL on both:

| pair | `pathDist aChain` (both cfgFlat and cfgBump) |
|------|----------------------------------------------|
| `p0 → p1` | 1 |
| `p0 → p2` | 2 |
| `p0 → p3` | 3 |
| `p3 → p0` | 4 (sentinel: unreachable — directed) |

Every entry is the same for `cfgFlat` and `cfgBump`. The grain moved (`p3` gained a unit); no distance changed. The imported distance is INVARIANT under the grain-change at fixed adjacency. (Verified by `decide` in the prototype: `¬ grainDependent adjDist cfgFlat cfgBump`.)

## 4. The verdict of the hunt: INERT

**The imported distance does NOT vary with the grain at fixed adjacency.** This is not a near miss to be tuned away; it is structural. `stepsFrom`/`pathDist` is a function of the adjacency alone — it has no channel through which the grain could enter. The grain can be anything; the distance does not move. GRAVITATIONAL (the grain sources the distance) does NOT earn its recovery on the imported object.

This is exactly the outcome Series 2.4 foretells. Series 2.4 proved the lateral axis (space, `latW`/`stepsFrom`) and the vertical axis (the measure, `rankW`) are DISTINCT: neither is a function of the other (`ws4_two_axes`, `ws5_audit_no_absolute_frame`). Gravity is precisely the coupling of those two axes — the measure curving the distance. This world built them apart. So the honest report is INERT: geometry decoupled from the grain, no gravity; and the specification for the next iteration is to couple the two axes Series 2.4 kept distinct.

## 5. Does INERT trigger the "skip to WS5" clause?

The protocol permits skipping the WS designs and landing INERT directly when the imported distance is invariant. It does NOT require it. Because the INERT finding is itself the capstone result of the built arc, it deserves the full workstream treatment: the ground (WS1: a non-constant grain and a non-trivial distance both exist, so the test is non-degenerate), the baseline (WS2: the distance is a function of the adjacency, and genuinely responds to it — it is not a rigged constant), the anti-costume core (WS3: the imported distance is invariant under grain-change, and it is the imported object, not a grain-weighted gadget), and the honest fork (WS4: INERT reached by the imported distance; the GRAVITATIONAL pole shown inhabited only by a counterfactual foil, so the fork is genuine and not a fiat). The WS designs build INERT as a proved, discriminated verdict, not a default. This also keeps the audit teeth (a)-(e) fully exercised on the landing.

## 6. The one thing NOT built

No grain-weighted distance is built as the recovered metric. A single COUNTERFACTUAL FOIL (`foilDist c x y := pathDist c.1 x y + c.2 y`, a by-hand grain-weighting) is exhibited in WS4 ONLY to witness that the grain-dependence test has a genuine positive side — that GRAVITATIONAL is a reachable verdict of the test for SOME distance function, so the INERT of the imported distance is a substantive finding and not a vacuous one. The foil is proved DISTINCT from the imported distance (the object under test), and the verdict rests on the imported distance alone. This is the Series 2.12 `partsWeight` pattern: a built alternative the discipline fences off from the recovered object, never passed off as the recovery. The no-smuggling gate (audit a) certifies the metric under test reads only the adjacency.

## 7. Forward-note (carried, not built)

The area law — that a region's information is bounded by its BOUNDARY, not its volume (Bekenstein, the holographic principle) — is the hardest, least-certain piece and is NOT this series' target. It is the disclosed forward-note, the deepest unbuilt question of the whole recovery. This series claims at most a grain-dependence test on the model's own distance; it lands INERT, which claims even less than a proportionality.
