# Program 2 Series 4 (2.4) — Design index (`spec/README.md`)

**SPACE, and the world it lives on. This is the design batch for Series 2.4: the WORLD (a genuine lateral
population of same-rank import-distinguished peers with a LOCAL attention graph) and the two GRADINGS on it
(a directed granular self-relative breadth-distance, and the reification depth). It fixes the shared witness,
the imported chain, the discipline, the cross-workstream triage, the outcome classes, and the names-in-prose
rule. Committed as one batch with `ws1-design.md`…`ws5-design.md` before any `formal/` file exists (Phase B gate).**

---

## 1. The imported chain (reached, not rebuilt)

Series 2.4 imports **`P2S3` only** and reaches `P2S2` / `P2S1` / `P2S0` / `P1` transitively (the layered chain;
the gate enforces `^import (P2S3|P2S4)…`). Its working material, reached through the chain:

| Piece | Origin (transitive) |
|---|---|
| The attention carrier `attends : X → Finset X`, `outDest`, finite bound `ws1_bound_is_finite_attention` | `P2S0` |
| The collapse engine `ws1_atomless_bisim` (any two `SHNE` states are plain-bisimilar), `SHNE`, `IsBisim` | `P1.Core` |
| The labelled functor `LkObj`, `IsBisimL`, `plainOf`, `Recoverable`, `AttentionDistinguishes` | `P1.Core` / `P1.Reader` |
| The rank-labelled lift `rankLift dest rank` (each edge broadcasts the source's `rank`) | `P1.Reader` |
| The knowing-asymmetry (the metric is directed): `ws3_direction_not_recoverable` | `P2S0` |
| The lateral texture: same-rank peers `slf`/`p`/`q` at rank 0, incomparable reaches | `P2S2` |

**Series 2.4 adds exactly two things:** THE WORLD (WS1) and the two GRADINGS on it. It reuses `rankLift` as
the generic labelling device: the VERTICAL lift is `rankLift outDest rank`, the LATERAL lift is
`rankLift outDest lat` (the SAME machine with a lateral coordinate in place of rank). Nothing below `P2S3` is
imported directly.

## 2. The shared witness (the world `W` and the tower `T`)

Two carriers, both at `Cardinal.{0}` on `Fin`, monomorphic (as in S0/S2).

### 2.1 The world `W = Fin 4` — the lateral zone (DISTINCT)

A directed 3-ring of same-rank peers plus one reified peer.

| Node | Lean | `rank` | `lat` | `attendsW` | role |
|---|---|---|---|---|---|
| `w0` | `0` | 0 | 0 | `{w1}` | the self (the basepoint of the self-relative metric) |
| `w1` | `1` | 0 | 1 | `{w2}` | a peer, one lateral step from the self |
| `w2` | `2` | 0 | 2 | `{w0}` | a peer, two lateral steps from the self (real extent) |
| `r`  | `3` | 1 | 0 | `{w1}` | a REIFIED copy of the self's locus: same lateral coordinate, higher rank |

- **Directed ring** `w0 → w1 → w2 → w0`: local (`w0` attends only `w1`, NOT `w2`), so distance carries structure.
- **`rankW`**: `w0,w1,w2 ↦ 0`, `r ↦ 1`. The vertical grading.
- **`latW`**: `w0 ↦ 0`, `w1 ↦ 1`, `w2 ↦ 2`, `r ↦ 0`. The lateral coordinate (distance-from-the-self on the ring;
  `r` sits at the self's coordinate, no lateral displacement).
- **`rankLiftW := rankLift (outDest hinf attendsW) rankW`**, **`latLiftW := rankLift (outDest hinf attendsW) latW`**.
- Every node is `SHNE` (all out-sets nonempty), so `ws1_atomless_bisim` makes ANY two nodes plain-bisimilar:
  the plain relating is blind, and all content lives in the two labels.

**The cross-pattern of separations (the crux — axis-independence):**

| pair | `lat` separates? | `rank` separates? |
|---|---|---|
| `(w0, w2)` | **yes** (`lat 0 ≠ 2`) | no (`rank 0 = 0`) |
| `(r, w0)` | no (`lat 0 = 0`) | **yes** (`rank 1 ≠ 0`) |

`lat` and `rank` separate DIFFERENT pairs, so neither grading is a function of the other. This is the new
content on which the verdict rests — NOT the mere multiplicity of peers (audit c).

### 2.2 The tower `T = Fin 3` — the collapsed zone (REDUCED reachable)

A directed line where every attention step IS a reification step, so breadth is accumulated depth.

| Node | Lean | `rankT` | `latT` | `attendsT` |
|---|---|---|---|---|
| `tw0` | `0` | 0 | 0 | `{tw1}` |
| `tw1` | `1` | 1 | 1 | `{tw2}` |
| `tw2` | `2` | 2 | 2 | `{tw2}` (self-loop, keeps `SHNE`) |

Here **`latT = rankT` as functions** (`ws4`-witnessed): the lateral coordinate is the reification rank, the two
axes COINCIDE, the same pairs are separated by both. This is REDUCED realized as a genuine structure — space is
time seen sideways, extension is disguised succession — so the DISTINCT fork is NOT decided by fiat (it fails on
`T`). REDUCED is reachable by construction of a real witness, not by a flag flip alone.

## 3. The breadth metric, path-grounded (audit d)

Distance is the **directed attention-path length**, defined via a length-indexed reach relation built on
`attendsW` (NOT a count of import-labels):

```
def reachIn (att : W → Finset W) : ℕ → W → W → Prop
  | 0,     x, y => x = y
  | n + 1, x, y => ∃ z ∈ att x, reachIn att n z y
```

`reachIn att n x y` means "there is a directed attention-path of length `n` from `x` to `y`." It is decidable
on the finite carrier, so all metric facts reduce by `decide`. The metric grading is **self-relative**:
`latW` is proved to be the shortest attention-path length FROM the self `w0` (`ws3_metric_grounded`:
`reachIn attendsW (latW x) w0 x` and no shorter path, for each ring peer). There is NO global two-argument
absolute distance function; every distance claim is FROM the named self `w0` (audit a). Locality (`w2 ∉ attendsW
w0` yet `reachIn attendsW 2 w0 w2`) makes the graph non-complete, so distance is genuine geometry, not a
label-count.

## 4. The discipline (the honesty invariants, transcribed)

- **Fork genuine, no fiat.** DISTINCT holds on `W`, REDUCED on `T`; both are built structures. The distinctness
  does NOT hold by typing on every carrier (it fails on `T`, where `latT = rankT`). Audit b.
- **No absolute frame.** The metric is self-relative (`latW` = path length from `w0`); no theorem asserts a
  distance frame-independently. Audit a.
- **The knot on axis-independence, not multiplicity.** The verdict rests on the cross-pattern (`lat` and `rank`
  separate different pairs), not on "there are many" (which is the Series 07 import, the acknowledged ground).
  Audit c, the Phase-2 costume gate.
- **Distance not disguised counting.** The metric is path-based on a LOCAL (non-complete) graph, grounded in
  `reachIn`. Audit d.
- **Names-not-terms.** No proof term, definition, or discharged obligation is named "space," "distance," "world,"
  "here," "there," "self," "time," "God," "choice," or "subjectivity" as content. The carrier uses neutral names
  (`W`, `w0…`, `latW`, `rankW`, `reachIn`, `latLiftW`); the interpretive words live only in docstring prose.
  Audit e.

## 5. Cross-workstream triage

| WS | Payoff | Strips to |
|---|---|---|
| WS1 | a genuine lateral world: same-rank peers, real extent, non-recoverable, not a tower | a set of same-rank states, pairwise non-recoverable, with a non-complete reachability relation |
| WS2 | the axes come apart: `lat`-move-no-rank and `rank`-move-no-`lat` | the reachability-distance grading and the rank grading are not functions of each other |
| WS3 | the lateral separation is an import (Series 07); metric directed, granular, self-relative | a distance-greater-than-one pair is `¬ Recoverable`; the path metric is asymmetric with a least positive step |
| WS4 | the two-axes fork: independence witnessed, REDUCED reachable on `T`, no fiat, no costume | a discriminating function over axis-independence, reaching two values, both witnessed |
| WS5 | the verdict computed + audit a–e | an `Outcome`-valued function, `= distinct` by `rfl`, discriminating by `decide`, flags earned by the WS1–WS4 headlines |

## 6. Outcome classes (WS5)

`inductive Outcome | distinct | reduced | shapeDrawn | partial'` (neutral names; no forbidden content-name).
`distinct` is the computed verdict on `W`'s flags; `reduced` is reached when independence fails (the `T` zone);
`shapeDrawn` when the fork is drawn but neither zone forced; `partial'` when an obligation lands only degenerate.

## 7. Module layout (`P2S4` namespace, registered at Phase E)

`P2S4.lean` imports `P2S4.ws1`…`P2S4.ws5`; `P2S4/wsN.lean` one per workstream; `P2S4/AxiomCheck.lean` runs
`#print axioms`. `ws1` imports `P2S3` (the chain); `ws2`…`ws5` import their predecessor `ws` files. Namespace
`P2S4`, mirroring `program-1/series-13/formal/Series13/`.

---

*No em dashes in final academic copy. The world this batch designs is the ground the rest of Phase 2 inherits.
The verdict is computed, never hand-set; the fork is genuine, REDUCED realized on `T`; the knot rests on the
independence of the two axes, not on the import-powered existence of many.*
