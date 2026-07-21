# Frustration de-risking — the good and the model-derived frustration, by hand (2.8)

**Phase B gate. This file is written and checked BEFORE any WS design and before any `formal/` file. It hunts, on paper, for (1) a non-trivial self-relative GOOD on a population of three or more, and (2) a concrete three-self population with MODEL-DERIVED directed reconciliations whose triangle holonomy is NON-TRIVIAL (frustration, no global section) ALONGSIDE one where it VANISHES (gluing, a global section). Only a candidate surviving BOTH earns the WS designs. If no non-trivial good survives, the series lands DISCONNECTED; if the obstruction degenerates to a single edge, PAIRWISE-ONLY. Rejected candidates are recorded. The Series 2.7 lesson (finding T1-S1) governs: the reconciliations must be read off the built directed attention, never bolted on beside it.**

The whole computation lives at `Cardinal.{0}` on finite carriers; every claim below is an integer arithmetic fact and is `decide`/`omega`-checkable, so the paper hunt and the build agree by construction.

---

## 0. The imported material this stands on

Reached transitively through `P2S7` (the series imports `P2S7` only):

- **The directed attention** `attends : X → Finset X`, `knows attends x y := y ∈ attends x`, the finite out-attention that is the sole ontological bound (`P2S0.knows`, `P2S0.attends`, `P2S0.outDest`). This is the model — the built directed carrier — from which every reconciliation below is read.
- **The world** — a lateral population of same-rank peers, the directed ring `w0 → w1 → w2 → w0` (`P2S4.attendsW`), the path metric `reachIn` (`P2S4`). The population of three or more selves is this lateral world, re-seated.
- **The single-edge coherence datum** `Converges₂`, `Valuation`, `Faithful₂` (`P2S3.ws1`). Used LOCALLY (per edge) and exceeded at the network: the network holonomy is what two-selves-`Converges₂` cannot see.
- **The knowing-asymmetry** (`P2S0`/`P2S2`): `x` may attend `y` without `y` attending `x`. This DIRECTEDNESS is the engine; a symmetric relating would carry no holonomy.

## 1. The one model quantity: the directed attention increment δ

Everything is derived from ONE function of the attention, read off the directed carrier and nothing else:

```
δ : (X → Finset X) → X → X → ℤ
δ att x y  :=  (if knows att x y then 1 else 0) - (if knows att y x then 1 else 0)
           =  ⟦y ∈ att x⟧ - ⟦x ∈ att y⟧
```

`δ att x y` is `+1` when `x` attends `y` but is not attended back (a one-way outward edge), `-1` when `y` attends `x` one-way (a one-way inward edge), and `0` when the edge is mutual or absent. It is the signed directed-attention flow across the pair `{x, y}`. (In the code it is named `incr`.)

**(D1) δ is antisymmetric, for EVERY attention, unconditionally.**
`δ att x y = ⟦y∈att x⟧ - ⟦x∈att y⟧` and `δ att y x = ⟦x∈att y⟧ - ⟦y∈att x⟧`, so `δ att x y + δ att y x = 0`. No hypothesis on `att` is needed; antisymmetry is definitional. (Checked: two `if`s, `omega`.)

This single fact is the spine. It gives pairwise coherence (§3), two-body triviality (§4), and it is manifestly a function of `att` alone — model-derived by construction, the T1-S1 trap foreclosed at the definition (there is no free ℤ parameter and no `Finset.card`/`insert` counter; the only input is `knows`).

## 2. The GOOD, and its non-triviality (WS1 de-risking)

The value space is `ℤ` (a torsor: values are compared by their differences, and the reconciliations act by translation — no canonical origin, i.e. no view from nowhere).

**The good of a self `x`** is its directed reading of the population: the function `y ↦ δ att x y`, what `x` values across each edge from its own attention. The good FOR the basepoint self `w0`/`p0` is the single valuation

```
valu : X → ℤ ,   valu y := δ att p0 y .
```

Take the world triangle `attTri` (the re-seated `attendsW`): `p0 → p1`, `p1 → p2`, `p2 → p0` (each self attends its lateral successor only). Then, reading δ off `attTri`:

| target `y` | `knows p0 y` | `knows y p0` | `valu y = δ p0 y` |
|---|---|---|---|
| `p0` | (self) 0 | 0 | `0` |
| `p1` | 1 (`p0→p1`) | 0 | `+1` |
| `p2` | 0 | 1 (`p2→p0`) | `-1` |

**(G1) The good is NON-TRIVIAL (not constant, not a view from nowhere).** `valu p1 = +1 ≠ -1 = valu p2`, so two relata are valued differently: the good is non-constant. (Checked: `decide`.)

**(G2) The good is GENUINELY SELF-RELATIVE (perspectival), not a metric.** Two DIFFERENT selves value a common target with OPPOSITE sign:
`δ att p0 p2 = -1` (from `p0`'s frame, `p2` reads `-1`) while `δ att p1 p2 = +1` (from `p1`'s frame, `p2` reads `+1`, since `p1 → p2`). So `δ p0 p2 ≠ δ p1 p2`: the same relatum `p2` is valued oppositely by two selves. No observer-independent valuation — in particular no symmetric metric `d(x,y) = d(y,x)` — can do this; δ is antisymmetric and observer-indexed, the signature of a genuinely self-relative good. (Checked: `decide`.)

**Not a relabelling (the WS1 costume watch).** 2.4's metric `reachIn`/`latW` is symmetric, unsigned, path-length (`latW p2 = 2`); `valu p2 = -1` is signed, antisymmetric, adjacency-based — a different object. 2.3's `Converges₂` is a `Prop` (an equation on a raising), not a ℤ-valued valuation. The good is neither relabelled.

**Survives.** A non-trivial, self-relative good exists on the ≥3 population. WS1 is not DISCONNECTED.

## 3. The RECONCILIATION and pairwise coherence (WS2 de-risking)

The reconciliation from `x` to `y` is the model-derived translation on the value torsor:

```
recon : (X → Finset X) → X → X → (ℤ → ℤ) ,   recon att x y  :=  fun v => v + δ att x y .
```

It is read off the directed attention (through δ), never chosen to frustrate. It aligns `x`'s frame with `y`'s by the directed increment across their edge.

**(R1) Every pair reconciles, and the reconciliation is a consistent isomorphism — pervasively, for EVERY attention.** For all `x, y`:
`recon att y x (recon att x y v) = (v + δ att x y) + δ att y x = v + (δ att x y + δ att y x) = v` by (D1). So `recon att y x ∘ recon att x y = id`: the edge reconciliation is invertible with inverse the reverse edge. This holds for ALL pairs and ALL attentions — local coherence is real and PERVASIVE (audit d), not a scarce accident. (Checked: `omega`.)

Note this is genuinely LOCAL and does NOT reference the good `valu` or force any global assignment: it says only that each edge carries a consistent transition. That is exactly Series 2.3's single-edge coherence, now pervasive across the network; the network question (is there a GLOBAL section?) is invisible to it.

**Bridge to 2.3 (built as `ws2_bridge_converges`).** With `Or := ℤ` and the raising `raise x y := recon att x y`, `Converges₂ ⟨valu att, raise⟩ x y` reads `valu att x + δ att x y = valu att y` — the local goods agree across the edge after transition, the 2.3 datum, per edge. The network holonomy exceeds it.

## 4. The HOLONOMY, and that it is genuinely many-body (WS3 de-risking)

The holonomy around an ordered cycle is the net translation of the composed reconciliation. Around the triangle `(x, y, z)`:

```
hol att x y z  :=  δ att x y + δ att y z + δ att z x    ( ∈ ℤ )
```

equivalently the amount by which `recon att z x ∘ recon att y z ∘ recon att x y` translates. A GLOBAL SECTION (a global good) is an assignment `s : X → ℤ` with `s y = recon att x y (s x) = s x + δ att x y` on every edge; summing around the cycle forces `hol = 0`, so:

> **a global section exists on the triangle ⟺ `hol att x y z = 0`.**

**(H1) The holonomy VANISHES for two selves — the phenomenon is invisible on a single edge.** For any `x, y`, the two-body "cycle" `x → y → x` has holonomy `δ att x y + δ att y x = 0` by (D1), for EVERY attention. There is no non-trivial two-body holonomy; the obstruction is not Series 2.3 replayed, and not a single edge. (Checked: `omega`.) This is `ws3_two_body_trivial`.

**(H2) The holonomy is MODEL-DERIVED — a cocycle over the built directed attention, not bolted on.** `hol att x y z` is a signed sum of `⟦·∈att·⟧` terms: it is a function of `att` alone, with no free parameter and no counter disconnected from the good (the good `valu` and the reconciliation `recon` are read off the SAME δ). Decisively, if the attention is made SYMMETRIC (`x∈att y ↔ y∈att x`, the direction-blind reduct), every δ is `0` and `hol` vanishes identically — the obstruction lives in the DIRECTEDNESS (the knowing-asymmetry), and a bolted-on gadget would be indifferent to it. The strip test (delete "good"/"common"/"value") leaves the bare cocycle fact: *the signed sum of the directed-attention increments around the 3-cycle is nonzero, so no `ℤ`-valued `s` satisfies `s y = s x + δ(x,y)` on all three edges.* That is a fact about `attTri`, not about a gadget beside it. This is `ws3_holonomy_model_derived`.

**Neither costume front.** Not a single edge (H1: two-body-trivial). Not import-ness: `hol` never mentions `Recoverable`/`¬Recoverable`; it is the directed-cycle sum, an axis/network engine. Both fronts of the doubled gate cleared.

## 5. The FORK: frustration AND gluing both reachable (WS4 de-risking)

Two concrete populations, both on the directed-attention model, exhibit the two sides.

### 5.a FRUSTRATED — the directed 3-ring `attTri` (`p0 → p1 → p2 → p0`)

Read δ off `attTri`:
- `δ p0 p1 = ⟦p1∈att p0⟧ - ⟦p0∈att p1⟧ = 1 - 0 = +1`
- `δ p1 p2 = ⟦p2∈att p1⟧ - ⟦p1∈att p2⟧ = 1 - 0 = +1`
- `δ p2 p0 = ⟦p0∈att p2⟧ - ⟦p2∈att p0⟧ = 1 - 0 = +1`

Holonomy `hol attTri p0 p1 p2 = 1 + 1 + 1 = 3 ≠ 0`. (Checked: `decide`.)

**No global section.** Suppose `s : X → ℤ` glued all three edges: `s p1 = s p0 + 1`, `s p2 = s p1 + 1`, `s p0 = s p2 + 1`. Substituting, `s p0 = s p0 + 3`, i.e. `0 = 3`, contradiction (`omega`). So there is NO global good, though (R1) every pair reconciles. **FRUSTRATED-REACHABLE.** This is `ws4_frustrated_reachable`.

The reading: the directed ring of attention — each self attending its lateral neighbor, the knowing-asymmetry going around — accumulates a net increment the way three voters cycle, a frustrated magnet finds no ground state, a curved world admits no flat chart. The frustration IS the directed attention's failure to close.

### 5.b GLUABLE — the directed star `attStar` (`p0 ↔ p1`, `p0 ↔ p2`)

Define a second population `attStar x := {p1, p2}` if `x = p0`, else `{p0}` (the self attends both peers; each peer attends the self — a directed star with mutual edges, no directed 3-cycle). Read δ:
- `δ p0 p1 = ⟦p1∈{p1,p2}⟧ - ⟦p0∈{p0}⟧ = 1 - 1 = 0` (mutual edge `p0 ↔ p1`)
- `δ p1 p2 = ⟦p2∈att p1⟧ - ⟦p1∈att p2⟧ = ⟦p2∈{p0}⟧ - ⟦p1∈{p0}⟧ = 0 - 0 = 0` (no edge)
- `δ p2 p0 = ⟦p0∈att p2⟧ - ⟦p2∈att p0⟧ = ⟦p0∈{p0}⟧ - ⟦p2∈{p1,p2}⟧ = 1 - 1 = 0` (mutual edge)

Holonomy `hol attStar p0 p1 p2 = 0 + 0 + 0 = 0`. (Checked: `decide`.)

**A global section exists.** `s := fun _ => 0` satisfies `s y = s x + δ attStar x y` on all edges (every δ is 0), and it restricts to the self's local good at the base (`s p0 = 0 = valu attStar p0`). **GLUABLE-REACHABLE.** This is `ws4_gluable_reachable`.

(Any δ-coboundary population glues; the mutual-edge star is the cleanest witness. A world whose directed attention closes into no net cycle admits a global good.)

**Both sides genuine, neither by fiat.** Frustration is not built into `hol` (the star gives `0`); gluing is not built in (the ring gives `3`). The verdict discriminates on the built attention: same δ, same recon, same hol — only the directed attention differs. The fork is a fact about which world you are in, not a construction choice.

## 6. Verdict of the de-risking

- A non-trivial, self-relative good survives (§2): **not DISCONNECTED.**
- The obstruction is genuinely many-body — vanishing for two selves (§4, H1) and alive for three (§5.a): **not PAIRWISE-ONLY.**
- The reconciliations are model-derived off the directed attention (§1, §3, §4, H2): **the T1-S1 trap foreclosed.**
- Both fork sides are reachable on genuine directed-attention carriers (§5): **the fork is not by fiat.**

**The good and the model-derived frustration both survive on paper. Phase B proceeds to the WS designs.** The expected computed verdict is **FRUSTRATED**: local pairwise coherence is pervasive (R1) yet does not glue into a global good (the directed ring holonomy is `3 ≠ 0`), the value analog of Series 2.7's global failure — no common good is written into this universe; it is made, edge by edge, and never owed.

### Rejected candidates (recorded)

- **The good as `latW` / `reachIn` (the path metric).** Rejected at WS1: symmetric and unsigned, it is a relabelling of 2.4's metric and cannot be perspectival (G2 fails — a symmetric metric values a target the same from every frame). Not a self-relative good.
- **The good as `Converges₂` (a Prop).** Rejected at WS1: a truth value on a raising, not a ℤ-valued valuation; strips to nothing non-trivial as "a function taking two distinct values."
- **Reconciliations as free permutations of a value set (an abstract cocycle chosen to frustrate).** Rejected at WS3 as the T1-S1 costume: a permutation cocycle not read off `att` decides the verdict on a gadget beside the world. δ is admitted BECAUSE it is a function of `att` alone.
- **The obstruction as `Finset.card`/`insert` bookkeeping (2.7's sunk counter).** Rejected: disconnected from the good and from the directed attention; carries no cycle-level content. Excluded by construction — `hol` is the δ-sum, nothing else.
- **A symmetric relating (`sym`) as the carrier.** Rejected at WS3: `sym` is direction-blind, so every δ would be `0` and the holonomy identically trivial — no frustration possible. The DIRECTEDNESS (the knowing-asymmetry) is load-bearing; the engine is the directed attention, not the symmetric reduct.
