# Series 2.10 de-risking (`spec/reversal-derisking.md`) — the paper hunt, before any WS design

**The paper gate. Before a single signature is fixed, this file settles on paper the two questions the whole series turns on: (1) the reification SECTION is a right-inverse that DECODES the reified pattern but does NOT preserve the built measure — decodability is strictly weaker than a dynamical reversal; and (2) an honest search for a genuine measure-preserving bijective sub-dynamics inside the built tick — a "core" one could run backward. If a genuine core is found, it earns the WS designs toward the recovered outcome; if the honest search finds none (the expected case, read off Series 2.7's rising rank), the obstruction is recorded and the series is aimed at the pre-registered NOT-RECOVERED. No inverse is added that the built tick does not have; the decodable section is never passed off as a reversal.**

The whole hunt is arithmetic on a four-element carrier, `decide`/`rfl`-checkable, so nothing here is hand-waved.

---

## 0. The imported material the hunt uses (quantified, never named as content)

Series 2.10 imports `P2S8` only; `P2S7 / … / P2S0 / P1` are reached transitively. The working objects, all built already and reused verbatim:

- **The reification section** — `P2S1.attendsT`/`P2S1.reifyT` (and the same shape at `P2S7`): `attends (reify s) = s` on the used patterns (a right-inverse: `reify` builds the product, `attends` reads its pattern back). The DECODER.
- **The built measure (the rank)** — `P2S7.rankM : MCar → ℕ`, the reification-tower height. The measure that a genuine reversal must PRESERVE. This is the higher bar; nothing here rigs it.
- **The tick** — the reification map `reify {·}` that carries a base relatum to its reified product. `P2S7.ws2_tick_raises` records that it STRICTLY raises the rank: `rankM (reifyM {e0}) = rankM e0 + 1`.
- **The collapse engine** — `AttentionDistinguishes` (the in-sight identification that makes the tick non-injective as a state map).

The measure the hunt preserves-or-not is `rankM`, the built rank, not a fresh gadget (audit d).

## 1. The carrier for the hunt (the built tick as a map on configurations)

We reuse Series 2.7's four-element carrier `MCar = Fin 4` and its built objects:

```
e0  = 0   -- a base relatum,           rankM e0  = 0
e0' = 1   -- a SECOND base relatum,    rankM e0' = 0   (gives the tick a second rank-0 state)
e1  = 2   -- a reified relatum,        rankM e1  = 1   ( = reifyM {e0}, an actualized tick-product)
e2  = 3   -- a higher reified relatum, rankM e2  = 2   ( = reifyM {e1} )
```

**The tick as a total map on configurations** is the reification map applied to the singleton pattern:

```
tick : Cfg → Cfg := fun x => reifyM {x}          -- Cfg := MCar, the built reification map
```

Unfolding `reifyM s = if s = {e0} then e1 else if s = {e1} then e2 else e0` on singletons:

| x   | {x}   | tick x = reifyM {x} | rankM x → rankM (tick x) |
|-----|-------|---------------------|--------------------------|
| e0  | {e0}  | e1                  | 0 → 1  (raises)          |
| e1  | {e1}  | e2                  | 1 → 2  (raises)          |
| e0' | {e0'} | e0  (default)       | 0 → 0  (holds)           |
| e2  | {e2}  | e0  (default)       | 2 → 0  (drops)           |

So as a functional graph the tick is `e0' → e0 → e1 → e2 → e0`: a tail `e0'` feeding a 3-cycle `e0 → e1 → e2 → e0`. This is the built tick; every entry above is `decide`-checkable, none is posited.

## 2. Question (1) — the section decodes but does NOT preserve the measure

The section `attends` is a right-inverse to `reify` on the used patterns (`P2S7.sectionM_e0`): `attendsM (reifyM {e0}) = {e0}`. It DECODES — given the reified product `reifyM {e0} = e1`, it reads the constituent pattern `{e0}` back. That is genuine and useful. It is NOT a dynamical reversal, for two independent reasons, both settled here on paper:

1. **Type.** The section maps a STATE to a PATTERN (`MCar → Finset MCar`), not a state to a state. It is not even of the type of a sub-dynamics one could iterate backward; it is a decoder.
2. **Measure.** The tick that produced the reified state RAISED the rank: `rankM (reifyM {e0}) = rankM e0 + 1 = 1 ≠ 0` (`ws2_tick_raises`). Recovering the pattern does not undo that rise; the measure the world carries is strictly higher after the tick, and the section does not lower it. A measure-preserving reversal would leave `rankM` fixed; the section leaves the rank raised and only reads the pattern.

**By-hand conclusion.** Decodability ⊊ reversibility. Passing the section off as a reversal is the costume (the exact Series 2.7 T1-S1 look-alike). WS3 states this as `attendsM (reifyM {e0}) = {e0}` (decodes) `∧ rankM (reifyM {e0}) ≠ rankM e0` (does not preserve the measure).

## 3. The core criterion (what a genuine reversal must clear — the higher bar)

A genuine reversible core is a sub-domain `D` on which the tick is a MEASURE-PRESERVING BIJECTION — a permutation of `D` that leaves the rank fixed, one you could run in reverse. On a finite carrier this is exactly:

```
IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D)                          -- closed
  ∧ (D.image t = D)                             -- surjective onto D
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y)       -- injective on D  (closed + surjective + injective on a Finset ⇒ a bijection D → D)
  ∧ (∀ x ∈ D, m (t x) = m x)                    -- rank-preserving  (the higher bar; NOT decodability)
```

Both clauses are required. Bijectivity alone is the wrong bar; a bijective sub-dynamics that raises the rank is not a reversal (see §4). Decodability (a right-inverse) is a still weaker and different thing (§2). The measure `m` is instantiated at the BUILT rank `rankM`, never a rigged measure.

## 4. Question (2) — the honest search for a core inside the built tick

A finite map is a bijection on `D` only if `D` is a union of its cycles (periodic points). The built tick's periodic set:

- `e0 → e1 → e2 → e0`: a **3-cycle**. These three are periodic.
- `e0'`: pre-periodic (feeds `e0`, never returns; nothing maps to `e0'`, since `reifyM` never outputs `e0'`). Not periodic.

So the only nonempty candidate for a bijective sub-dynamics is `D = {e0, e1, e2}` (or `∅`, which is vacuous and excluded by nonemptiness). Test the rank-preservation clause on it:

```
tick e0 = e1 :  rankM e0 = 0,  rankM e1 = 1     ⇒  0 ≠ 1   -- rank NOT preserved on this edge
```

The 3-cycle is a genuine bijective sub-dynamics but it does NOT preserve the rank: going round the cycle the rank reads `0, 1, 2, 0`, which is not constant, so it cannot be held fixed on every edge. **No nonempty measure-preserving bijective sub-dynamics exists inside the built tick.** This is the expected obstruction (read off Series 2.7: the rank rises on every reification edge), and it aims the series at the pre-registered NOT-RECOVERED outcome. The whole claim is one `decide` over the sixteen subsets of `Fin 4`:

```
ws4_no_core_built : ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick rankM D
```

## 5. The fork is not vacuous — the criterion IS satisfiable (audit b)

For the NOT-RECOVERED finding to be discriminating rather than a definitional impossibility, the criterion must be SATISFIABLE by some genuine dynamics on the built rank. It is. Take, on the SAME carrier and the SAME built rank, the relabelling permutation that swaps the two rank-0 states and fixes the rest:

```
tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x
```

Then `D = {e0, e0'}` is closed, the swap is a bijection of `D`, and it preserves the rank (`rankM e0 = rankM e0' = 0`): `IsCore tickR rankM {e0, e0'}` holds. So a measure-preserving bijective sub-dynamics is possible in principle — the criterion is real, not empty. The built REIFICATION tick simply is not one of them. This is the genuine fork:

```
ws4_core_reachable : ∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR rankM D      -- the criterion is satisfiable
ws4_no_core_built  : ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick  rankM D      -- the BUILT tick has no such core
```

`tickR` is NOT the built tick and is NOT called a reversal of the model; it is the control that shows the test is not rigged to always fail. The verdict is computed from the BUILT tick (`tick`, which has no core), and lands NOT-RECOVERED.

## 6. What the hunt settled (the outcome it earns)

- The section decodes but does not preserve the built rank — decodability ⊊ reversibility (WS3, §2). **Settled: yes.**
- A genuine measure-preserving bijective sub-dynamics inside the BUILT tick — **Settled: none exists** (§4). The rank rises on every reification edge; the one bijective sub-dynamics (the 3-cycle) fails rank-preservation.
- The criterion is nonetheless satisfiable on the built rank (§5), so the finding is discriminating, not a fiat.

The paper hunt therefore aims Series 2.10 at the pre-registered **NOT-RECOVERED** close (the arrow is fundamental): the built tick raises the measure at every scale, the section only decodes, and no sub-dynamics can be run backward measure-preservingly. This is the expected and most consequential report; the WS designs formalize exactly these facts, and the verdict computes it — never relabels a shortfall into a recovered core built on the section. Had §4 found a genuine core, the same signatures would have carried the recovered outcome; the honesty is that the verdict is the residue of the built theorems, not a premise.

---

*No inverse is added that the built tick lacks (the no-smuggling gate). The decodable section is held strictly apart from a dynamical reversal (the costume gate). The measure is the built rank `rankM`, not a rigged one (audit d). No proof term is named for the interpretive content (audit e). The four-element carrier makes every claim `decide`/`rfl`-checkable. This de-risking is committed as part of the Phase B batch, before any `formal/` file exists.*
