# The generative engine (paper-four frontier)

> *Scratch / paper-four frontier — unnumbered until promotion.* Lean:
> [`../formal/GenerativeEngine.lean`](../formal/GenerativeEngine.lean) (not gated); imports the canonical
> process `Theory.MutualCoupling`. The node inventory is [`../../theory/spec/NODES.md`](../../theory/spec/NODES.md).

The canonical A3-process (`Theory.MutualCoupling`) is generative **by definition** — a self is a fixed point
of co-directed attention (`JointFixed`, with the capacity-limited raising `stepMu` baked in). This frontier
node is the **analysis** of that process's modulus dynamics: whether it *ignites or spends down*. It is
**unused by any shipped paper** (paper two's eigenform takes the self as a hypothesis; it never needs the
growth verdict), so it lives here, derived on the canonical process — not in the canonical layer. A3's text —
*"sustained generatively, not spent down; being attended-to raises the attention one can give"* — is a
**creation term**, which cannot live in a single channel with a *fixed* coupling, so the coupling is
**dynamical and mutual**. The one question that is not free: does creation balance dissipation at a *stable,
bounded, larger* self, or run away, or collapse?

## The law

The coupling on edge `(i,j)` is raised by the **mutual attention** across it, at each end's **own
capacity-limited rate**:

  `‖μ' i j‖ = raise ‖μ i j‖ ( α i · mutualAttn M i j )`,   `raise r a = (1 − a) r + a`,
  `mutualAttn M i j = ‖M i j‖ · ‖M j i‖`.

- **Co-directed, neither end freezable.** `mutualAttn` is built from both ends and vanishes if *either* is
  frozen (`mutualAttn_collapse_left`/`_right`).
- **Mutual but *not* symmetric.** The gain `α i` (node `i`'s **capacity** — its standing in all its other
  couplings, the constitutive finiteness) is `i`'s alone, so `μ_{ij} ≠ μ_{ji}` in general. Asymmetry is
  *produced* by the dynamics (`asymmetry_emerges`), not imposed; co-direction is tested by **non-freezability**
  (`frozen_no_growth`, either end) and **non-factoring** (`coupling_not_factor`), never by `μ_{ij} = μ_{ji}`.
- **Raising (monotone), per end.** `raise` is a convex pull of `‖μ‖` toward the band `1` (`le_raise`,
  `raise_le_one`): each end raises only toward the band, at a rate it can afford.

The phase rides free (`stepMu` preserves `μ/‖μ‖`), so the generative content is entirely in the modulus
(the phase-bearing reading is paper two's [`T2.15-phase-bearing.md`](../../paper-2/spec/T2.15-phase-bearing.md));
the dynamics is the real two-sided engine `Engine2 (α i) (α j)`, the genuine per-edge modulus law of the
`jointStep α` orbit (`orbit_engine2`).

## The verdict

The discriminating quantity is the **stability of the creation/dissipation balance**, not the bare occurrence
of growth. All `[proved]`:

| Outcome | Status | Where |
|---|---|---|
| **Divergent (blowup)** | **excluded structurally** — the per-end capacity `α ≤ 1` feeding the convex cap of `raise` keeps the orbit in `[0,1]⁴` forever. `α` *is* the brake. | `engine2_bounded`, `engine_bounded` |
| **Generative (grows)** | **`[earned]`, in the strong-attention basin** `1 − r₀ ≤ x₀²/8`: the coupling reaches the band (`r n → 1`) while the coherence is *not spent* (`x n ≥ x₀/2 > 0` ∀n) — the edge joins the conserved band carrying live coherence, `Peri` strictly grows to a *stable, bounded* self. | `engine_ignition` |
| **Conservative (no net growth)** | holds in the weak basin `r₀ + (4/3)x₀² ≤ 1/2`: coupling stays below the band, coherence spent to `0`. Co-direction real, but only redistributed. | `engine_spend_down` |
| **Asymmetric / leading-lagging** | the richer end (`α` larger) **leads** on both coupling and coherence at every step — a bond that grows *unequally*: two-sided, unequal, both growing. | `capacity_orders_couplings` |
| **Extractive (one grows at the other's expense)** | **absent under this law — and that is the finding.** Growth of either coupling *requires both* coherences live (`growth_requires_both`); the non-freezable multiplicative attention means a depleted end *stalls the whole loop* rather than feeding the other. Genuine extraction would need **dynamical** `α` (capacity falling under depletion) — an open frontier, not this constant-`α` law. | `no_growth_without_both`, `growth_requires_both` |

**Headline:** the self is **generative `[earned]`, conditionally and asymmetrically**. One law makes growth
*possible* (strong mutual attention ignites a self that grows to the band), *finite and bounded* (the capacity
`α ≤ 1` with the convex cap forbids blowup), *gracefully failing* (weak attention is merely spent), and
*asymmetric without extraction* (the richer end leads, neither is drained — shared non-freezable attention
couples their fates). The capacity bound `α` turns growth into a finite **achievement** of selfhood;
**dynamical `α`** is the open frontier for genuine depletion/extraction.

Canonical axioms: [`AXIOMS.md`](../../theory/spec/AXIOMS.md). The existence/stability of the fixed point is
`Theory.Axioms.self_exists` (existence) and `GenerativeEngine.self_exists_stable` (reached generatively).
