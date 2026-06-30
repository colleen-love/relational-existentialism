# scratch — the living frontier (paper four workbench)

`scratch/` is the **pre-paper-four workbench**: the living frontier where the next paper's development
happens before it is frozen. Its Lean (under [`../formal/`](../formal)) is **not in the gated build** yet.

**Free workbench.** Unlike the papers, scratch **may import freely** from `paper-2/` and `paper-3/` (as well
as `theory/` and `foundation/`) — it is a workbench, not a sealed artifact, so the cite-don't-import /
hoist-to-`theory/` convention is **not** enforced here. `scripts/gate.sh` exempts scratch.

**The convention activates at promotion.** When a result is ready to become **paper four**, the promotion
event applies the discipline: cross-paper *results* it depends on become **prose citations** (or the needed
lemma is **hoisted to `theory/`** once a second paper imports it), and the per-node `T4.<nn>` numbering is
assigned then — not before. Until promotion, scratch stays **unnumbered**.

- **The conservation thread:** [`conservation-seed.md`](conservation-seed.md).
- **The generative engine** (ignition / spend-down analysis of the A3 process):
  [`generative-engine.md`](generative-engine.md) — Lean: [`../formal/GenerativeEngine.lean`](../formal/GenerativeEngine.lean).

**The turn that's currently hanging.** The conservation result first read as deflationary — the conserved quantity isn't a self; what is a self is precisely what is *not* conserved; the global ledger is the accounting of the self's dissolution into its correlations. But the better reading, which is what's now suspended and unresolved, is that the self is *carried*, not *kept*: a relation keeps constituting a self even after the other end is gone (a deceased relative carried forward; an AI instance whose output becomes the next input; conversations folded back into training). So presence may not be a state-functional conserved at an instant at all — it may be the invariant of a *persisting relation across the flow*, what survives the dissolution of every state that instantiated it. That reframes the open frontier (the "Noether coincidence"): the symmetry presence is the conserved charge *of* may not be time-translation of a state, but the invariance of a *relation* under the flow that sustains it — which is exactly what the modular flow is. This is the conceptual move that needs experts, distance, and a clear head before it's mechanized, not momentum.
