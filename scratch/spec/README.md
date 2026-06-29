# scratch — the living frontier (paper three workbench)

`scratch/` is the **pre-paper-three workbench**: the living frontier where the next paper's development
happens before it is frozen. Its Lean (under [`../formal/`](../formal)) is **not in the gated build** yet.

**Free workbench.** Unlike the papers, scratch **may import freely** from `paper-1/` and `paper-2/` (as well
as `theory/` and `foundation/`) — it is a workbench, not a sealed artifact, so the cite-don't-import /
hoist-to-`theory/` convention is **not** enforced here. `scripts/gate.sh` exempts scratch.

**The convention activates at promotion.** When a result is ready to become **paper three**, the promotion
event applies the discipline: cross-paper *results* it depends on become **prose citations** (or the needed
lemma is **hoisted to `theory/`** once a second paper imports it), and the per-node `P3.<nn>` numbering is
assigned then — not before. Until promotion, scratch stays **unnumbered**.

- **The conservation thread:** [`conservation-seed.md`](conservation-seed.md).
