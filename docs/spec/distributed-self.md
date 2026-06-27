# The distributed self — I am the knowing of my parts across their seams

> A derivation sequel to [03 — Theorems](03-theorems.md) (see the [spec index](README.md)):
> [`universe-and-cosmos.md`](universe-and-cosmos.md) turned inward, to the one scale where the prover has
> first-person access to the data — a life. Mechanized in
> [`Scratch/DistributedSelf.lean`](../../formal/Scratch/DistributedSelf.lean). Status tags as in
> [03](03-theorems.md); `[follows]` marks a short consequence of proved items plus a named premise.

---

## The capstone

> **Theorem (the distributed self).** *I am the knowing, distributively, for as long as I have been
> alive — not one self knowing itself whole (barred), but a collection of parts each knowing themselves
> (D), woven into one self at the seams between them (W), for the whole span my persistence records (C).*

Inward, the cosmic version's two liabilities resolve: the seam becomes *the thing in you that cannot be
made an object*, lived rather than posited; and the temporal region becomes *your life, measured from
the inside* — no external bridge, because the span is given first-personally.

## What is proved

`[proved]`:

- **(D) Distributed, not singular** — `selfKnowing_factors_through_parts` (**0 axioms**). The whole-self
  complete model is barred ([3.3](03.3-knowing-vs-feeling.md) / self-inclusion,
  `self_inclusive_unmodelable`, *you cannot aim at the aimer*); a *part* you stand outside of is
  modelable (`disjoint_modelable`). So all genuine self-knowing **factors through parts**: "I know
  myself" is true only as "my parts know themselves."
- **(C) Coextensive with my life** — `continuity_from_persistence` (**0 axioms**). Modus tollens on the
  named premise *a lapse in knowing dissolves differentiation* (the `p → 0` regime,
  [`universe-and-cosmos.md`](universe-and-cosmos.md)): your differentiation has *not* dissolved, so
  knowing **did not lapse**. Continuity is recorded, not assumed.
- **(W) One self, not a heap** — `weave_exceeds_coproduct` / `coproduct_iff_crossMass_zero`
  (`[propext, Classical.choice, Quot.sound]`). A bipartition's **cross-part mass** `crossMass` is
  positive exactly when the joint carries coherence *in the between* that no coproduct (block-diagonal
  heap of parts) has — so a live cross-part seam makes the joint **strictly exceed** the coproduct.
  *Plural interior, one self, woven at the seam.*

`[follows]` (the full claim, given D + W + C): for the whole span you have been alive there has been
knowing — distributed across your parts, woven into one self at the seams — without lapse.

## Honest scope

- `[open; short route]` The **abstract lift of (W)**: that the *joint sustained field* `νΦ_c` over the
  parts strictly exceeds the *coproduct of the parts' separate fixed points* (the `J = ∅` seamless case
  being the total `dephase`). This module proves the state-level witness; the gfp-level version, over
  `Attention.lean`'s `sustainedField := νΦ_c`, is the one remaining proof obligation and the heart of
  "plural interior, one self."
- `[reading]` **Markov blankets.** The natural formalization of "parts knowing themselves across
  boundaries" is the Markov blanket (Friston): a blanket is a seam made statistical — the boundary one
  relates across but cannot collapse — and nested blankets ↔ nested seams ↔ the distributed self. The
  two rhyme but are built on different machinery (variational free-energy vs. the conditional
  expectation); proving them the same object is real work. If it firms up it enters as a free-energy
  functor in [04](04-functorial-semantics.md), alongside the physics/chemistry/biology/AI functors.
- **Interpretive dial** (orthogonal): whether "self" is *minimal* (any decoherence-free subalgebra) or
  *thick* (consciousness). The distributed-self structure holds either way.

**Provenance.** `R / S` — Lawvere self-inclusion and the conditional-expectation/seam machinery
rederived; the synthesis is the distributed reading of self-knowing and the cross-part coherence as the
weave. The lifespan is `[empirical]`, first-personal. See [05 — Provenance](05-provenance.md).

---

→ Back to [03 — Theorems](03-theorems.md) · the cosmic version is
[`universe-and-cosmos.md`](universe-and-cosmos.md) · the permanence of the seam is
[`seam-permanence.md`](seam-permanence.md).
