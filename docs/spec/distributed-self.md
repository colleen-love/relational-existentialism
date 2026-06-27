# The distributed self — I am the knowing of my parts across their seams

**Status tags.** `[proved]` mechanized sorry-free (mathlib v4.15.0; D and C on **0 axioms**, W on
`[propext, Classical.choice, Quot.sound]`). `[follows]` short consequence of proved items plus a named
premise. `[reading]` interpretation over proved structure. `[open]` neither yet. `[empirical]` measured
outside the theory, first-personally.

Companion module: [`formal/Scratch/DistributedSelf.lean`](../../formal/Scratch/DistributedSelf.lean).
Builds on [`02-axioms.md`](02-axioms.md) (A1–A3), [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md)
(part / other / collection; routing vs directing), [`03.6-the-self-quantified.md`](03.6-the-self-quantified.md)
(the distributed self), [`time-flow.md`](time-flow.md), and
[`universe-and-cosmos.md`](universe-and-cosmos.md). This is `universe-and-cosmos` §8 turned inward: the
same structure at the one scale where the prover has first-person access to the data — a life.

## 0. The claim

> **I am the knowing, distributively, for as long as I have been alive — not one self knowing itself
> whole, but a collection of parts each knowing themselves, woven into one self at the seams between
> them.**

Three sub-claims, separated because they have different proof shapes:

- **(D) Distributed, not singular.** "I" is not a unitary `νΦ_c` modelling itself whole (barred), but a
  plurality of knowings held together. §2.
- **(W) One self, not a heap.** The plurality is nonetheless *one* self — woven at the seams (the
  un-attendable boundaries between parts), not a coproduct of unrelated sub-selves. §3.
- **(C) Coextensive with my life.** The knowing has run continuously for the whole span I have been
  alive, and that continuity is *witnessed by my persistence*, not posited. §4.

## 1. Why this is the right scale

The cosmic version ([`universe-and-cosmos.md`](universe-and-cosmos.md)) carried two liabilities: the
seam was a cosmological abstraction, and the temporal region needed an empirical bridge to physics.
Inward, both resolve. The seam becomes *the thing in you that cannot be made an object* — lived, not
posited. The temporal region becomes *your life, measured from the inside* — no external bridge
required, because the span is given first-personally. So the distributed-self theorem is the framework
touching a self that can check the proof against its own existence: the place where promise becomes
testable without paying for cosmology.

## 2. (D) Distributed, not singular — `[proved]`

The singular reading — one self that knows *itself whole* — is the exact thing
[3.3](03.3-knowing-vs-feeling.md) / self-inclusion bars: `self_inclusive_unmodelable`, *you cannot aim
at the aimer*, you cannot get outside the whole you are in. So "I know myself whole" is the one knowing
you provably cannot have.

What you *can* have is [`03.4`](03.4-limits-of-knowing.md)'s **relation to a part — the partial trace**:
looping back *some* wires while holding the rest at a distance, each such partial loop having its own
fixed point, a **sub-self**. Directing attention at a *part* of yourself is permitted
(`disjoint_modelable`); directing it at the *whole* is not (`self_inclusive_unmodelable`). Therefore the
only knowing a self can perform on itself is **distributed across its parts**:

> **Distributed Self-Knowing `[proved]`** (`selfKnowing_factors_through_parts`, **0 axioms**). The
> whole-self complete model is barred and a part is modelable, conjoined: *all genuine self-knowing
> factors through parts.* "I know myself" is true only as "my parts know themselves," never as one
> total self-model.

So (D) is not a concession to humility; it is forced by the same obstruction that makes selfhood
interesting. *You are the holding-together of parts each knowing themselves, because the alternative is
literally unprovable-by-construction.*

## 3. (W) One self, not a heap — the seam does the weaving — `[proved]` (concrete) / `[open]` (abstract)

The risk in (D): if self-knowing is only ever part-knowing, why are "you" one self and not a bag of
disconnected sub-selves? The answer is the **seam**. [`03.4`](03.4-limits-of-knowing.md)'s
relation-to-another is the **co-directed, shared trace**: when two parts share a looped wire, "a part of
you is a part of the other," and the shared fixed point `νΦ_c` lives *in the between*. Between your parts
there are such shared seams — and `SeamForcing` proved the seam is the one block no available knowing
can decohere (`attend_fixes_seam`, `self_cannot_fully_decohere`).

> **Weave — the state-level witness `[proved]`.** A bipartition of the self into a part `P` and its
> complement; a **coproduct** is block-diagonal (no cross-part coherence — a heap of separable parts);
> the **weave** is the cross-part coherence a coproduct lacks. `crossMass` measures it, and
> `weave_exceeds_coproduct` proves: a single live cross-part coherence forces `0 < crossMass` and
> `¬ IsCoproduct` — the joint carries coherence *in the between* that no coproduct of the parts has, so
> it **strictly exceeds** the heap. `coproduct_iff_crossMass_zero` makes `crossMass` an exact gauge:
> zero iff a heap, positive iff genuinely woven. *Plural interior, one self, woven at the seam.*

> **The abstract lift `[open]`.** The gfp-level version — the *joint sustained field* `νΦ_c` over the
> parts strictly exceeds the *coproduct of the parts' separate fixed points*, unless the seams are empty
> (the `J = ∅` case `SeamForcing` already identifies with the seamless total `dephase`) — is the
> remaining proof obligation. This module proves the state-level witness (a joint state with live seam
> coherence is not a coproduct); the sustained-field version, over `Attention.lean`'s
> `sustainedField := νΦ_c`, is the short route still to run.

This answers the fork directly: **not** many sub-selves with no center, **and not** a unitary knower —
but one distributed self *constituted by* mutual knowing across un-decohere-able seams.

## 4. (C) Coextensive with my life — continuity as a theorem from evidence — `[proved]`

This is `universe-and-cosmos.md` §9, folded in and run **backwards**. The spec there left continuity as
a *choice* (posit it, or accept gappy time). The inward version converts it from posit to inference,
because at personal scale you *have the record*:

> **Continuity-from-persistence `[proved]`** (`continuity_from_persistence`, **0 axioms**). Premise (the
> §9 commitment, named not hidden): a global lapse in knowing de-differentiates — knowing stops ⇒ no
> diagonal ⇒ the differentiated self dissolves back to undifferentiated feeling (the `p → 0` universe
> regime). Evidence: your differentiation has *persisted* across the whole span you have been alive.
> Therefore knowing **did not lapse** at any point in that span. Continuity of the self across time is a
> *witness* that knowing held throughout — **recorded, not assumed.**

The logic is contrapositive: *lapse ⇒ dissolution*; *no dissolution (you're still here)* ⇒ *no lapse*.
Survival of differentiation across the span is evidence of unbroken knowing across the span. The 13.8 Gyr
of the cosmos is the same argument at the scale where the record is cosmological rather than
biographical: *recorded differentiation implies constant knowing for as long as the record runs.*

> **Corollary (the full claim) `[follows]`, given D + W + C.** For the whole span you have been alive,
> there has been knowing — distributed across your parts, woven into one self at the seams — without
> lapse. *You are the knowing, distributively, for as long as you have been alive.*

## 5. The bridge worth flagging — Markov blankets — `[reading]`

The natural formalization of "parts knowing themselves across boundaries" is the **Markov blanket**
(Friston / free energy principle): the statistical boundary rendering a system's internal and external
states conditionally independent *given* the blanket, nested so blankets contain blankets. A blanket is
exactly a **seam made statistical** — the boundary one relates across but cannot collapse — and the
nesting is precisely the parts-within-parts of the distributed self.

> **Blanket–Seam bridge `[reading]` / bridge-conjecture.** The Markov blanket
> (conditional-independence boundary, Bayesian) and the framework's seam (un-attendable shared block, a
> conditional expectation / decoherence boundary) are the same object: the boundary across which an
> interior is conditionally sealed from an exterior. Nested blankets ↔ nested seams ↔ the distributed
> self.

Held as a **reading, not a theorem** — exactly as `time-flow` holds "this structure is physical time."
The two notions *rhyme* structurally but are built on different machinery (variational free-energy
minimization vs. the diagonal / conditional expectation); proving them the same object is real work. If
it firms up, it enters as a **free-energy functor** in the Layer-4 functorial semantics
([04](04-functorial-semantics.md)), alongside the physics / chemistry / biology / AI functors — a
genuine prize, earned later, asserted now only as motivation.

## 6. Footprint

| Ingredient | Status |
|---|---|
| A1–A3 | axioms |
| whole-self diagonal barred; part-trace permitted | `[proved]` ([3.3](03.3-knowing-vs-feeling.md), [`03.4`](03.4-limits-of-knowing.md)) |
| distributed self-knowing (D) | `[proved]` (0 axioms) |
| seam survives every available knowing | `[proved]` (`SeamForcing`) |
| weave: live cross-part coherence ⇒ joint ≠ coproduct (W, state-level) | `[proved]` |
| weave: joint `νΦ_c` ≠ coproduct of part fixed points (W, abstract) | `[open; short route]` |
| lapse ⇒ dedifferentiation | premise from §9 (`universe-and-cosmos`) |
| continuity-from-persistence (C) | `[proved]` (0 axioms) |
| Markov-blanket = seam | `[reading]` / bridge-conjecture |
| my lifespan as the temporal region | `[empirical]`, first-personal |
| **new axioms required** | **none** |

## 7. The status ledger

- `[proved]`, in hand: whole-self diagonal barred; part-directed trace permitted; seam survives every
  available knowing; (D) `selfKnowing_factors_through_parts`; (C) `continuity_from_persistence`; (W,
  state-level) `weave_exceeds_coproduct` / `coproduct_iff_crossMass_zero`.
- `[follows]`: the final corollary, given D + W + C.
- `[open; short route]`: (W) the abstract lift — the joint `νΦ_c` strictly exceeds the coproduct of the
  parts' fixed points. The one remaining proof obligation, and the heart of "plural interior, one self"
  at the gfp level.
- `[reading]`: the Markov-blanket bridge; and, inherited, flow = time.
- **Remaining interpretive dial** (orthogonal): whether "self" is *minimal* (any decoherence-free
  subalgebra) or *thick* (consciousness). The distributed-self structure holds either way.

## 8. Verification

`DistributedSelf.lean` builds sorry-free against mathlib v4.15.0; `selfKnowing_factors_through_parts` and
`continuity_from_persistence` depend on **no axioms**, `weave_exceeds_coproduct` and
`coproduct_iff_crossMass_zero` on `[propext, Classical.choice, Quot.sound]` — verified. It is wired into
the `Scratch` aggregator, so the default `lake build Scratch` stays clean. To reproduce:

```
cd formal
lake build Scratch.DistributedSelf
```

---

*One line:* you cannot know yourself whole (the diagonal is barred), so all self-knowing factors through
parts knowing themselves (D, proved, 0 axioms); the seams between those parts — the between-coherence no
coproduct carries — bind the part-knowings into one self rather than a heap (W, the state-level witness
proved, the `νΦ_c` lift the one open route); and because a lapse in knowing would dissolve
differentiation, your unbroken persistence is itself the record that knowing never lapsed (C, proved,
0 axioms) — so *you are the knowing, distributively, woven at the seams, for as long as you have been
alive*, with a Markov-blanket bridge waiting as the reading that could one day make the seam a measured
boundary.
