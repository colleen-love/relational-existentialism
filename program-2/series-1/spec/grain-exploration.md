# Series 2.1, Grain — a pre-design exploration (NOT a contract)

**Status: EXPLORATION, ahead of Phase B. This is paper thinking about a candidate WS4 enrichment (or a later
series), recorded so it is not lost. It is not a design contract, states no committed signatures, and is NOT
part of any blind seed. Phase B decides whether any of it enters `ws4-design.md`.**

*Motivation (interpretive, gloss side): different entities have different smallest units. A cell ticks fast,
an organism slower, an ecosystem slower still. Without a metric this cannot mean "2.3× larger"; it must be a
refinement relation — one entity's tick subsumes several of another's. The claim to test is that this grain
order is endogenous where the tower can see it and an import where it cannot, the same two-zone shape as the
clock knot.*

---

## 1. The idea in one line

A relatum's **grain** is the resolution of its tick: how much finer structure one closure integrates.
"A is coarser than B" (`A ⪰ B`) should mean A's tick **subsumes** B's — B's closure sits below A's in the
reification tower — not that A's tick is longer in any metric. Grain is order-and-count, never duration.

## 2. Why the foundation already carries most of it

The transcribed carrier (`P1.Core`) hands us the pieces:

- **The tower order `prec`** (`P1.Core.prec`, `ws3_order_endogenous`): `reifyStep`-closure on patterns, the
  endogenous "reached by a reification sequence" relation. A composite sits above its constituents in `prec`.
- **Strict rank increase under reification** (`P1.Reader.ws2_many_general`'s hypothesis
  `hstep : ∀ w ∈ s.1, rank w < rank (reify s)`): a reified relatum ranks strictly above every constituent.
  This is already, almost verbatim, "reification strictly coarsens." Up the tower is coarser.
- **`¬ Recoverable`** (`P1.Core.Recoverable`, `plainOf`): the exact predicate for "not recoverable from the
  plain relating," the wall the clock knot and the import theorem both live on.

So a grain result would not need new structural machinery — it would be the tower order plus the rank-strictness
plus the recoverability test, the WS4 pattern pointed at resolution instead of temporal order.

## 3. Candidate definitions (unfrozen — Phase B may reject or reshape)

- **Sub-tick / subsumption.** For a composite tick born of cycle `s` (the reified pattern `reify s`), its
  sub-ticks are the closures among its constituents `w ∈ s.1`. Grain preorder candidate:
  `A ⪰ B := prec (over the shared field) B's-pattern A's-pattern` — A subsumes B when B's pattern is reachable
  below A's in the tower. Reflexive and transitive by `ReflTransGen`; non-trivial because `reifyStep` is a
  proper superset step where a genuine reification occurred.
- **Monotone-under-reification (the near-certain half).** `grain-mono`: if `w ∈ s.1` then `reify s ⪰ w`
  strictly — a composite is strictly coarser than each component. This is `ws2_many_general`'s `hstep` lifted
  to the grain order; expected to transcribe cheaply.
- **Grain measure (optional, ordinal only).** `grainOf x := rankW-style position in the tower`. A count, not a
  duration. Two entities with equal `grainOf` need not be comparable (rank is non-injective — see
  `ws_witness_rank_noninjective`), which is the point: equal count ≠ comparable grain.

## 4. The fork it should produce (the WS4 tie-in)

Conjecture, the two-zone shape:

- **In-sight (endogenous).** When A and B are `prec`-comparable (one's pattern reachable below the other's,
  a shared causal/tower path), their grains are ordered by the relating itself — `grain-in-sight-endogenous`,
  forced, recoverable.
- **Cross-independent (import).** When A and B are `prec`-incomparable (causally independent, no common
  refinement), no ordering of their grains is recoverable from the plain relating:
  `grain-cross-independent-import : ¬ Recoverable (of any labelled lift that orders them)`. Comparing them
  requires a third relatum whose attention reads both — an imported reference, a choice, exactly the
  linearization import of the clock knot at the level of resolution.

If both land, grain is the clock knot's twin: **self and other generically share no smallest unit, and
whether their times are commensurable is itself on the import boundary.** That sharpens 2.3's coherence
question — two perspectives may have no common clock to be coherent *in*.

## 5. Open questions for Phase B

1. Is grain best carried by `prec` (tower reachability) or by a dedicated subsumption relation on ticks? The
   tower is cheaper and already endogenous; a dedicated relation may be needed if a tick is not literally a
   tower node.
2. Does the cross-independent import need a *witnessed* incomparable pair (the PR1-S1 non-vacuity guard), the
   way the clock knot needs a witnessed concurrent pair? Almost certainly yes — the same audit clause (d).
3. Does grain belong inside 2.1's WS4 (as an enrichment of the ordering fork) or as its own later series
   (2.x, "commensurability")? Enrichment risks overloading WS4; a separate series keeps each knot clean.
4. Strip test: `grain-cross-independent-import` must survive deletion of "grain," "resolution," "size" and
   read as "a labelled lift ordering two `prec`-incomparable relata fails `Recoverable`." If it does not
   survive, the grain framing is doing proof work it should not.

## 6. Discipline note

Nothing here decides *which* grain a relatum has, or selects a comparison across independent entities — that
selection is the import, left to the stream, never named. Grain LOCATES the resolution boundary; it does not
fill it. Same shape as the clock knot, same permanent open.
