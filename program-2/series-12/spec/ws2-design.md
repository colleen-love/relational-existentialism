# WS2 design — the weight is a non-negative, non-classical candidate measure (2.12)

**Prove the squared amplitude `|amp|²` (the imported `combinedWeight`) is a genuine NON-NEGATIVE weight, and NON-CLASSICAL: the destructive interference of Series 2.11 makes a combined outcome's weight fall STRICTLY BELOW the sum of the parts, which no classical additive probability can do. So the add-then-square form is a candidate probability that already departs from any classical measure — the quantum signature at the level of the weight.**

## Imported objects (from `P2S11`)

- `P2S11.combinedWeight att := (directAmp + loopAmp att)^2` — the add-then-square weight.
- `P2S11.partsWeight att := directAmp^2 + (loopAmp att)^2` — the square-then-add (classical additive) weight.
- `P2S11.ws3_destructive : combinedWeight attTri < partsWeight attTri` — the interference (combined strictly below parts).

## What WS2 adds

Two properties of the imported weight, read as measure-facts: non-negativity (it is a weight) and non-classicality (it undercuts the classical additive sum). No new arithmetic beyond `sq_nonneg` and the imported interference.

## Signatures

```lean
namespace P2S12
open P2S8 P2S11

-- The add-then-square weight is NON-NEGATIVE: (directAmp + loopAmp att)^2 ≥ 0 for every att.
-- A genuine weight (a candidate probability is at least a non-negative number).
theorem ws2_sq_nonneg (att : S → Finset S) : 0 ≤ combinedWeight att

-- NON-CLASSICAL: on the frustrated cycle the combined (add-then-square) weight falls STRICTLY BELOW
-- the sum of the parts (the square-then-add weight). No classical additive probability can undercut
-- its own parts (classically weights add: combined ≥ parts). Rests on P2S11.ws3_destructive.
theorem ws2_not_classical : combinedWeight attTri < partsWeight attTri
```

## Proofs (by hand, checked)

- `ws2_sq_nonneg`: `combinedWeight att = (directAmp + loopAmp att)^2`; `unfold combinedWeight; exact sq_nonneg _`.
- `ws2_not_classical`: exactly Series 2.11's interference, `exact P2S11.ws3_destructive` (`combinedWeight attTri = 0 < 2 = partsWeight attTri`).

## Outcome classes / costume watch

- The weight is a genuine NON-NEGATIVE candidate measure (WS2 nonneg) and it is NON-CLASSICAL (WS2 not_classical). A classical additive probability satisfies `combined = parts` (the weights of the ways add); a combined weight STRICTLY below the parts is impossible for any classical mixture. So `|amp|²` is not merely a weight — it is a weight that already cannot be a classical additive probability.
- **Costume foreclosed:** the non-classicality is a STRICT inequality (`0 < 2`) inherited from Series 2.11's `ws3_destructive`, not a relabelled sum; the whole content is the strict fall below the parts.

## Strip test

Delete "measure," "probability," "classical," "weight": the bare facts are `0 ≤ (directAmp + loopAmp att)^2` (a square is non-negative) and `combinedWeight attTri < partsWeight attTri` (`0 < 2`) — non-negativity of a square and one strict integer inequality, `sq_nonneg`/`norm_num`-checkable. Survives.
