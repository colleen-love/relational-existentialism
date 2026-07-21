# WS1 design — the outcomes and the imports (the ground) (2.12)

**The ground. FORMALIZE the outcomes (the amplitude-carrying configurations of Series 2.11) and the IMPORTS as the free selection among them, and ask whether the imports carry a MEASURE — a weight over the possibilities. Prove the setup non-trivial: there are genuinely distinct outcomes with distinct amplitudes, so there is something to weigh. The risk (pre-registered) is that the imports are structureless — no non-trivial measure survives — a genuine obstruction toward DETERMINISTIC.**

## Imported objects (from `P2S11`, transitively `P2S8 / … / P1`)

- `P2S11.loopAmp att := amp (hol att p0 p1 p2)` — the loop-path sign (the amplitude of the around-the-ring path).
- `P2S11.directAmp := amp 0 = +1`, `P2S11.loopAmp attTri = -1`, `P2S11.loopAmp attStar = +1` (`ws1_amp_signed`).
- `P2S8.attTri`, `P2S8.attStar` — the two carriers (the two possibilities the differentiator selects between).
- `P2S11.combinedWeight att := (directAmp + loopAmp att)^2` — the add-then-square weight (the candidate measure, read at WS2/WS3).

## What WS1 adds

The reading of the two carriers as the OUTCOMES the imports select between, and the statement that the outcomes are genuinely distinct (distinct amplitudes) — so there is a non-trivial thing to weigh. No new arithmetic; a reading and a non-triviality theorem.

## Signatures

```lean
namespace P2S12
open P2S8 P2S11

-- The outcomes carry distinct amplitudes: the loop-path sign differs across the two carriers the
-- imports select between. There is a real distinction to weigh (else nothing to be a measure OF).
theorem ws1_outcomes_nontrivial :
    loopAmp attTri ≠ loopAmp attStar

-- The imports' candidate measure is non-trivial: the add-then-square weight takes DISTINCT values on
-- the two possibilities, so the freedom is genuinely weighted (the ground of genuine chance; its
-- failure would be the DETERMINISTIC obstruction — a constant/structureless weight).
theorem ws1_measure_nontrivial :
    combinedWeight attTri ≠ combinedWeight attStar
```

## Proofs (by hand, checked)

- `ws1_outcomes_nontrivial`: `loopAmp attTri = -1`, `loopAmp attStar = 1`, and `-1 ≠ 1` (`rw [loopAmp_attTri, loopAmp_attStar]; decide`). Directly Series 2.11's `ws1_amp_signed`.
- `ws1_measure_nontrivial`: `combinedWeight attTri = 0`, `combinedWeight attStar = 4`, and `0 ≠ 4` (`unfold`, `simp only [directAmp_eq, loopAmp_attTri, loopAmp_attStar]; decide`).

## Outcome classes / costume watch

- The setup is NON-TRIVIAL: distinct outcomes, distinct amplitudes, a non-constant weight — something to be a measure of. If the amplitudes were constant (no signed fork survived) or the weight constant, the honest obstruction is toward DETERMINISTIC (interference without chance). It does not obtain (the S2.8 frustrated/gluable fork gives distinct amplitudes and a non-trivial weight).
- **Costume foreclosed:** the imports' measure question is genuinely at issue — the non-triviality is a checked fact about the imported weight, not an assumed structure. The DETERMINISTIC obstruction is real and pre-registered (a constant weight is a trivial measure, WS4), not excluded by fiat.

## Strip test

Delete "outcome," "import," "measure": the bare facts are `loopAmp attTri ≠ loopAmp attStar` (`-1 ≠ 1`) and `combinedWeight attTri ≠ combinedWeight attStar` (`0 ≠ 4`) — two inequalities on the imported amplitude/weight, `decide`-checkable. Survives.
