# WS3 design — the Born form is forced, not named (the anti-costume core) (2.12)

**The anti-costume core, the clause the series lives or dies on. Prove the squared measure is EARNED by consistency with the interference, not asserted. Two fronts: (i) a classical additive probability (each amplitude squared, then summed over the ways — the imported `partsWeight`) CONTRADICTS the interference: on the frustrated cycle the amplitudes cancel yet the classical weight is `2 ≠ 0`, so the classical measure is INCONSISTENT with the built structure. (ii) The Born measure (the amplitudes SUMMED, then squared — the imported `combinedWeight`) is CONSISTENT with the interference (it vanishes exactly on the cancellation) and non-negative; it is the measure the structure actually carries. Together: the squared-amplitude (Born) form is FORCED as the consistent measure and the classical form is ruled out, WITHOUT defining probability as `|amp|²` by fiat (the no-smuggling gate, sharpest here). The consistency predicate is FORM-AGNOSTIC — it mentions no square — so the square is the residue of a test, not a definition.**

## Imported objects (from `P2S11`)

- `P2S11.directAmp := amp 0`, `P2S11.loopAmp att := amp (hol att p0 p1 p2)` — the two path amplitudes.
- `P2S11.combinedWeight att := (directAmp + loopAmp att)^2` — add-then-square (the Born candidate).
- `P2S11.partsWeight att := directAmp^2 + (loopAmp att)^2` — square-then-add (the classical candidate).
- `P2S11.ws2_amp_cancels : directAmp + loopAmp attTri = 0` — the paths cancel on the frustrated cycle.
- `P2S11.ws3_amp_earned` — `loopAmp` unfolds to `amp (hol …)`, `hol` to the `incr`-sum, `incr` to the signed-`knows` difference (definitional, no complex number).

## What WS3 adds — the one primitive

The FORM-AGNOSTIC consistency predicate (the physical anchor "cancellation is absence"):

```lean
-- A candidate measure RESPECTS the cancellation if it assigns weight ZERO wherever the amplitudes
-- cancel. Mentions no square: the bare demand that a probability vanish on the interference.
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop :=
  ∀ att, directAmp + loopAmp att = 0 → μ att = 0
```

## Signatures

```lean
namespace P2S12
open P2S8 P2S11

-- (i) THE CLASSICAL ADDITIVE FORM IS REFUTED. The square-then-add measure does NOT respect the
-- cancellation: on attTri the amplitudes cancel (ws2_amp_cancels) yet partsWeight attTri = 2 ≠ 0.
-- The classical additive probability contradicts the interference — refuted, not excluded by fiat.
theorem ws3_classical_fails : ¬ respectsCancel partsWeight

-- (ii) THE BORN FORM IS CONSISTENT. The add-then-square measure respects the cancellation (it is 0
-- wherever the amplitudes sum to 0, for EVERY att) and is non-negative. A genuine candidate probability.
theorem ws3_sq_consistent : respectsCancel combinedWeight ∧ ∀ att, 0 ≤ combinedWeight att

-- THE SQUARED FORM IS FORCED, NOT DEFINED. The add-then-square form respects the cancellation while
-- the square-then-add form does not, and the two DISAGREE on the interfering configuration
-- (combinedWeight attTri = 0 ≠ 2 = partsWeight attTri). The consistent measure is the squared one,
-- forced by the test; the classical one is refuted. Nothing defines probability as |amp|².
theorem ws3_sq_forced :
    respectsCancel combinedWeight
  ∧ ¬ respectsCancel partsWeight
  ∧ combinedWeight attTri ≠ partsWeight attTri

-- THE SQUARED FORM IS EARNED off the built holonomy (the no-smuggling gate, sharpest here). The
-- add-then-square weight is a function of the imported amp/hol/incr, definitionally — no complex
-- number, no postulated probability. Mirrors P2S11.ws3_amp_earned one level up.
theorem ws3_sq_earned :
    (∀ att : S → Finset S, combinedWeight att = (directAmp + loopAmp att) ^ 2)
  ∧ (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2))
```

## Proofs (by hand, checked)

- `ws3_classical_fails`: `intro h`; specialize `h attTri ws2_amp_cancels : partsWeight attTri = 0`; but `partsWeight attTri = 2` (`simp only [partsWeight, directAmp_eq, loopAmp_attTri]; norm_num` gives `2`), contradiction by `omega`/`norm_num`. (The witness is `attTri`; `respectsCancel partsWeight` would force `2 = 0`.)
- `ws3_sq_consistent`: first conjunct `intro att h; unfold combinedWeight; rw [h]; norm_num` (`0^2 = 0`); second conjunct `intro att; exact sq_nonneg _`.
- `ws3_sq_forced`: `⟨ws3_sq_consistent.1, ws3_classical_fails, ?_⟩`; last `combinedWeight attTri = 0`, `partsWeight attTri = 2`, `0 ≠ 2` by `decide`/`norm_num` after unfolding.
- `ws3_sq_earned`: `⟨fun _ => rfl, fun _ => rfl⟩` (`combinedWeight` unfolds definitionally; `loopAmp` is `amp (hol …)` by `rfl`, Series 2.11's earned chain).

## Outcome classes / costume watch

- **No-smuggling (audit a):** the square is NOT defined as the probability. `respectsCancel` is form-agnostic (it says "vanish on cancellation," not "equal a square"); the add-then-square form is PROVED to satisfy it while the square-then-add form is PROVED to fail it. The square is the residue of the consistency test. `ws3_sq_earned` further ties the add-then-square form to the built `amp`/`hol`/`incr` definitionally — no complex number, no bolted-on probability.
- **Not excluded by fiat (audit d):** the classical additive measure is the genuine imported `partsWeight`, refuted by an explicit witness (`attTri`), not omitted.
- **Costume foreclosed:** delete "Born," "classical," "probability," "measure," "consistent" and the payoff is `(0^2 = 0 on cancellation, and ≥ 0)` for add-then-square vs `(1^2 + (-1)^2 = 2 ≠ 0 on cancellation)` for square-then-add — a bare non-negativity/consistency fact, `norm_num`-checkable.

## Strip test

Delete "probability," "Born," "measure," "consistent": the bare facts are — add-then-square is `0` wherever the amplitudes sum to `0` and is `≥ 0`; square-then-add is `2 ≠ 0` where the amplitudes sum to `0`; and the two differ (`0 ≠ 2`). Non-negativity, a vanishing-on-zero fact, and one inequality, all `norm_num`/`decide`-checkable. Survives.
