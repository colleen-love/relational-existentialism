# WS3 design — The single line is the linearization import (1D lived time) (2.6)

**Prove that the single lived line is the self's LINEARIZATION of the partial causal order, and that this
linearization is an IMPORT: the partial causal order (the reification-dependency) is ENDOGENOUS, but a total
linear order of the moments is NON-RECOVERABLE (reading Series 2.1's `ws4_linearization_import` as the single
line). So the ONE-DIMENSIONALITY of lived time is not a fact about the world but the self's import over a
partially-ordered reality, and it is SELF-RELATIVE. The 1D content rests on the linearization being the import,
NOT on rank being an ℕ-valued scalar (charter §4.b, audit d): the tower rank cannot even linearize the concurrent
pair.**

## 1. Candidate constructions

1. **1D lived time = rank is an ℕ-valued scalar, so the moments are linearly ordered.** REJECTED: the costume of
   the order (charter §4.b). That makes 1D time a triviality of the grading. The tower rank does NOT linearize:
   `rankT kA = rankT kB = 1` on the concurrent pair. The line must rest on the linearization import.
2. **Read Series 2.1's `ws4_linearization_import` as the single line (CHOSEN).** The partial causal order `causal`
   is endogenous (witnessed `kA ≺ kC`, `kB ≺ kC`; rank-constrained; and genuinely partial — `kA`,`kB`
   incomparable). The single lived line is a TOTAL linearization of it. Series 2.1 proved every such
   linearization an import: for any order label `ord` distinguishing the incomparable pair, the ordered lift
   plain-identifies the pair (collapse) yet is label-separated, hence NOT `Recoverable`. That non-recoverable
   total order IS the self's single line: 1D lived time is the import.

## 2. Triage

- **Not the scalar costume (audit d).** `ws3_line_not_scalar` (`rankT kA = rankT kB`) shows the endogenous rank
  does NOT supply the line; `ws3_line_is_import` rests on `ws4_linearization_import` (the total order
  non-recoverable), quantified over ALL order labels distinguishing the pair. The single line is the import, not
  the scalar.
- **The partial order is endogenous (the contrast).** `ws3_partial_order_endogenous` (`= ws4_causal_order_endogenous`)
  exhibits the partial order as witnessed, rank-constrained, and genuinely partial. The partial order is
  recoverable; the TOTAL line over it is not. The wall between them is Series 07's import boundary.
- **Strip test.** `ws3_line_is_import` → "for any order label distinguishing an incomparable pair, the ordered
  lift is not `Recoverable`"; `ws3_partial_order_endogenous` → "a witnessed rank-constrained partial order with an
  incomparable pair"; `ws3_line_not_scalar` → "`rankT kA = rankT kB`." Bare `Recoverable` / order facts.
- **Names-not-terms (audit e).** `ws3_line_is_import`, `ws3_partial_order_endogenous`, `ws3_line_not_scalar` embed
  no forbidden content-word (note: "line," not "timeline").

## 3. Winning construction — typed signatures

```
-- THE SINGLE LINE IS THE LINEARIZATION IMPORT. For any order label distinguishing the concurrent pair, the
-- ordered lift is NOT Recoverable (the single line is the self's import). Rests on P2S1's ws4_linearization_import.
theorem ws3_line_is_import {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
      ¬ Recoverable (rankLift (outDest hinf attendsT) ord)

-- THE PARTIAL ORDER IS ENDOGENOUS (the contrast). Witnessed, rank-constrained, genuinely partial.
theorem ws3_partial_order_endogenous :
    (causal kA kC ∧ causal kB kC)
  ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA)

-- THE LINE IS NOT SCALAR RANK (audit d). The tower rank cannot linearize the concurrent pair.
theorem ws3_line_not_scalar : rankT kA = rankT kB
```

`ws3_line_is_import` is `fun ord h => (P2S1.ws4_linearization_import hinf ord h).2`;
`ws3_partial_order_endogenous` is `P2S1.ws4_causal_order_endogenous`; `ws3_line_not_scalar` is `rfl`/`decide`.
All three reached transitively through `P2S5` (no direct `import P2S1`).

## 4. Why the line is the import, not the scalar

The partial causal order is read off the relating (endogenous, recoverable), but it is genuinely PARTIAL: the
concurrent pair `kA`,`kB` has no causal order between them and equal rank. To live time as a SINGLE line, the
self must totalise that partial order — pick an order on the incomparable pair — and any such total order is
non-recoverable from the plain relating (`ws4_linearization_import`): an import. So the one-dimensionality of
lived time is the self's imposition on a partially-ordered reality, self-relative (a different self's line is a
different total order), and it does NOT come from rank being a scalar (rank does not even distinguish `kA`,`kB`).

## 5. Outcome classes

WS3 has no fork of its own; the linearization import is near-certain (Series 2.1's `ws4_linearization_import` is
forged). If, implausibly, the total order were recoverable, the line would be endogenous and 1D time a fact
about the world — reported in that direction. That does not obtain: the concurrent pair forces the import.

## 6. Strip annotation

- `ws3_line_is_import` → "for any order label distinguishing an incomparable pair, the ordered lift is not
  `Recoverable`."
- `ws3_partial_order_endogenous` → "a witnessed rank-constrained partial order with an incomparable pair."
- `ws3_line_not_scalar` → "`rankT kA = rankT kB`."
