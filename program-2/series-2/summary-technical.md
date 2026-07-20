# Series 2.2 — Technical summary

**Verdict: TWO-FACING, computed by `P2S2.verdict` from the WS1-WS4 flags (`ws5_verdict_eq : verdict true true
true true true = Outcome.twoFacing`, by `rfl`). Build: sorry-free, axiom-clean (standard three only;
`ws5_verdict_eq`, `ws5_verdict_discriminates`, and the two `True` audit clauses axiom-free), gate-green (`P2S2`
imports `P2S1` and its own roots plus Mathlib; `P2S0` and the `P1` foundation are reached transitively through
S1). Namespace `P2S2`, built on the `P2S1` ground.**

## The witness

One monomorphic carrier `RCar := Fin 5` at `Cardinal.{0}` carries every payoff (so WS4's arms and the reader
payoff are exercised on the same structure, audit (a), (d)):

| Node | role | `attendsR` | `rankR` |
|---|---|---|---|
| `slf` | the self | `{slf, oth, p}` | 0 |
| `oth` | the OTHER (reified self-relation upgraded to a locus reading back) | `{slf, oth, q}` | 1 |
| `p` | a relatum in the self's reach only | `{p}` | 0 |
| `q` | a relatum in the other's reach only | `{q}` | 0 |
| `bnd` | a higher closure the pair does not jointly attend (residue witness) | `{oth}` | 2 |

`reifyR` is the pointwise `FinReify` section (`{slf,oth,q} ↦ oth`, `{oth} ↦ bnd`, else `slf`). The two reaches
`{slf,oth,p}` and `{slf,oth,q}` are INCOMPARABLE (`p ∈ slf∖oth`, `q ∈ oth∖slf`). All finite obligations reduce
by the kernel (`decide`/`rfl`), as in the S0 `attendsU` and S1 `attendsT` witnesses.

## The theorems (all BUILT)

| WS | Theorem | Content | Strips to |
|----|---------|---------|-----------|
| WS1 | `ws1_other_is_locus` | `oth = reifyR {slf,oth,q}` (section `attendsR (reifyR {slf,oth,q}) = {slf,oth,q}`), `oth ≠ slf`, `(attendsR oth).Nonempty`, `rfield` contains both and their reaches, out-neighborhoods `< ℵ₀` (S0's bound) | a `FinReify`/membership/bound fact |
| WS2 | `ws2_other_distinguishes` | `AttentionDistinguishes (rankLift (outDest attendsR) rankR) oth slf` (plain-bisim via collapse engine + rank-1-vs-0 separation) | an `AttentionDistinguishes` fact |
| WS2 | `slfReader` / `ws2_other_reader_wise` | a NAMED `FiniteAttention` (focus `slf`, reads `{slf}`) for which `oth` is `RealFor` — reader load-bearing, not `∃ att`, not `Many` (audit (a)) | a `RealFor` fact |
| WS2 | `ws2_other_non_recoverable` | `¬ Recoverable (rankLift (outDest attendsR) rankR)` — the twoness an import (Series 07) | an import (`¬ Recoverable`) fact |
| WS3 | `faces` / `ws3_four_readings` | the four readings (self/self, self/other, other/self, other/other) typed and all witnessed, never evaluated | four `attends`-membership facts |
| WS3 | `faceLift` / `ws3_facing_asymmetric` | the reading-DIRECTION lift (tags each edge with `decide (rankR x < rankR z)`), `plainOf = outDest attendsR`; `slf` has an upward edge, `oth` none; `¬ Recoverable (faceLift)` | a rank-direction + import fact |
| WS3 | `ws3_facing_partial` | both self-readings witnessed, and no inspection is self-total (the imported diagonal `ws1_no_self_total_hold`, disclosed companion) | a self-loop + diagonal fact |
| WS4 | `ws4_mutual_residue` | all four readings; the joint residue (`bnd` bisimilar to `oth` yet `∉ attendsR slf` AND `∉ attendsR oth`, both conjuncts biting on the incomparable reaches); reading order rank-constrained; `¬ Recoverable` (not collapse); diagonal companion (not totalized) | a bisim/membership/rank/import/diagonal fact |
| WS5 | `ws5_verdict_eq` | `verdict true true true true true = twoFacing` (`rfl`, axiom-free) | the computed outcome |
| WS5 | `ws5_verdict_discriminates` | four discriminators (flip a flag → one / totalized / disconnected / partial') | falsifiability |
| WS5 | `ws5_flags_justified` | the five flags earned by the WS1-WS4 headlines (reader by the NAMED `slfReader`) | the workstream facts |
| WS5 | `ws5_audit_*` (a)-(e) | reader load-bearing; twoness import; facing asymmetric; residue genuine (mutuality tested); names / coherence-open (`True`, mechanical grep) | the audit propositions |

## The knot (WS4, the mutual residue)

The mutual reading is the JOINT attention of the two loci over the shared field, with all four readings
witnessed (`oth` reads `slf`, which reads `oth`, which reads `slf` — the recursion genuine). The residue is
carried by the `ws2_composite_residue` move (bisimilar yet unattended = the finite attention subtracts) lifted
from ONE reader to the PAIR: `bnd` is plain-bisimilar to `oth` (the collapse engine `ws1_atomless_bisim`
identifies all atomless relata, Series 07 — the honest import structure) yet in NEITHER reach. Because the
reaches are INCOMPARABLE, both non-membership conjuncts bite: dropping `bnd ∉ attendsR slf` admits `p` (in the
self's reach but not the other's), dropping `bnd ∉ attendsR oth` admits `q` — so the joint blind spot is
genuinely mutual, not one perspective's (verified in the blind code review, F4-S1). The reading order is
rank-constrained (`∀ z ∈ attendsR bnd, rankR z < rankR bnd`), so it is not free/total (PR1-S1 foreclosed). NOT
COLLAPSE is `ws2_other_non_recoverable`; NOT TOTALIZED is the diagonal `ws1_no_self_total_hold`, carried as a
DISCLOSED structure-independent companion, never the whole payoff. ONE and TOTALIZED are pre-registered outcomes
the same `verdict` computes for other structures.

## Discipline (audit)

- (a) The other is a READER, not a label: `ws2_other_reader_wise` proves `RealFor` for the FIXED named
  `slfReader` (its `reads` membership load-bearing), never `Many`, never `∃ att`. The other's attention is
  load-bearing across the bundle (WS3/WS4); it cannot be an inert tag.
- (b) The twoness is NON-RECOVERABLE: `ws2_other_non_recoverable` a `¬ Recoverable` proof term (the otherness an
  import, Series 07).
- (c) The facing is ASYMMETRIC: `ws3_facing_asymmetric`'s `¬ Recoverable (faceLift)` — the reading DIRECTION
  (source-vs-target rank), read by `IsBisimL`, genuinely distinct from WS2's source-rank separation; the S0
  `ws3_direction_not_recoverable` mechanism lifted to the two perspectives.
- (d) The residue is GENUINE, the MUTUALITY TESTED: the joint-unattended residue on the incomparable reaches
  (both conjuncts load-bearing), the reading order rank-constrained, both collapse and totalize arms reachable
  (`ws5_verdict_discriminates`). No PR1-S1 tautology. The COHERENCE (`Converges₂`, Series 2.3's) is NEVER
  decided — no signature or identifier touches it.
- (e) Names-not-terms: no identifier embeds a forbidden content-name (`slf`/`oth`/`p`/`q`/`bnd` are neutral
  positions; the reader is `slfReader`, the direction lift `faceLift`, the outcome `twoFacing`; the
  coherence-open clause is `ws5_audit_downstream_open`). The §6 grep hits are docstring prose only.

## Provenance and deviations

- Layered import chain `P1 → S0 → S1 → S2` (program charter §2): `P2S2` imports `P2S1` only; the S0 and P1
  machinery (`attends`/`outDest`, `ws1_atomless_bisim`, `rankLift`, `AttentionDistinguishes`, `RealFor`,
  `ws1_no_self_total_hold`, `Recoverable`, `ws4_recoverable_not_import`, `ws1_bound_is_finite_attention`) is
  transitive through S1. Disclosed in `charter-status.md` §5.
- No new atom, no cardinal ceiling, no evaluation of a reading; the only addition is the other as a second
  attending locus. The section is pointwise (total `FinReify` unsatisfiable on the finite carrier, as in S0/S1);
  disclosed.

## Review history

- Phase C (design), pass 1: one SERIOUS (C1-S1, the reader existentially quantified out — a `Many`-style claim),
  two REAL (C3-S1 the residue mutuality decorative, C2-S1 the hand-set flags), several COSMETIC. Repaired in
  Phase D: C1-S1 **(Fixed)** by the NAMED `slfReader`; the carrier moved to `Fin 5` with distinct reaches. Pass 2
  returned ZERO SERIOUS with one REAL (C2p2-R1, the distinct reaches were NESTED so one conjunct was redundant),
  **(Fixed)** by making the reaches INCOMPARABLE.
- Phase F (code), blind review of the built sources: ZERO SERIOUS, ZERO REAL (three COSMETIC prose/disclosure
  notes; one WS2 docstring softened). The reviewer independently confirmed no `sorry`/`admit`/`axiom`/
  `native_decide`, the clean names/coherence greps, the projection indices, and that every headline proves its
  stated proposition; audit (d) F4-S1 confirmed the joint residue load-bearing (each incomparable-reach conjunct
  necessary). The F/G loop closed with only a docstring change.

Every SERIOUS finding in the run (C1-S1) closed **Fixed** (the named-reader target was built), never Relabeled.
The verdict is the residue of the process, computed honestly with the collapse and totalize arms left reachable:
**TWO-FACING**. The two faces are built; the coherence across them is the next door (Series 2.3).
