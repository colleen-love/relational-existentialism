# WS2, Subtractivity and the arrow (the reader knot, K1)

**Design doc. Series 2.1. Owns: the composite is genuinely NEW and the reading is LOAD-BEARING. Partial
attention is subtractive - the composite carries a residue non-recoverable from the plain relating
(`ws2_composite_residue`, the diagonal at the cycle level), the composite is real FOR a named finite attention
(`ws2_composite_real_for`, a genuine `RealFor` witness), and the tick does not invert (`ws2_tick_irreversible`,
a theorem over the relating). The central sin (charter §4.a, PR1-S2): the reader quantified out, the composite
a point-tag.**

*Imports `P2S0`; uses the diagonal residue (`residue`, `ResidueRecoverable`, `ws2_residue_free`), the collapse
engine (`ws1_atomless_bisim`), and the reader (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`,
`rankLift`), all reached transitively through S0 (README §1). Built on the WS1 witness `TCar` (README §3): the
composite is `kA`, the base relatum it is real against is `p0`.*

## The object at stake

The charter's WS2 (§2): the composite carries a residue not recoverable from the plain relating; it is real for
a bounded `attends`-reader and not a point-tag; and because the closure loses what the residue holds, the tick
does not invert. Three payoffs, the middle one guarded hardest (audit (c)): the reader must be named and
load-bearing, exactly the PR1-S2 fix `ws2_attention_makes_real` carries.

## Candidates

### C1, the residue is free at the cycle level (the subtractivity payoff)

The composite's self-inspection has a diagonal residue no hold realises - the transcribed diagonal
(`ws2_residue_free`) applied to the tick's relating, with the composite's holds inhabited so the residue is a
genuine content over `kA`.

```lean
theorem ws2_composite_residue {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ)
    (insp : Hold (outDest hinf attendsT) → HoldPred (outDest hinf attendsT)) :
    (¬ ResidueRecoverable insp)                          -- the residue is non-recoverable (subtractive)
  ∧ (∃ h : Hold (outDest hinf attendsT), h.1.1 = kA)     -- kA has a genuine hold: the residue is over the tick
```
The first conjunct is `ws2_residue_free (outDest hinf attendsT) insp` (S0's diagonal). The second exhibits a
hold based at `kA` (`kA` attends `p0`, so `⟨(kA, p0), _⟩ : Hold`), so the free residue is a content of the
composite's own inspection, not a vacuous global fact. The conjuncts interact: the residue is free FOR the
inspections of a relatum that genuinely has holds.

- **Ambient:** `ws2_residue_free`, `Hold`, `attendsT kA = {p0,p1}` (WS1).
- **Success condition:** `ws2_residue_free` discharges conjunct 1 for every `insp`; the hold witness by the
  membership `p0 ∈ attendsT kA` (`decide`).
- **Failure mode:** *the residue does not touch the composite* (a vacuous global diagonal). Foreclosed by the
  hold witness at `kA`. **Winner.**

### C2, the composite is REAL FOR a named finite attention (the reader payoff, audit (c))

Mirror `ws2_attention_makes_real`: a bounded reader (focus `p0`, reads `{p0}`, finite, grounded) for which the
composite `kA` is real - `kA` plain-bisimilar to the read relatum `p0` (collapse engine) yet label-separated
over the rank lift.

```lean
-- kA and the base relatum p0 are plain-bisimilar yet rank-separated (kA at rank 1, p0 at rank 0)
theorem ws2_composite_distinguishes {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kA p0

theorem ws2_composite_real_for {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsT) rankT),
      RealFor (rankLift (outDest hinf attendsT) rankT) att kA
```
`ws2_composite_distinguishes` is proved as `ws1_first_other`'s separation is: plain-bisim by
`ws1_atomless_bisim` on `plainOf (rankLift …) = outDest attendsT` (via `plainOf_rankLiftT`) with `SHNE` from
WS1; label-separation by the rank edge argument (`rankT kA = 1 ≠ 0 = rankT p0`), the `firstOther_label_sep`
pattern. `ws2_composite_real_for` packages it with the reader `⟨p0, {p0}, finite_singleton, grounded⟩`, the
`ws2_attention_makes_real` shape. **The reader is load-bearing: `att.reads` membership is used in `RealFor`.**

- **Ambient:** `ws1_atomless_bisim`, `AttentionDistinguishes`, `RealFor`, `FiniteAttention`, `rankLift`,
  `plainOf_rankLiftT`, `ws1_tcar_SHNE`.
- **Success condition:** both typecheck; the reader named, `kA` real for it.
- **Failure mode:** *the reader quantified out (PR1-S2, SERIOUS).* Foreclosed: `RealFor` binds `att` and uses
  `att.reads`; `Many` is not used. **Winner (audit (c)).**

### C3, the tick does not invert (the arrow, a theorem over the relating)

Because the closure raises the tower and the height is non-recoverable from the plain relating, no plain
bisimulation runs the closure backward: the rank label separating `kA` from its base is not recoverable.

```lean
theorem ws2_tick_irreversible {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsT) rankT)
```
Proved as `ws2_distinction_free`: from `ws2_composite_distinguishes` (a plain-bisimilar, label-separated pair),
recoverability would make the plain bisimulation a label bisimulation, contradicting the separation. The arrow
is a theorem, not a stipulation: the direction is the non-recoverability of the height the closure adds.

- **Ambient:** `Recoverable`, `ws4_recoverable_not_import`, `ws2_composite_distinguishes`.
- **Failure mode:** *irreversibility posited as a `Nat` order.* Foreclosed: the statement is `¬ Recoverable`, a
  bare recoverability fact; the strip test passes. **Winner.**

### C4, irreversibility as a step-counter monotonicity (the smuggled clock)

```lean
theorem ws2_tick_irreversible_bad : ∀ n, stepCounter (tickAt (n+1)) > stepCounter (tickAt n)
```
- **Failure mode:** *a `Nat` step counter doing the work of succession (charter §4.b, SERIOUS).* **Reject.**
  C3 states irreversibility as non-recoverability of the reification height, no counter.

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | residue free at `kA` | `ws2_residue_free`, hold at `kA` | yes | **win (subtractivity)** |
| C2 | `kA` real for a named reader | `ws1_atomless_bisim`, `RealFor`, `rankLift` | yes (S0 pattern) | **win (audit c)** |
| C3 | tick non-invertible = `¬ Recoverable` | `ws2_distinction_free` pattern | yes | **win (arrow)** |
| C4 | step-counter monotone | `Nat` counter | yes | **reject (smuggled clock)** |

## Winning candidates: C1 + C2 + C3

**Proof architecture.** `ws2_composite_distinguishes` is the shared engine (plain-bisim + rank-separation on
`kA`,`p0`), reused by `ws2_composite_real_for` (wraps it in a reader) and `ws2_tick_irreversible` (derives
non-recoverability). `ws2_composite_residue` applies the general diagonal to the tick's relating with a hold
witnessed at `kA`. All three land the `arrow = true` flag for WS5. **Dependencies:** WS1's witness and
`ws1_tcar_SHNE`, `plainOf_rankLiftT`, `rankLiftT_val`.

## Outcome classes (per charter §5)

- **Arrow proved (the WS2 payoff, feeds `arrow = true`):** residue free, composite real for a named reader,
  tick non-invertible.
- **Partial (pre-registered):** the residue is free but the reader goes inert (C2 collapses to `Many`), so the
  novelty is real but not reader-relative; reported Partial, `arrow` demoted.
- **Strip test.** `ws2_composite_residue` strips to *"the diagonal residue of an inspection of `outDest attendsT`
  is non-recoverable, and `kA` has a hold"* (by `ws2_residue_free`). `ws2_composite_real_for` strips to *"there
  is a finite attention for which `kA` is plain-bisimilar to `p0` yet label-separated"* (`RealFor`).
  `ws2_tick_irreversible` strips to *"the rank lift over `outDest attendsT` is not `Recoverable`"*. All three
  survive; no name is a term.

## Deliverable

`formal/P2S1/ws2.lean`: `ws2_composite_distinguishes`, `ws2_composite_residue`, `ws2_composite_real_for`,
`ws2_tick_irreversible`. Reader load-bearing (audit (c)); no `Many`; no counter. Axiom check reduces through
the collapse engine, `rankLift`, and `ws2_residue_free` to the standard three.
