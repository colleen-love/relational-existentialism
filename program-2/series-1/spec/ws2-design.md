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

### C1, the composite's partial attention DRIVES a genuine loss (subtractivity — LOAD-BEARING, Charter Extension 1 R3)

**Charter Extension 1 (EXT-F3, R3) raises the bar here.** The first build proved a bare conjunction of the
global diagonal `ws2_residue_free` (which never mentions `kA`) with a non-vacuity hold witness — the composite's
partial attention did no work. The rebuild makes the subtractivity LOAD-BEARING: the composite's FINITE
attention is a PROPER PART of its relating — `kA` is behaviorally related (the collapse engine) to a relatum it
does NOT attend, so the finite attention genuinely subtracts.

```lean
theorem ws2_composite_residue {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∃ y : TCar, (∃ R, IsBisim (outDest hinf attendsT) R ∧ R kA y) ∧ y ∉ attendsT kA
```
The composite `kA` relates behaviorally (plain-bisimilar, via `ws1_atomless_bisim`, both `SHNE`) to `kC`, yet
`kC ∉ attendsT kA = {p0,p1}`: `kA`'s attention is strictly less than what it relates to. The witness is `y = kC`
(`decide` for `kC ∉ attendsT kA`; the collapse engine for the bisimulation). The composite's partial attention
IS the loss — it subtracts everything beyond `{p0,p1}`, including relata it is behaviorally identified with. The
statement mentions `kA` essentially and the finite `attendsT kA` is what does the subtracting (audit: attention
⊊ relating).

- **Ambient:** `ws1_atomless_bisim`, `ws1_tcar_SHNE`, `IsBisim`, `attendsT kA` (WS1).
- **Success condition:** typechecks; `y = kC` witnesses attention ⊊ relating for `kA`.
- **Failure mode (foreclosed by R3):** *a bare conjunction where the composite does no work (EXT-F3).* The
  statement now ties the loss to `kA`'s finite attention essentially. **Pre-registered honest fallback:** if no
  genuine tie were achievable, Relabel explicitly (the transcribed global diagonal, subtractivity in prose,
  recorded (Relabel)) — but the tie IS achievable here (attention ⊊ relating), so it closes (Fixed). **Winner.**

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

### C3, the tick does not invert (the arrow — DIRECTIONAL, Charter Extension 1 R1)

**Charter Extension 1 (EXT-F2, R1) raises the bar here.** The first build proved `¬ Recoverable (rankLift …
rankT)` — non-recoverability (the `ws2_distinction_free` pattern), which is a genuine import fact but NOT
directional irreversibility. The rebuild makes the DIRECTIONAL content primary: reification strictly raises the
tower height from a tick's components to the composite, so the closure does not run backward (the composite is
not a predecessor of its own components; the tick relation is acyclic). The `¬ Recoverable` fact is retained as
the COMPANION import (Series 07: a genuine distinction is non-recoverable).

```lean
theorem ws2_tick_irreversible {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∀ x ∈ attendsT kA, rankT x < rankT kA)                     -- DIRECTIONAL: composite strictly outranks its components (acyclic)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsT) rankT)      -- COMPANION import: the arrow is non-recoverable
```
Conjunct 1 (the arrow proper) is `decide`: `attendsT kA = {p0,p1}`, `rankT p0 = rankT p1 = 0 < 1 = rankT kA`,
so every component ranks strictly below the composite — the closure raises the tower and cannot invert. The
general acyclicity of the between-tick order is WS4's `causal t u → rankT t < rankT u` (untouched). Conjunct 2
is the previous proof (`ws2_composite_distinguishes` + `ws4_recoverable_not_import`).

- **Ambient:** `attendsT kA`, `rankT` (WS1); `Recoverable`, `ws4_recoverable_not_import`,
  `ws2_composite_distinguishes`.
- **Success condition:** both conjuncts typecheck; WS5's arrow flag rests on conjunct 1 (the directional theorem),
  not the reader and not `¬ Recoverable`.
- **Failure mode (foreclosed by R1):** *the arrow carried by prose over a non-recoverability fact (EXT-F2).* The
  directional statement is now the theorem; the strip test reads it as "every member of the finite pattern
  `attendsT kA` has strictly smaller `rankT` than `reifyT` of it" — a bare rank-order fact. **Winner.**

### C4, irreversibility as a step-counter monotonicity (the smuggled clock)

```lean
theorem ws2_tick_irreversible_bad : ∀ n, stepCounter (tickAt (n+1)) > stepCounter (tickAt n)
```
- **Failure mode:** *a `Nat` step counter doing the work of succession (charter §4.b, SERIOUS).* **Reject.**
  C3 states irreversibility as non-recoverability of the reification height, no counter.

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | attention ⊊ relating: `kA` bisimilar to `kC ∉ attendsT kA` (LOAD-BEARING, Ext-1 R3) | `ws1_atomless_bisim`, `attendsT kA` | yes | **win (subtractivity)** |
| C2 | `kA` real for a named reader | `ws1_atomless_bisim`, `RealFor`, `rankLift` | yes (S0 pattern) | **win (audit c)** |
| C3 | tick DIRECTIONAL: `∀ x ∈ attendsT kA, rankT x < rankT kA` ∧ `¬ Recoverable` companion (Ext-1 R1) | `attendsT kA`, `rankT`, `ws2_composite_distinguishes` | yes | **win (arrow)** |
| C4 | step-counter monotone | `Nat` counter | yes | **reject (smuggled clock)** |

## Winning candidates: C1 + C2 + C3

**Proof architecture.** `ws2_composite_distinguishes` is the shared engine (plain-bisim + rank-separation on
`kA`,`p0`), reused by `ws2_composite_real_for` (wraps it in a reader) and by `ws2_tick_irreversible`'s companion
`¬ Recoverable` conjunct. `ws2_tick_irreversible`'s directional conjunct (`∀ x ∈ attendsT kA, rankT x < rankT
kA`) is `decide`. `ws2_composite_residue` (Ext-1 R3) witnesses attention ⊊ relating via the collapse engine
(`kA` bisimilar to `kC ∉ attendsT kA`). The DIRECTIONAL `ws2_tick_irreversible` feeds the WS5 `arrow` flag (Ext-1
R1); the reader (`ws2_composite_real_for`) feeds audit (c). **Dependencies:** WS1's witness and `ws1_tcar_SHNE`,
`plainOf_rankLiftT`, `rankLiftT_val`.

## Outcome classes (per charter §5)

- **Arrow proved (the WS2 payoff, feeds `arrow = true`):** the composite's attention subtracts (load-bearing
  residue), it is real for a named reader (audit (c)), and the tick is DIRECTIONAL (strictly outranks its
  components, acyclic).
- **Partial (pre-registered):** the reader goes inert (C2 collapses to `Many`) or the subtractivity fails to tie
  to `kA` (R3's Relabel fallback); reported Partial / Relabel, `arrow` demoted.
- **Strip test.** `ws2_composite_residue` strips to *"`kA` is plain-bisimilar to some `y ∉ attendsT kA`"* — a
  bare bisimulation/membership fact (attention ⊊ relating). `ws2_composite_real_for` strips to *"there is a
  finite attention for which `kA` is plain-bisimilar to `p0` yet label-separated"* (`RealFor`).
  `ws2_tick_irreversible` strips to *"every member of `attendsT kA` has strictly smaller `rankT` than `kA`, and
  the rank lift is not `Recoverable`"* — a bare rank-order + import fact. All three survive; no name is a term.

## Deliverable

`formal/P2S1/ws2.lean`: `ws2_composite_distinguishes`, `ws2_composite_residue`, `ws2_composite_real_for`,
`ws2_tick_irreversible`. Reader load-bearing (audit (c)); no `Many`; no counter. Axiom check reduces through
the collapse engine, `rankLift`, and `ws2_residue_free` to the standard three.
