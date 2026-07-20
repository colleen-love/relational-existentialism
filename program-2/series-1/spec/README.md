# Series 2.1, Design Index (`spec/README.md`)

**The shared carrier, the primitive decision, the discipline, the cross-workstream triage, the outcomes, and
the names-live-in-prose rule. Read once before the `wsNN-design.md` docs; they cite this file for every shared
object. This index and WS1-WS5 are committed as one batch before any `formal/` file exists (Phase B gate).**

*Series 2.1 stands on the Series 2.0 ground (`P2S0`), imported. Every carrier piece below is either S0's own
API or a P1 piece reached transitively through S0. Nothing new is added to the substance; the three additions
(§2) are constructions over the ground, not new atoms.*

---

## 1. What is transcribed, and from where

The build imports `P2S0` only (gate `^import (P2S0|P2S1)…`); the P1 prior art is reached transitively.

| Object | Origin (reached through S0) | Used by |
|---|---|---|
| `attends : X → Finset X`, `knows`, `sym`, `attendedBy` | `P2S0.ws1` | all |
| `outDest hinf attends : X → PkObj κ X` (finite out-attention coalgebra) | `P2S0.ws1` | WS1-WS4 |
| `finsetToPk`, `pkSingle`, `ws1_bound_is_finite_attention` | `P2S0.ws1` | WS1 |
| `FinReify`, `finReifyStep`, `finTowerN`, `ws1_finreify_injective` | `P2S0.ws1` | WS1 |
| `ws1_first_other`, the `Fin 3` unified witness `attendsU`/`rankU`/`reifyU`, `plainOf_rankLift`, `rankLiftU_val`, `SHNE_U` | `P2S0.ws1` | WS1 (base case) |
| `impLift`, `ws4_import_breaks_baseline`, `ws4_import_quantified` | `P2S0.ws4` | WS3 (the stream) |
| `PkObj`, `PkMap`, `LkObj`, `SReaches`, `SHNE`, `IsBisim`, `IsBisimL`, `plainOf`, `Recoverable` | `P1.Core` (via S0) | WS1-WS4 |
| `ws1_atomless_bisim` (the collapse engine) | `P1.Core` (via S0) | WS2, WS4 |
| `Hold`, `HoldPred`, `diag`, `residue`, `ResidueRecoverable`, `ws2_residue_free` | `P1.Core` (via S0) | WS2 |
| `rankLift`, `FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `ws2_many_general` | `P1.Reader` (via S0) | WS2, WS4 |

**Deliberately NOT used** (the foundation's two guardrails, `program-2/formal/P1.lean`): Series 12 WS3/WS4
compass/convergence machinery (PR1-S1, absent from the foundation); `Many` as a payoff template (PR1-S2 -
`RealFor` / `AttentionDistinguishes` carry every plurality/reality payoff, never `Many`).

## 2. The primitive: the three additions over the ground

Series 2.1 adds exactly three things over the S0 ground, none a new atom:

1. **Partial attention made load-bearing.** A relatum `attends` a proper finite part; the payoffs are read on
   the `attends`/`outDest` relating, never on a background index.
2. **The attention cycle and its composite (the TICK).** A finite pattern of relata each attending the next,
   closing on the first, reified by a pointwise section `reifyT` into a composite relatum whose `attends` is
   exactly the cycle pattern. This GENERALIZES `ws1_first_other` (the self-loop reified into the first other is
   the length-1 base case).
3. **The exogenous stream with the two orders on ticks.** The CAUSAL partial order (which tick consumes which
   tick's product) read off the relating, and the LINEARIZATION (which of two concurrent ticks came first)
   supplied by the stream. The stream generalizes S0's `impLift`.

## 3. The shared witness (`§WITNESS`, fixed here, built in WS1, used by WS2-WS4)

One monomorphic carrier at `Cardinal.{0}` carries every payoff, so WS4's two arms and the reader payoff are
exercised on the SAME structure (audit (d)). Carrier `TCar := Fin 7`.

| Node | def | role | `attendsT` | `rankT` |
|---|---|---|---|---|
| `p0` | `0` | base, cycle A | `{p1}` | 0 |
| `p1` | `1` | base, cycle A | `{p0}` | 0 |
| `q0` | `2` | base, cycle B | `{q1}` | 0 |
| `q1` | `3` | base, cycle B | `{q0}` | 0 |
| `kA` | `4` | composite of cycle A (a TICK) | `{p0, p1}` | 1 |
| `kB` | `5` | composite of cycle B (a TICK) | `{q0, q1}` | 1 |
| `kC` | `6` | higher closure consuming `kA`, `kB` | `{kA, kB}` | 2 |

- **Cycle A** is the genuine 2-cycle `p0 → p1 → p0` (`p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1`); cycle B likewise.
  A 2-cycle is the minimal genuine cycle above the self-loop base case (`ws1_first_other`, a 1-cycle).
- **The section.** `reifyT : Finset TCar → TCar` is defined pointwise: `{p0,p1} ↦ kA`, `{q0,q1} ↦ kB`,
  `{kA,kB} ↦ kC`, else `p0`. It sections `attendsT` at exactly these patterns: `attendsT (reifyT s) = s` for
  `s ∈ {cycleA, cycleB, {kA,kB}}` (the FinReify section, pointwise; total `FinReify` is unsatisfiable on the
  finite carrier, as in S0). All these hold by `decide`.
- **The causal edge.** `kA ∈ attendsT kC` and `kB ∈ attendsT kC`: `kC` consumes the products `kA`, `kB`. The
  causal order is `causal t u := isTick t ∧ isTick u ∧ t ∈ attendsT u` (`isTick x := x = kA ∨ x = kB ∨ x = kC`):
  `attends`-membership among the PRODUCED relata (ticks) only. It is acyclic (a DAG, not a cycle - the cycle is
  WITHIN each tick, the causal order is BETWEEN ticks) and rank-constrained (`causal t u → rankT t < rankT u`).
  The base 2-cycle edges (`p1 ∈ attendsT p0`, equal rank) are WITHIN-tick relating, correctly NOT causal edges
  (the C1-S1/S2 repair: an unrestricted `attends`-membership would wrongly make the base cycles violate the
  rank constraint).
- **The concurrent pair.** `kA ≠ kB`, `kA ∉ attendsT kB`, `kB ∉ attendsT kA`: neither consumes the other. They
  are the genuine concurrent (causally-independent) pair the linearization import needs (audit (d) non-vacuity).
- **SHNE.** Every node's `attendsT` is a nonempty singleton or doubleton, and every reachable node has nonempty
  `attends` (the cycles keep the base nodes live), so every node is `SHNE (outDest hinf attendsT)`. Proved
  `ws1_tcar_SHNE` by reduction to `attendsT_ne_empty` (decide).

All facts about the witness reduce by the kernel (`Fin 7` has computable `DecidableEq`), so `decide`/`rfl`
discharge the finite obligations, exactly as S0's `attendsU` witness does.

## 4. The discipline (the honesty invariants, applied)

- **No smuggled clock.** No `Nat` step counter, no background time index orders the ticks. The causal order is
  `attends`-membership among ticks (`causal`, `isTick`); the linearization is an exogenous label. `rankT` is the
  reification-tower height (a
  structural fact about who reifies whom), NOT a clock: it is used only to separate a composite from its base,
  never to order concurrent ticks (`rankT kA = rankT kB = 1`, so rank does NOT linearize the concurrent pair -
  that is the whole point).
- **The stream is exogenous.** WS3's choice is `¬ Recoverable`, a proof term (`impLift` reused), never assumed.
- **The reader is load-bearing.** WS2's `ws2_composite_real_for` names a genuine `FiniteAttention`; the
  composite is `RealFor` it, never a point-tag. `Many` is not used.
- **The fork is genuine.** WS4's concurrent pair (`kA`,`kB`) and causal pair (`kA ≺ kC`) are both witnessed on
  `TCar`, and the causal order carries the structural constraint `causal t u → rankT t < rankT u`.
- **Names are names.** No proof term, definition, or discharged obligation is named `time`, `now`, `clock`,
  `before`, `after`, `moment`, `self`, `other`, `chance`, `choice`, or `subjectivity` as content. The witness
  nodes are `p·`/`q·`/`k·`; the orders are `causal`/`linLift`; the tick is `kA`. Verified by the §6 grep.

## 5. The two watch-points (protocol §0.8)

- **WS1 - does the cycle genuinely reify?** `kA`'s well-formedness is discharged from the section
  `attendsT (reifyT cycleA) = cycleA` (a real pointwise `FinReify` fact, by `decide`), not posited by an opaque
  constructor. `kA` is a relatum of the SAME field `TCar`, and `attendsT kA` is a genuine finite `attends` set.
- **WS4 - is the concurrency order a genuine constraint?** `ws4_causal_order_endogenous` is exercised on the
  witnessed causal pair `kA ≺ kC`; `ws4_linearization_import` on the witnessed concurrent pair `kA`,`kB`; both
  on `TCar`; the causal order is rank-constrained (`decide`), the concurrency non-empty (`kA ≠ kB`, `decide`).

## 6. The mechanical checks (Phase E)

```
cd lake && lake build P2S1 P2S1.AxiomCheck
grep -rn "sorry" ../program-2/series-1/formal
lake build P2S1.AxiomCheck                       # standard three only
../scripts/gate.sh                               # P2S1 imports P2S0 + self + Mathlib only
grep -rniE "\b(time|now|clock|before|after|moment|self|other|chance|choice|subjectivity)\b" \
  ../program-2/series-1/formal                   # hits must be docstring prose only
```

## 7. The outcomes (WS5, per charter §5)

`Outcome := twoZone | endogenous | timeIsImport | partial' | disconnected`. The verdict is COMPUTED from the
WS1-WS4 flags by `verdict` (WS5), never hand-set:

- **twoZone** (expected): WS1 well-formed, WS2 arrow with the reader named, WS3 exogenous, WS4 causal order
  endogenous AND linearization import, both arms witnessed.
- **endogenous**: WS4's linearization proves forced too (`linImport = false`).
- **causalImport** (the charter's TIME-IS-IMPORT outcome, renamed so no identifier embeds a forbidden
  content-name): WS4's causal order proves non-recoverable (`causEndo = false`).
- **partial'**: an obligation lands only per-instance / degenerate.
- **disconnected**: WS1's construction imports structure beyond the stream (`wf = false`).

## 8. Names live in prose

Every headline mentions only the cycle, the composite `kA`, the attention, the residue, the stream (`impLift`),
the two orders, `Recoverable`, `rankLift`, the transcribed machinery, and standard Lean/Mathlib. The motivating
reading (the tick, the moment, the door) lives here and in `charter.md`, never in a proof term.
