# WS2, Genuinely two reader-wise (the reader knot, the central sin, K1)

**Design doc. Series 2.2, the discipline gate. Owns: the proof that self and other are genuinely two
READER-WISE (a bounded reading load-bearing in the distinction) and that the separation is NON-RECOVERABLE (an
import, Series 07). The central sin (charter §4.a, K1, SERIOUS): the other a bare label, or the reader
quantified out — the Series 11 Bookkeeping / PR1-S2 failure, sharpest here because the OTHER is the reader.**

*Imports `P2S1`; reuses S1's `ws2_composite_real_for` / `ws2_tick_irreversible` architecture (a NAMED
`FiniteAttention` for which the reified relatum is `RealFor`, plus `¬ Recoverable`), the `ws1_first_other` /
`firstOther_label_sep` separation engine, and `ws4_recoverable_not_import`. The reader is the whole burden.*

## The object at stake

The charter's WS2 (§2): prove self and other genuinely two READER-WISE, not label-wise only — a bounded reading
(finite attention) load-bearing in the distinction, the separation `¬ Recoverable` from the plain relating
(which by Series 07 is exactly what a genuine distinction must be). The other must be an attending locus whose
READING does the distinguishing, never a point-tag, never the self relabeled, never the reader quantified out
(K1). Lift S0's `ws1_first_other` / `AttentionDistinguishes` machinery from one relatum to two full perspectives.

## Candidates

### C0, the shared separation engine (`ws2_other_distinguishes`)

`oth` and `slf` are plain-bisimilar over the bare out-attention relating (`ws1_atomless_bisim`, both `SHNE`) yet
NOT label-bisimilar over the rank lift (`oth`'s edge carries `rankR oth = 1`, `slf`'s carries `rankR slf = 0`):
exactly `AttentionDistinguishes`. The S0 `firstOther_label_sep` / S1 `ws2_composite_distinguishes` pattern, on
the two loci.

```lean
theorem ws2_other_distinguishes (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsR) rankR) oth slf
```
- Plain-bisim via `plainOf_rankLiftR` + `ws1_atomless_bisim` with `ws1_rcar_SHNE`; label-separation by the edge
  argument (`oth`'s outgoing edge tagged `⟨1⟩`, none of `slf`'s edges tagged `⟨1⟩`), the `firstOther_label_sep`
  argument. Shared by C1 and C2.

### C1, the reader is load-bearing (the K1 payoff, the lead)

The reader is a NAMED `def selfReader` (a fixed bounded reader: focus `slf`, reading `{slf}`, finite, grounded),
NOT an existential over readers (the C1-S1 repair — the blind Phase C review flagged the existential form as the
reader quantified out, a `Many`-style claim). The other `oth` is real FOR that fixed named reader: `oth` is
plain-bisimilar to the read relatum `slf ∈ selfReader.reads` yet label-separated from it (`RealFor` via
`ws2_other_distinguishes`). The reader's `reads` membership is LOAD-BEARING; `Many` is not used; the reader
cannot be tailored per witness.

```lean
noncomputable def selfReader (hinf : ℵ₀ ≤ κ) : FiniteAttention (rankLift (outDest hinf attendsR) rankR) :=
  ⟨slf, {slf}, Set.finite_singleton slf, ⟨Set.mem_singleton slf, …grounded by ReflTransGen.refl…⟩⟩

theorem ws2_other_reader_wise (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (selfReader hinf) oth
```
- **Ambient:** `FiniteAttention`, `RealFor`, `ws2_other_distinguishes`, `Set.finite_singleton`,
  `ReflTransGen.refl`.
- **Success condition:** `⟨slf, Set.mem_singleton slf, ws2_other_distinguishes hinf⟩` for the FIXED reader
  `selfReader` (focus `slf`, reads `{slf}`, grounded by `ReflTransGen.refl`).
- **Failure mode:** *the reader quantified out / the other a bare label (K1, SERIOUS).* Foreclosed by the C1-S1
  repair: the reader is a NAMED `def` (not existential), its `reads` membership used to witness `RealFor`; the
  other's own reading (`attendsR oth`, all four readings from WS3) is what the separation distinguishes; `Many`
  (reader-erased) is not used. **Winner (K1 payoff).**

### C2, the twoness is non-recoverable (the import, audit (b))

The self/other separation is NOT recoverable from the plain (symmetric) relating: an import, which by Series 07
is what a genuine atomless distinction MUST be. The `ws2_tick_irreversible` / `ws2_distinction_free` pattern.

```lean
theorem ws2_other_non_recoverable (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
```
- **Ambient:** `ws2_other_distinguishes`, `ws4_recoverable_not_import`.
- **Success condition:** assume `Recoverable`; the plain-bisim half of `ws2_other_distinguishes` becomes a
  label-bisim via `ws4_recoverable_not_import`, contradicting the label-separation half. Exactly
  `ws2_tick_irreversible`'s second conjunct.
- **Failure mode:** *the twoness recoverable — the collapse smuggled shut (charter §4.b, SERIOUS).* Foreclosed:
  `¬ Recoverable` is a discharged proof term, the otherness an import (Series 07). **Winner (import).**

### C3, the other via `Many` (the PR1-S2 trap to avoid)

```lean
theorem ws2_other_bad (hinf) : Many (rankLift (outDest hinf attendsR) rankR)   -- reader-erased plurality
```
- **Failure mode:** *`Many` erases the reader — it asserts SOME pair is separated, with no attention consuming
  it (K1 / PR1-S2, SERIOUS).* **Reject.** The reader must be load-bearing (`RealFor` on a named attention, C1),
  not an existential over separated pairs.

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C0 | `AttentionDistinguishes oth slf` | engine + rank lift | yes (S0/S1 pattern) | **win (engine)** |
| C1 | reader load-bearing, `RealFor` on a named attention | `FiniteAttention`, C0 | yes | **win (K1)** |
| C2 | twoness `¬ Recoverable` | C0, `ws4_recoverable_not_import` | yes | **win (import)** |
| C3 | `Many` (reader-erased) | — | K1/PR1-S2 | reject (SERIOUS) |

## Winning candidates: C0 + C1 + C2

**Proof architecture.** C0 generalizes `firstOther_label_sep` to the two loci (plain side by the collapse
engine, label side by the rank edge argument). C1 wraps C0 in a NAMED `FiniteAttention` for which `oth` is
`RealFor` — the reader load-bearing, `Many` unused. C2 turns the label-separation into `¬ Recoverable` via
`ws4_recoverable_not_import`. Lands `readerTwo = true` for WS5. **Dependencies:** `ws1_rcar_SHNE`,
`plainOf_rankLiftR`, `rankLiftR_val` (WS1); `ws1_atomless_bisim`, `ws4_recoverable_not_import`, `FiniteAttention`,
`RealFor`, `AttentionDistinguishes` (imported).

## Outcome classes (per charter §5)

- **readerTwo = true (the expected WS2 payoff):** the reader load-bearing (`RealFor` on a named attention), the
  twoness `¬ Recoverable`.
- **ONE (pre-registered, first-class):** if the separation proved RECOVERABLE (`ws2_other_non_recoverable`
  refuted), reported ONE — the other recoverable from the self, the world the One (Series 07). Foreclosed here by
  C2, but pre-registered.
- **PARTIAL (pre-registered):** if the reader landed only reader-erased (`Many`, no `RealFor`), reported PARTIAL
  — the twoness label-wise only, the reader not load-bearing. Foreclosed by C1.

## Strip test (charter §0.3)

`ws2_other_reader_wise` strips (delete "other," "self," "reader," "perspective") to *"there is a
`FiniteAttention` for which the relatum `oth` is `RealFor`: `oth` is plain-bisimilar to a read relatum yet
`AttentionDistinguishes`-separated from it"* — a bare `RealFor` / `AttentionDistinguishes` fact, the WS2 SHOULD
per charter §0.3. `ws2_other_non_recoverable` strips to *"the rank lift over `outDest attendsR` is
`¬ Recoverable`"* — a bare import fact. Both survive: no name is a term, the reader is a `FiniteAttention` not a
label.

## Deliverable

`formal/P2S2/ws2.lean`: `ws2_other_distinguishes`, `ws2_other_reader_wise`, `ws2_other_non_recoverable`. The
reader load-bearing (a named `FiniteAttention`, not `Many`, K1); the twoness `¬ Recoverable` (an import, Series
07). Axiom check reduces through the collapse engine, `rankLift`, and `decide` to the standard three.
