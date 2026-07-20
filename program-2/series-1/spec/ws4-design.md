# WS4, The clock knot (the genuinely-uncertain obligation, K2)

**Design doc. Series 2.1, the knot. Owns: the two orders on ticks and the two-zone fork. The CAUSAL partial
order (tick `t` precedes tick `u` when `u`'s closure consumes a relatum `t` produced) is endogenous, forced
within what the relating sees (`ws4_causal_order_endogenous`); every LINEARIZATION of a genuinely concurrent
pair the stream supplies is a genuine import, non-recoverable from the relating (`ws4_linearization_import`).
Both arms witnessed on the SAME structure, a genuine causal pair and a genuine concurrent pair, the order
structurally constrained. The sin (charter §4.d, PR1-S1): the ordering decided by definition - a causal order
total by construction or a concurrency that is empty, making the import claim vacuous.**

*Imports `P2S0`; the causal order is `attendsT`-membership among the composites of the witness `TCar`
(README §3); the linearization import reuses the `rankLift` separation pattern with an EXOGENOUS order label
(not the endogenous `rankT`); the collapse engine (`ws1_atomless_bisim`) plain-identifies the concurrent pair.
The two watch-point checks (protocol §0.8) are the whole burden here.*

## The object at stake

The charter's WS4 (§2): define two orders on ticks - the causal partial order and any linearization extending
it to concurrent pairs - and prove the two-zone fork: causal endogenous, linearization import, the wall between
them Series 07's import boundary. Both arms reachable on a witnessed structure: a concurrent pair must exist
(else the linearization claim is the PR1-S1 tautology) and a causal pair must exist (else endogeneity is
empty). The order relation must carry a structural constraint, not be decided by an unconstrained parameter.

## The witnessed pairs (audit (d) non-vacuity, fixed first)

On `TCar` (README §3): the ticks (`isTick`) are the composites `kA` (cycle A), `kB` (cycle B), `kC = reifyT
{kA,kB}`.
- **Causal pair (non-empty):** `causal kA kC` and `causal kB kC` - `kC` (a tick) consumes both `kA`,`kB` (a
  tick each), `kA,kB ∈ attendsT kC` (`decide`).
- **Concurrent pair (non-empty):** `kA ≠ kB`, `¬ causal kA kB`, `¬ causal kB kA` - neither consumes the other
  (`decide`).
Both on `TCar`. The concurrency is genuinely non-empty and the causal order is genuinely partial (not total:
`kA`,`kB` are incomparable), foreclosing PR1-S1.

## Candidates

### C1, the causal order as `attends`-membership, endogenous and rank-constrained (the lead, arm 1)

The causal order `causal t u := t ∈ (attendsT u)` reads directly off the relating; it is exhibited on the
causal pair, is a genuine strict order (rank-constrained: consuming a product raises the tower), and leaves the
concurrent pair incomparable.

```lean
def isTick (x : TCar) : Prop := x = kA ∨ x = kB ∨ x = kC   -- the produced relata (ticks/closures)
def causal (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u   -- u (a tick) consumes t (a produced tick)

theorem ws4_causal_order_endogenous :
    (causal kA kC ∧ causal kB kC)                          -- the causal pair is witnessed (non-empty)
  ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)         -- structurally constrained: consuming raises rank
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA)                      -- the concurrent pair is incomparable (partial, not total)
```
**The causal order is BETWEEN ticks, not within them (C1-S1/S2 repair).** `causal` is the "which tick consumes
which tick's product" relation on the produced relata (`isTick`), NOT bare `attendsT`-membership over the whole
carrier: the base 2-cycle edges (`p1 ∈ attendsT p0`, equal rank 0) are WITHIN-tick relating and are correctly
NOT causal edges. The only tick-to-tick consumption edges are `kA, kB ∈ attendsT kC`, so `causal t u → rankT t
< rankT u` holds (`decide`) - the between-tick order is acyclic (a DAG), rank-constrained, and genuinely partial
(the concurrent pair `kA`,`kB` is incomparable). The order is ENDOGENOUS: `causal` is defined from `attendsT`
and `isTick`, the plain relating, with no exogenous label. It
is forced (recoverable): reading `attendsT` determines it. The rank constraint (`decide`, using that composites
outrank their constituents) is the structural constraint audit (d) demands - the order is not total by
construction (the concurrent pair refutes totality).

- **Ambient:** `attendsT`, `rankT` (README §3).
- **Success condition:** all conjuncts by `decide`.
- **Failure mode:** *the causal order total by construction (PR1-S1, SERIOUS).* Foreclosed: `¬ causal kA kB ∧
  ¬ causal kB kA` exhibits an incomparable pair. **Winner (arm 1, endogenous).**

### C2, the linearization as an exogenous label, non-recoverable, quantified (the lead, arm 2)

To order the concurrent pair `kA`,`kB` - which came first - the stream must supply a label, and every such
label is non-recoverable from the plain relating. Model the linearization as `rankLift` with an EXOGENOUS order
function `ord : TCar → ℕ` (NOT the endogenous `rankT`; `rankT kA = rankT kB = 1`, so the tower does NOT order
them). For any `ord` with `ord kA ≠ ord kB`, the ordered lift plain-identifies `kA`,`kB` (collapse engine) yet
is label-separated.

```lean
-- kA, kB are plain-bisimilar (collapse engine) yet separated by ANY exogenous order label distinguishing them
theorem ws4_linearization_import {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB   -- plain-bisim, label-separated
      ∧ (¬ Recoverable (rankLift (outDest hinf attendsT) ord))                -- the linearization is an import
```
Plain-bisim via `ws1_atomless_bisim` on `plainOf (rankLift … ord) = outDest attendsT` (`plainOf_rankLiftT`)
with `SHNE` (WS1); label-separation by the edge argument (`ord kA ≠ ord kB`), the `ws2_many_general` /
`firstOther_label_sep` pattern generalized to an arbitrary label. `∀ ord` = "every linearization the stream
supplies"; `ord` is the exogenous order, quantified, never named (audit (e)). Non-recoverability is the import.

- **Ambient:** `ws1_atomless_bisim`, `rankLift`, `AttentionDistinguishes`, `Recoverable`, `plainOf_rankLiftT`,
  `ws1_tcar_SHNE`.
- **Success condition:** typechecks `∀ ord`; both conjuncts hold on the concurrent pair.
- **Failure mode:** *the concurrency empty (PR1-S1, SERIOUS)* or *`ord` an unconstrained parameter deciding the
  order by fiat.* Foreclosed: the concurrent pair is witnessed (`kA ≠ kB`, incomparable in `causal`); `ord` is
  quantified and its separation is the IMPORT (non-recoverable), the honest content, not a fiat order on the
  endogenous side. **Winner (arm 2, import).**

### C3, the two-zone fork bundled (the audit-facing aggregate)

```lean
theorem ws4_two_zone {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (causal kA kC ∧ ¬ causal kA kB ∧ ¬ causal kB kA)            -- causal: a witnessed, partial, endogenous order
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        ¬ Recoverable (rankLift (outDest hinf attendsT) ord))    -- linearization: import, quantified
```
The conjunction of the two arms, one object for WS5. The wall between the conjuncts is Series 07's boundary:
the causal order is on the recoverable side, the linearization on the non-recoverable side. **Winner (aggregate).**

### C4, the linearization decided by `rankT` (the tautology to avoid)

```lean
theorem ws4_linearization_bad : ∀ t u, rankT t < rankT u → linBefore t u   -- order the concurrent pair by rank
```
- **Failure mode:** *the concurrent pair has EQUAL rank (`rankT kA = rankT kB`), so `rankT` does NOT order
  them; forcing an order on them by an endogenous quantity would be false, and forcing it by a total parameter
  would be the PR1-S1 fiat (SERIOUS).* **Reject.** The linearization is genuinely exogenous (C2); the tower
  cannot supply it - that IS the two-zone result.

### C5, grain (the WS4-enrichment candidate, deferred)

The grain fork (`spec/grain-exploration.md`): resolution ordered where the tower can see it, an import where it
cannot - the clock knot's twin. **Decision (Phase B): DEFER to a later series.** Grain would overload WS4 with a
second fork on the same structure and risks diluting the clock knot's non-vacuity. Recorded in
`charter-status.md` §5 as a disclosed scope decision; the exploration stands for 2.x. **Reject as 2.1 content.**

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | causal = `attendsT`-membership, endogenous, rank-constrained, partial | `attendsT`, `rankT` | yes, `decide` | **win (arm 1)** |
| C2 | linearization exogenous, non-recoverable, quantified | `ws1_atomless_bisim`, `rankLift` | yes (S0 pattern) | **win (arm 2)** |
| C3 | two-zone bundle | C1 + C2 | yes | **win (aggregate)** |
| C4 | linearization by `rankT` | — | false / fiat | reject (tautology, SERIOUS) |
| C5 | grain enrichment | `prec`, `¬ Recoverable` | yes, but overloads WS4 | **defer to 2.x** |

## Winning candidates: C1 + C2 + C3 (grain deferred)

**Proof architecture.** C1 is `decide` on the witness (the causal order read off `attendsT`, rank-constrained,
partial). C2 generalizes the `rankLift` separation to an arbitrary exogenous label `ord`, the plain side by the
collapse engine, the label side by the edge argument; quantified over all `ord` distinguishing the concurrent
pair. C3 bundles them. The wall is Series 07's boundary: the causal order recoverable, the linearization not.
Both arms on `TCar`, witnessed causal pair (`kA ≺ kC`) and concurrent pair (`kA`,`kB`). Lands `causEndo = true`
and `linImport = true` for WS5. **Dependencies:** WS1's witness, `ws1_tcar_SHNE`, `plainOf_rankLiftT`,
`rankLiftT_val`.

## Outcome classes (per charter §5)

- **twoZone (the expected WS4 payoff, `causEndo = true ∧ linImport = true`):** causal endogenous, linearization
  import, both witnessed.
- **ENDOGENOUS (pre-registered, first-class):** if the linearization proves FORCED too (some endogenous quantity
  orders the concurrent pair, `linImport` refuted), reported ENDOGENOUS in its direction - honorable, not a
  failure. Here `rankT kA = rankT kB` blocks this, so the import stands; but the alternative is pre-registered.
- **TIME-IS-IMPORT (pre-registered, first-class):** if the causal order proves NON-recoverable (`causEndo`
  refuted), reported TIME-IS-IMPORT - Program 2 would need a second import for time itself. Foreclosed here by
  C1 (`causal` is `attendsT`-membership, manifestly recoverable), but pre-registered.
- **Strip test.** `ws4_causal_order_endogenous` strips to *"`causal kA kC`, `causal kB kC` (both a conjunction
  of `isTick` flags and `attendsT`-membership), `causal` implies strict rank increase, and `kA`,`kB` are
  `causal`-incomparable"* - a bare membership/rank fact.
  `ws4_linearization_import` strips to *"for every `ord` with `ord kA ≠ ord kB`, the `ord`-lift over
  `outDest attendsT` is plain-bisimilar on `kA`,`kB` yet label-separated, hence not `Recoverable`"* - a bare
  import fact. Both survive deletion of "clock", "time", "before", "after", "order"; no name is a term.

## Deliverable

`formal/P2S1/ws4.lean`: `causal`, `ws4_causal_order_endogenous`, `ws4_linearization_import`, `ws4_two_zone`.
Both arms on `TCar` (audit (d)); the causal order rank-constrained and partial (not PR1-S1); the linearization
quantified over `ord`, never named (audit (e)); grain deferred. Axiom check reduces through the collapse engine,
`rankLift`, and `decide` to the standard three.
