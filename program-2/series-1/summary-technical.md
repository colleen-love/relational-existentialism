# Series 2.1 — Technical summary

**Verdict: TWO-ZONE, computed by `P2S1.verdict` from the WS1-WS4 flags (`ws5_verdict_eq : verdict true true
true true true = Outcome.twoZone`, by `rfl`). Build: sorry-free, axiom-clean (standard three only; several
theorems axiom-free), gate-green (`P2S1` imports `P2S0` and its own roots plus Mathlib; the `P1` foundation is
reached transitively through S0). Namespace `P2S1`, carrier `P2S0`.**

## The witness

One monomorphic carrier `TCar := Fin 7` at `Cardinal.{0}` carries every payoff (so WS4's two arms and the reader
payoff are exercised on the same structure, audit (d)):

- bases `p0,p1` (cycle A, `p0 ⇄ p1`), `q0,q1` (cycle B, `q0 ⇄ q1`); composites `kA = reifyT {p0,p1}`,
  `kB = reifyT {q0,q1}`; higher closure `kC = reifyT {kA,kB}`.
- `attendsT` gives each its cycle/pattern; `rankT` is the reification height (0 on bases, 1 on `kA,kB`, 2 on
  `kC`); `reifyT` is the pointwise `FinReify` section at the three used patterns.

All finite obligations reduce by the kernel (`decide`/`rfl`), as in the S0 `attendsU` witness.

## The theorems (all BUILT)

| WS | Theorem | Content | Strips to |
|----|---------|---------|-----------|
| WS1 | `ws1_cycle_reifies` | the 2-cycle reifies into `kA : TCar`, section `attendsT (reifyT cycleA) = cycleA`, distinct cycles → distinct composites | a `FinReify`/section fact |
| WS1 | `ws1_composite_attention_finite` | out-neighborhoods `< ℵ₀` (S0's bound, no ceiling), `attendsT kA = cycleA`, bounded by components | a bound-and-set fact |
| WS2 | `ws2_composite_distinguishes` | `AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kA p0` (plain-bisim via collapse engine + rank-1-vs-0 separation) | an `AttentionDistinguishes` fact |
| WS2 | `ws2_composite_residue` | `¬ ResidueRecoverable insp` (the global diagonal `ws2_residue_free`) ∧ a witnessed hold at `kA` (honest bare conjunction) | a `residue`-freeness fact |
| WS2 | `ws2_composite_real_for` | a named `FiniteAttention` (focus `p0`, reads `{p0}`) for which `kA` is `RealFor` — reader load-bearing, not `Many` | a `RealFor` fact |
| WS2 | `ws2_tick_irreversible` | `¬ Recoverable (rankLift (outDest hinf attendsT) rankT)` (the reification height is an import) | a `¬ Recoverable` fact |
| WS3 | `ws3_stream_exogenous` | `∀ Q f, f true ≠ f false →` plain-identified ∧ label-separated (`ws4_import_breaks_baseline`, quantified) | an import-separation fact |
| WS3 | `ws3_tick_needs_stream` | plain projection identifies the options ∧ `¬ Recoverable (impLift hinf id)` | a `¬ Recoverable` fact |
| WS4 | `ws4_causal_order_endogenous` | `causal kA kC ∧ causal kB kC`; `∀ t u, causal t u → rankT t < rankT u`; `kA,kB` incomparable | a membership/rank fact |
| WS4 | `ws4_linearization_import` | `∀ ord : TCar → ℕ, ord kA ≠ ord kB →` `AttentionDistinguishes (rankLift … ord) kA kB` ∧ `¬ Recoverable (rankLift … ord)` | an import (`¬ Recoverable`) fact |
| WS4 | `ws4_two_zone` | the aggregate: causal partial+endogenous, linearization import, quantified over `ord` | the two facts above |
| WS5 | `ws5_verdict_eq` | `verdict true true true true true = twoZone` (`rfl`, axiom-free) | the computed outcome |
| WS5 | `ws5_verdict_discriminates` | four discriminators (flip a flag → endogenous / causalImport / disconnected / partial') | falsifiability |
| WS5 | `ws5_flags_justified` | the five flags earned by the WS1-WS4 headlines (causEndo = the FULL causal headline) | the five workstream facts |
| WS5 | `ws5_audit_*` (a)-(e) | no smuggled index; stream exogenous; reader load-bearing; fork genuine; names-not-terms (`True`, mechanical grep) | the audit propositions |

## The two orders (the knot)

The causal order `causal t u := isTick t ∧ isTick u ∧ t ∈ attendsT u` (`isTick x := x = kA ∨ x = kB ∨ x = kC`)
is the "which tick consumes which tick's product" relation on the produced relata. It is endogenous (read off
`attendsT`), rank-constrained (`causal t u → rankT t < rankT u`, so acyclic), and genuinely partial (the
concurrent pair `kA,kB` is incomparable). The base 2-cycle edges are within-tick relating, correctly not causal
edges — the fix from the Phase C review (an unrestricted `attendsT`-membership would have made the equal-rank
base cycles violate the rank constraint).

The linearization is an exogenous label `ord : TCar → ℕ`. The tower rank cannot supply it (`rankT kA = rankT kB
= 1`), so `rankLift … rankT` does not separate `kA,kB`. For every `ord` with `ord kA ≠ ord kB`: the ordered
lift is plain-bisimilar on `kA,kB` (the collapse engine, `ord`-independent) yet label-separated (the `ord` label
survives, forcing `ord kA = ord kB`, contradiction), hence `¬ Recoverable`. Quantified over all such `ord`,
never named (audit (e)). This is the import boundary: the causal order recoverable, the linearization not.

## Discipline (audit)

- (a) No smuggled clock: no `Nat` step counter, no background index; the only order-relevant labels are the
  reification height `rankT` (used only to separate composites from bases, never to order the concurrent pair)
  and the exogenous `ord` (the import). Verified by the strip test and the §6 grep.
- (b) Stream exogenous: `ws3_stream_exogenous` / `ws5_audit_stream_exogenous` are `¬ Recoverable` proof terms.
- (c) Reader load-bearing: `ws2_composite_real_for` binds a `FiniteAttention` and uses `att.reads`; `Many` unused.
- (d) Fork genuine: concurrent pair (`kA ≠ kB`, incomparable) and causal pair (`causal kA kC`) both witnessed on
  `TCar`; order rank-constrained. No PR1-S1 tautology (concurrency non-empty, order not total).
- (e) Names-not-terms: no identifier embeds a forbidden content-name (the charter's TIME-IS-IMPORT outcome is
  `causalImport`; audit (a) is `ws5_audit_no_smuggled_index`). The §6 grep hits are docstring prose only.

## Provenance and deviations

- Layered import chain `P1 → S0 → S1` (program charter §2): `P2S1` imports `P2S0` only; the P1 machinery
  (`ws1_atomless_bisim`, `rankLift`, `AttentionDistinguishes`, `RealFor`, `ws2_residue_free`, `Recoverable`) is
  transitive through S0. Disclosed in `charter-status.md` §5.
- The stream is S0's `impLift` located at the tick's choice-point (charter §3); disclosed, not a narrowing.
- Grain (`spec/grain-exploration.md`) deferred to a later series; disclosed.

## Review history

- Phase C (design), pass 1: one SERIOUS root defect (C1-S1/S2, the unrestricted causal order breaking the rank
  constraint on the base cycles), two REAL, five COSMETIC. Repaired in Phase D (causal restricted to ticks; the
  residue conjunction relabelled honestly; the `timeIsImport`/`no_smuggled_clock` identifiers renamed). Pass 2
  returned zero SERIOUS.
- Phase F (code): see `charter-status.md` §4 for the ledger and closures.
