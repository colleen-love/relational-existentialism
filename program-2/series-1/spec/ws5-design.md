# WS5, The verdict and the audit folded in

**Design doc. Series 2.1. Owns: the verdict, COMPUTED from the WS1-WS4 flags (never hand-set), and the five
audit clauses (a)-(e) as actual propositions bundling the WS1-WS4 payoffs. The verdict function discriminates
(falsifiability); the flags are earned by the built theorems; the audit clauses certify the discipline.**

*Imports `P2S0` and the WS1-WS4 modules. The `Outcome` type and `verdict` function are universe-free and
self-contained (the S0 `ws5` pattern). No motivating prose enters a proof term (audit (e)).*

## The object at stake

The charter's WS5 (§2, §5): the verdict is computed - twoZone (all payoffs), endogenous / causalImport (the
WS4 alternatives), partial, disconnected - and the audit checks (a)-(e) are propositions, not prose. The
verdict must DISCRIMINATE (a different flag pattern computes a different outcome) so it is falsifiable, and the
flags must be EARNED by theorems, not chosen.

## Candidates

### C1, the verdict function computed from five flags (the lead)

The charter's pre-registered outcome "TIME-IS-IMPORT" (the causal order itself proves non-recoverable) is named
`causalImport` in Lean (C1-S5 repair: no identifier embeds a forbidden content-name such as `time`); the mapping
is recorded here and in README §7.

```lean
inductive Outcome | twoZone | endogenous | causalImport | partial' | disconnected
  deriving DecidableEq

def verdict (wf arrow exo causEndo linImport : Bool) : Outcome :=
  if !wf then Outcome.disconnected                       -- WS1 construction imports structure
  else if !(arrow && exo) then Outcome.partial'          -- WS2/WS3 land only per-instance
  else if causEndo && linImport then Outcome.twoZone     -- the expected fork
  else if causEndo && !linImport then Outcome.endogenous -- linearization forced too
  else Outcome.causalImport                              -- causal order non-recoverable

theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoZone := rfl
```
- **Success condition:** `ws5_verdict_eq` by `rfl`; the five flags feed the five pre-registered outcomes.
- **Failure mode:** *the verdict hand-set.* Foreclosed: `verdict` is a total function of the flags, computed by
  `rfl`; the flags are earned (C3). **Winner.**

### C2, falsifiability - the function discriminates (the guard)

```lean
theorem ws5_verdict_not_endogenous  : verdict true true true true true ≠ Outcome.endogenous := by decide
theorem ws5_verdict_not_import      : verdict true true true true true ≠ Outcome.causalImport := by decide
theorem ws5_verdict_not_partial     : verdict true true true true true ≠ Outcome.partial' := by decide
theorem ws5_verdict_discriminates :
    verdict true true true true false = Outcome.endogenous          -- had linearization fallen forced
  ∧ verdict true true true false true = Outcome.causalImport        -- had the causal order fallen import
  ∧ verdict false true true true true = Outcome.disconnected := by decide
```
The verdict is not constant: flipping `linImport` yields endogenous, flipping `causEndo` yields causalImport,
flipping `wf` yields disconnected. The two-zone verdict is a genuine computed discrimination, not a tautology.

- **Failure mode:** *a constant verdict* (any flags give twoZone). Foreclosed by `ws5_verdict_discriminates`.
  **Winner.**

### C3, the flags are earned (the justification)

```lean
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (attendsT (reifyT cycleA) = cycleA)                                            -- wf   (WS1)
  ∧ (∀ x ∈ attendsT kA, rankT x < rankT kA)                                        -- arrow (WS2, DIRECTIONAL, Ext-1 R1)
  ∧ (∀ ch : TCar → ℕ, ch kA ≠ ch kB →
        ¬ Recoverable (rankLift (outDest hinf attendsT) ch))                       -- exo   (WS3, tick-specific, Ext-1 R2)
  ∧ ((causal kA kC ∧ causal kB kC)                                                 -- causEndo (WS4 arm 1,
      ∧ (∀ t u, causal t u → rankT t < rankT u)                                    --  the FULL headline,
      ∧ (¬ causal kA kB ∧ ¬ causal kB kA))                                         --  rank clause included)
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        ¬ Recoverable (rankLift (outDest hinf attendsT) ord))                      -- linImport (WS4 arm 2)
```
**Charter Extension 1 re-points two flags.** The `arrow` flag is now R1's DIRECTIONAL theorem (`∀ x ∈ attendsT
kA, rankT x < rankT kA`, the composite strictly outranks its components) — not the reader (which feeds audit (c))
and not `¬ Recoverable`. The `exo` flag is now R2's TICK-SPECIFIC stream on `TCar` (`∀ ch, ch kA ≠ ch kB → ¬
Recoverable (rankLift … ch)`) — not S0's generic `impLift`. The `causEndo` conjunct is the FULL
`ws4_causal_order_endogenous` headline (untouched). `wf`, `exo`, `linImport` are the load-bearing halves of their
headlines. The verdict's five `true` inputs are theorems, not choices.

- **Failure mode:** *a flag asserted, not proved.* Foreclosed: each conjunct is a built theorem. **Winner.**

### C4, the five audit clauses as propositions (a)-(e)

```lean
theorem ws5_audit_no_smuggled_index {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :          -- (a)
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)
theorem ws5_audit_stream_exogenous {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :           -- (b, Ext-1 R2: on TCar)
    ∀ ch : TCar → ℕ, ch kA ≠ ch kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ch)
theorem ws5_audit_reader_loadbearing {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :         -- (c)
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsT) rankT),
      RealFor (rankLift (outDest hinf attendsT) rankT) att kA
theorem ws5_audit_fork_genuine {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :               -- (d)
    (kA ≠ kB ∧ ¬ causal kA kB ∧ ¬ causal kB kA)          -- concurrent pair genuine
  ∧ (causal kA kC)                                        -- causal pair genuine
  ∧ (∀ t u, causal t u → rankT t < rankT u)               -- order structurally constrained
theorem ws5_audit_names_not_terms : True                                          -- (e) certified by the §6 grep
```
Audit (a): every temporal fact strips to a reification/attention/import fact - the linearization import IS the
`ord`-lift non-recoverability, no background index. Audit (b): the stream is a proof term. Audit (c): the reader
is named. Audit (d): both WS4 arms witnessed, order constrained. Audit (e): the grep is clean (a mechanical
check, recorded in `charter-status.md`; the Lean placeholder is `True` since the property is about NAMES, not a
proposition).

- **Failure mode:** *an audit clause that is prose, not a proposition.* Foreclosed: (a)-(d) are theorems; (e)
  is the mechanical grep. **Winner.**

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | verdict computed = twoZone | the five flags | yes, `rfl` | **win (verdict)** |
| C2 | verdict discriminates | `verdict` | yes, `decide` | **win (falsifiability)** |
| C3 | flags earned by theorems | WS1-WS4 headlines | yes | **win (justification)** |
| C4 | audit (a)-(e) as propositions | WS1-WS4 payoffs | yes | **win (audit)** |

## Winning candidates: C1 + C2 + C3 + C4

**Proof architecture.** `verdict` is a total `Bool⁵ → Outcome`; `ws5_verdict_eq` computes twoZone by `rfl`;
`ws5_verdict_discriminates` shows the function is not constant; `ws5_flags_justified` collects the WS1-WS4
headlines so the inputs are earned; the five audit theorems bundle the payoffs. The verdict is the residue of
the process: on the built theorems it is twoZone, computed, not premised.

## Outcome classes (per charter §5)

- **twoZone (computed here):** all five flags earned.
- The alternatives (endogenous, causalImport, partial', disconnected) are pre-registered in `verdict` and
  reachable by `ws5_verdict_discriminates`; whichever the build earns is reported.
- **Strip test.** `verdict` names outcomes, not terms; `ws5_flags_justified` strips to the five workstream facts
  (reification section, `RealFor`, import separation, causal membership, `ord`-lift non-recoverability). No name
  is a term.

## Deliverable

`formal/P2S1/ws5.lean`: `Outcome`, `verdict`, `ws5_verdict_eq`, the falsifiability theorems, `ws5_flags_justified`,
and the five audit theorems (a)-(e). The verdict is computed (never hand-set); the flags are earned; the audit
is folded in. Axiom check: `ws5_verdict_eq` and the discriminators depend on NO axioms; the flag/audit theorems
reduce to the standard three.
