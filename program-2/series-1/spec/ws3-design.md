# WS3, The stream and the tick (the exogeneity knot, K4)

**Design doc. Series 2.1. Owns: the tick draws on the EXOGENOUS stream. Identify the choice-point (which of
several available cycles closes) and draw it from the stream; prove the choice non-recoverable from the plain
relating (`ws3_stream_exogenous`, in the manner of S0's `impLift` / `ws4_import_quantified`) and load-bearing
(`ws3_tick_needs_stream`: without the choice the options collapse to the One, so the stream's entry is an
obligation). The sin (charter §4.c): the stream smuggled below the line, the choice a definable function of the
field, which by Series 07 collapses the dynamics.**

*Imports `P2S0`; the stream IS S0's seated import `impLift` located at the tick's choice-point (charter §3: the
stream generalizes `impLift` into succession). Reuses `impLift`, `ws4_import_breaks_baseline`,
`ws4_import_quantified` (README §1). The two available cycles A, B of the witness (README §3) are the choice.*

## The object at stake

The charter's WS3 (§2): the tick is one cycle-closure event; a choice is required (which of several available
cycles closes); that choice is drawn from the exogenous stream and is (a) non-recoverable and (b) load-bearing.
The stream is quantified over, never named or selected (audit (e)). The pre-registered sin: the choice a
definable function of the relating, hence recoverable, hence the deterministic-relational One (Series 07).

## Candidates

### C1, the choice-point as S0's exogenous import, quantified (the lead)

The witness carries two concurrent available closures, `kA` (cycle A) and `kB` (cycle B), plain-bisimilar
(neither is forced by the relating). Which one the tick closes is an exogenous label: model the two options as
`Bool` and the stream as `impLift`. The choice is non-recoverable, quantified over ALL import value-spaces and
functions, none named.

```lean
theorem ws3_stream_exogenous {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type} (f : Bool → Q), f true ≠ f false →
        (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R true false)   -- the options are plain-identified
      ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false)          -- the choice is NOT plain-recoverable
```
This is exactly `ws4_import_breaks_baseline hinf f hf` (S0), reused: the plain relating identifies the two
available closures, the exogenous choice separates them. `Bool` encodes {close-A, close-B}. No proof term names
which closes; `f` is quantified.

- **Ambient:** `impLift`, `ws4_import_breaks_baseline` (S0).
- **Success condition:** the reuse typechecks; `∀ Q f` quantification holds (audit (e)).
- **Failure mode:** *the choice recoverable (charter §4.c, SERIOUS).* Foreclosed: the second conjunct is
  `¬ ∃ label-bisim`, S0's proven separation. **Winner.**

### C2, the choice is load-bearing: without it, the One (the obligation)

If the tick required no choice, the plain relating would already determine the closure, and by the collapse the
two options are behaviorally identified - a genuine determinate tick REQUIRES the exogenous entry.

```lean
theorem ws3_tick_needs_stream {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (impLift hinf (id : Bool → Bool))) R ∧ R true false)  -- plain: the options are one
  ∧ (¬ Recoverable (impLift hinf (id : Bool → Bool)))                            -- so the choice is an import
```
The first conjunct: the plain projection identifies the options (the collapse - without the import they are the
One). The second: the identity import (the canonical non-choice, not a content-name) is non-recoverable, so the
choice is genuinely load-bearing rather than cosmetic. This is `ws4_import_quantified.2` plus the plain-bisim
witness. Together: the stream's entry is what makes the tick determinate, an obligation not an assumption.

- **Ambient:** `ws4_import_quantified`, `plainOf_impLift_true_bisim` (S0).
- **Failure mode:** *the choice cosmetic* (the tick determinate without the stream). Foreclosed: the plain
  identification shows the relating alone does not determine the closure. **Winner.**

### C3, name the stream's selection (the forbidden fill)

```lean
def theTickThatFires : Bool := true    -- selects cycle A
theorem ws3_stream_selected : impLift hinf (fun _ => theTickThatFires) …
```
- **Failure mode:** *naming the stream / selecting a tick (charter §4.e, audit (e), SERIOUS).* **Reject.** C1
  quantifies over `f`; the `id` witness in C2 is the canonical non-choice, not a selection.

### C4, the choice as a definable function of the field (the smuggle)

```lean
def choice (x : Bool) : Bool := decide (x ∈ attendsSomething)   -- recovered from the relating
```
- **Failure mode:** *the stream smuggled below the line (charter §4.c, SERIOUS).* A definable choice is
  recoverable, collapsing to the One by Series 07. **Reject.** The choice must be `¬ Recoverable` (C1).

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | choice exogenous, quantified | `ws4_import_breaks_baseline` | yes (S0 reuse) | **win (exogeneity)** |
| C2 | choice load-bearing, else One | `ws4_import_quantified` | yes | **win (obligation)** |
| C3 | name the selection | — | selects a tick | **reject (audit e, SERIOUS)** |
| C4 | choice definable from field | — | recoverable | **reject (§4.c, SERIOUS)** |

## Winning candidates: C1 + C2

**Proof architecture.** Both reuse S0's proven `impLift` machinery, located at the tick's choice-point (the two
concurrent available closures `kA`/`kB`, encoded as `Bool`). `ws3_stream_exogenous` = `ws4_import_breaks_baseline`
quantified over all `Q`, `f`; `ws3_tick_needs_stream` = the plain identification plus `ws4_import_quantified.2`
non-recoverability. Together they land `exo = true` for WS5. The stream is quantified, never named (audit (e));
the reuse is disclosed in `charter-status.md` §5 (the stream is S0's import, generalized to succession).

## Outcome classes (per charter §5)

- **Exogenous and load-bearing (the WS3 payoff, feeds `exo = true`):** both theorems typecheck; the choice
  non-recoverable and quantified.
- **Partial (pre-registered):** the choice is exogenous but not shown load-bearing (C2 fails), so exogeneity is
  real but the tick's dependence on it is not; reported Partial, `exo` demoted.
- **Strip test.** `ws3_stream_exogenous` strips to *"for all `Q`, `f` with `f true ≠ f false`, `impLift f` is
  plain-bisimilar yet label-separated on `true`,`false`"* - a bare import fact. `ws3_tick_needs_stream` strips
  to *"the plain projection of `impLift id` identifies `true`,`false`, and `impLift id` is not `Recoverable`"*.
  No name is a term; the stream is `impLift`, quantified.

## Deliverable

`formal/P2S1/ws3.lean`: `ws3_stream_exogenous`, `ws3_tick_needs_stream`, reusing S0's `impLift` /
`ws4_import_breaks_baseline` / `ws4_import_quantified` at the choice-point. The stream is quantified, never
named (audit (e)). Axiom check reduces through the S0 import machinery to the standard three.
