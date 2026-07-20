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

### C1, the stream is a TICK-SPECIFIC choice label on `TCar` (Charter Extension 1 R2, the lead)

**Charter Extension 1 (EXT-F1, R2) raises the bar here.** The first build reused S0's generic `impLift` on
`Bool` — exogeneity genuine but disconnected from the actual tick machinery (`kA`/`kB`/`attendsT` on `TCar`).
The rebuild puts the stream's choice ON the real carrier: the choice among the concurrent available closures
`kA`, `kB` is an exogenous label `ch : TCar → ℕ` distinguishing them, non-recoverable, proved via the collapse
engine on `outDest attendsT`, quantified over all such labels, never named. (This is the WS4-linearization
pattern reused for the choice; WS4 itself is untouched.)

```lean
theorem ws3_stream_exogenous {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ ch : TCar → ℕ, ch kA ≠ ch kB →
        AttentionDistinguishes (rankLift (outDest hinf attendsT) ch) kA kB   -- plain-identified, choice-separated
      ∧ (¬ Recoverable (rankLift (outDest hinf attendsT) ch))                -- the choice is NOT recoverable
```
The two concurrent closures `kA`, `kB` are plain-bisimilar on the real carrier (`ws1_atomless_bisim` on
`outDest attendsT`, both `SHNE` from WS1) — the relating does not force which closes. The exogenous choice label
`ch` separates them (the edge argument, `ch kA ≠ ch kB`), and no choice is recoverable (Series 07). `ch` is the
picker among concurrent closures, quantified, never named. **This is the tick's actual choice-point on `TCar`,
not a generic `Bool`.**

- **Ambient:** `ws1_atomless_bisim`, `rankLift`, `AttentionDistinguishes`, `Recoverable`, `plainOf_rankLiftT`,
  `ws1_tcar_SHNE`, `rankLiftT_val` (WS1) — no S0 `impLift`.
- **Success condition:** typechecks `∀ ch`; both conjuncts on `TCar`. The stream lives at the tick (EXT-F1 fixed).
- **Failure mode (foreclosed by R2):** *the stream generic, disconnected from the tick (EXT-F1)* — now on the
  real carrier; *the choice recoverable (§4.c)* — foreclosed, `¬ Recoverable` proved. **Winner.**

### C2, the choice is load-bearing: without it, the closures are one (Charter Extension 1 R2)

If the tick required no choice, the plain relating on `TCar` would already determine which closure fires; but
`kA`, `kB` are plain-identified there (the collapse engine), so the choice is genuinely indeterminate without
the stream.

```lean
theorem ws3_tick_needs_stream {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (outDest hinf attendsT) R ∧ R kA kB)                       -- the closures are plain-identified on TCar
  ∧ (∀ ch : TCar → ℕ, ch kA ≠ ch kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ch))  -- so any choice is an import
```
The first conjunct: `kA`, `kB` are plain-bisimilar on the real carrier (`ws1_atomless_bisim`), so the relating
alone does not determine the closure. The second: every exogenous choice label is non-recoverable, so the
stream's entry is load-bearing rather than cosmetic. On `TCar`, not `Bool` (EXT-F1 fixed).

- **Ambient:** `ws1_atomless_bisim`, `ws1_tcar_SHNE`, `rankLift`, `Recoverable` (WS1).
- **Failure mode:** *the choice cosmetic.* Foreclosed: the plain identification on `TCar` shows the relating
  does not determine the closure. **Winner.**

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
| C1 | choice exogenous on `TCar`, quantified over `ch : TCar → ℕ` (Ext-1 R2) | `ws1_atomless_bisim`, `rankLift` | yes | **win (exogeneity)** |
| C2 | choice load-bearing on `TCar` (closures plain-identified) (Ext-1 R2) | `ws1_atomless_bisim` | yes | **win (obligation)** |
| C3 | name the selection | — | selects a tick | **reject (audit e, SERIOUS)** |
| C4 | choice definable from field | — | recoverable | **reject (§4.c, SERIOUS)** |

## Winning candidates: C1 + C2 (Charter Extension 1 R2 — on `TCar`)

**Proof architecture.** Both live on the real carrier `TCar` (Ext-1 R2), reusing the WS4-linearization pattern
(WS4 untouched): the choice among the concurrent closures `kA`,`kB` is an exogenous label `ch : TCar → ℕ`.
`ws3_stream_exogenous` proves, for every `ch` distinguishing them, that they are plain-bisimilar
(`ws1_atomless_bisim` on `outDest attendsT`) yet choice-separated (the edge argument), hence `¬ Recoverable`.
`ws3_tick_needs_stream` gives the plain identification of `kA`,`kB` on `TCar` plus the quantified
non-recoverability. Together they land `exo = true` for WS5, now genuinely at the tick. The stream is quantified,
never named (audit (e)); it stays non-recoverable (a recoverable stream would collapse the dynamics, Series 07).

## Outcome classes (per charter §5)

- **Exogenous and load-bearing (the WS3 payoff, feeds `exo = true`):** both theorems typecheck on `TCar`; the
  choice non-recoverable, quantified, tick-specific.
- **Partial (pre-registered):** the choice is exogenous but not shown load-bearing (C2 fails); reported Partial,
  `exo` demoted.
- **Strip test.** `ws3_stream_exogenous` strips to *"for all `ch : TCar → ℕ` with `ch kA ≠ ch kB`, the `ch`-lift
  over `outDest attendsT` is plain-bisimilar yet label-separated on `kA`,`kB`, hence not `Recoverable`"* — a bare
  import fact on the real carrier. `ws3_tick_needs_stream` strips to *"`kA`,`kB` are plain-bisimilar, and every
  distinguishing `ch`-lift is not `Recoverable`"*. No name is a term; `ch` is quantified.

## Deliverable

`formal/P2S1/ws3.lean`: `ws3_stream_exogenous`, `ws3_tick_needs_stream`, on `TCar` (Ext-1 R2), via
`ws1_atomless_bisim` + the `rankLift`/`ch` separation (the WS4-linearization pattern, WS4 untouched). The stream
is quantified, never named (audit (e)); it stays non-recoverable. Axiom check reduces to the standard three.
