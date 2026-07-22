# Series 3.1 — The Arrow

The decisive series of Program 3. One question: does irreversibility emerge from coarse-graining a reversible flow — is the arrow of time the information a summary discards?

## Step zero result

Inherited from the program's step zero: the direction-erasing summary is lossy and its macro-step reads the erased microstate (`Derisk.lean`, check 3). This series builds the arrow on that seed.

## The objects

- The microdynamics: Series 3.0's state space `G` and transport moves, imported.
- The summary: `summary g a b := decide (b ∈ g a) || decide (a ∈ g b)` — the direction-erasing coarse-graining. This is Program 2's symmetric relating (`P2S0.sym`), the reading Series 2.0 proved blind to the knowing-asymmetry; the identification enters by bridge theorem.
- The macro alphabet: `Fin 3 → Fin 3 → Bool`, with the summary landing in its symmetric part.

## Targets

Workstream 1, the two levels:
- `ws1_summary_symmetric` — the summary is direction-blind: `summary g a b = summary g b a`, for every state.
- `ws1_state_count` — the micro world has 512 states (`Fintype.card G = 512`), computed structurally, giving the loss its scale.

Workstream 2, the loss, counted:
- `ws2_summary_lossy` — two distinct microstates with the same summary (the one-edge pair).
- `ws2_fiber_multiple` — a single summary with at least three distinct microstates in its fiber (one edge forward, one edge back, both), so the loss is counted on a named fiber, not asserted.
- `ws2_no_decoder` — no function recovers the microstate from the summary. The projection admits no section.

Workstream 3, the arrow:
- `ws3_micro_loses_nothing` — every transport is injective: the microdynamics destroys no information. From 3.0's involution.
- `ws3_observation_always_lossy` — for every move, the composite "flow then summarize" is non-injective: no amount of further flowing repairs the loss. The proof must be structural (transport bijectivity plus the lossy pair), not a table.
- Together these are the arrow: reversible beneath, irreversible in every observation above.

Workstream 4, the bridges:
- `ws4_summary_is_p2_sym` — the summary is Program 2's symmetric relating: `summary g a b = true ↔ P2S0.sym g a b`. The reuse enters by theorem.
- `ws4_charge_erased` — the summary erases the charge: two states with the same summary and different charge. What the coarse-graining forgets is exactly the ledger's quantity — the link 3.2 inherits.

Workstream 5, the verdict:
- Outcomes: `arrow` (micro injective, observation lossy for every move, no decoder), `transparent` (the summary is injective — no loss, no arrow), `opaque` (the microdynamics itself loses — would contradict 3.0), `partial'`.
- `ws5_verdict_tied` in the tying pattern; `ws5_verdict_eq` beside it. No vacuous audits.

## Reuse

| Reused object | From | Bridge obligation |
|---|---|---|
| `G`, `transport`, involution, `charge` | `P3S0` | direct import (same program, chain) |
| `sym` (the symmetric relating) | `P2S0` | `ws4_summary_is_p2_sym` |

## Pre-registered outcomes

- **arrow** — the expected close; the design's central bet cashed.
- **transparent** — the summary loses nothing; the arrow does not emerge here. Reported as the refutation of the coarse-graining choice, and the program halts for re-chartering.
- **opaque** — a transport fails injectivity; contradicts 3.0 and would be a serious finding against it.
- **partial** — a target lands only in weakened form; disclosed.

## Build and registration

Namespace `P3S1`, sources at `program-3/series-1/formal/`. Lakefile: `[[lean_lib]] name = "P3S1"`, roots `P3S1` and `P3S1.AxiomCheck`, added to `defaultTargets`. Gate:

```
check program-3/series-1 "^import (P3S0|P3S1)(\.[A-Za-z0-9_]+)*$"
```

Universal targets structural (the step-zero lesson); `decide` for witnesses and single states only. Sorry-free, axiom-clean, house-style docstrings.
