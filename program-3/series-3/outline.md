# Series 3.3 — The Phase

The first post-gate series. One question: do flow histories carry a genuine phase — path-dependent, forced within its family, and interfering?

## The objects

- Histories: lists of moves, run by folding transports; the first appearance of paths as objects (the absence Program Review 2-1 graded against Series 2.11).
- The step sign: `+1` when a move actually transports forward, `-1` backward, `0` when it idles. The winding of a history is the accumulated step sign along the evolving state.
- The phase: the parity sign on windings — now to be earned by classification, not chosen.

## Targets

Workstream 1, composition: `ws1_run_append` and `ws1_wind_append` — histories compose, and the winding is a cocycle over composition.

Workstream 2, path dependence: `ws2_winding_path_dependent` — two co-terminal histories from one state with different windings. The winding is not a function of the endpoints: the flow has genuine holonomy, the necessary condition for interference to be non-trivial.

Workstream 3, the forced sign (the missing theorem of Program Review 2-1, S-1): `ws3_sign_forced` — every composition-respecting, `±1`-valued phase on windings is either trivial or the parity sign. The sign is classified, not selected.

Workstream 4, interference on histories: `ws4_amp_canonical` (the parity sign satisfies the classification's hypotheses and is the nontrivial member); `ws4_destructive_iff` — co-terminal windings destructively interfere exactly when their difference is odd, for all windings; concrete witnesses for both poles on named co-terminal histories; and `ws4_exponent_not_forced` — every member of the `|·|^p` family respects cancellation, so the cancellation test forces the phase and provably not the exponent (Series 2.12's ceiling, restated as a theorem at this scope).

Workstream 5, the verdict: outcomes `phase` (all land), `exact'` (winding path-independent — no phase), `unforced` (the classification fails), `partial'`; tied verdict.

## Reuse

`P3S2` at the boundary (reaching `P3S1`'s witnesses and `P3S0`'s transports); no re-seats.

## Pre-registered outcomes

`phase` expected; `exact'` would refute the winding's design (a state function, not a connection); `unforced` would leave the sign a choice as in Program 2; `partial'` disclosed.

## Build

Namespace `P3S3`, gate `check program-3/series-3 "^import (P3S2|P3S3)…"`, registered roots `P3S3` / `P3S3.AxiomCheck`. Universal targets structural; `decide` for concrete histories and states only.
