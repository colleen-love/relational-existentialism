# Series 3.3 landing note

Verdict: **phase** — computed by `ws5_verdict_tied`, every flag bound to its justifying theorem.

## Theorems

- `ws1_run_append` / `ws1_wind_append` — histories compose; the winding is a cocycle over composition. Paths exist as objects for the first time in either program.
- `ws2_winding_path_dependent` — two co-terminal histories from one state with windings 1 and 2: genuine holonomy; the phase reads the path, not the endpoints. `ws2_windings_both_parities` adds a co-terminal winding-3 history.
- `ws3_sign_forced` — the theorem Program Review 2-1 found missing (finding S-1): every composition-respecting, ±1-valued phase on windings is trivial or the parity sign. The sign is classified, not chosen.
- `ws4_amp_canonical` — the parity sign satisfies the classification's hypotheses and is the nontrivial member.
- `ws4_destructive_iff` — co-terminal windings destructively interfere exactly when their difference is odd, for all windings.
- `ws4_interference_on_histories` — both poles witnessed on named co-terminal histories.
- `ws4_exponent_not_forced` — every `|·|^p` (p ≥ 1) vanishes exactly at cancellation: the test forces the phase, provably not the exponent. Series 2.12's ceiling as a theorem.
- `ws5_verdict_tied` / `ws5_verdict_eq`.

Build green, gate green, standard-three axioms or fewer (`ws5_verdict_eq` on none), sorry-free, no vacuous audits.

## For the end-of-arc review to press on

- The winding's step-sign is defined per move; check the docstrings claim path-dependence only for this winding, not for every conceivable one.
- The classification is over ±1-valued composition-respecting phases; richer phase groups (beyond ±1) are not classified here — the honest scope is rebit-plus-forcing, one step past Program 2, not the full complex phase.
