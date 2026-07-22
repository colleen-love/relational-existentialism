# Series 3.2 landing note

Verdict: **ledger** — computed by `ws5_verdict_tied`, every flag bound to its justifying theorem. Conservation returns as a theorem about regions, and creation is orthogonal to the flow by proof.

## Theorems

- `ws1_total_charge_zero` — the world's total ledger is closed in every state (double counting, structural).
- `ws2_region_flux` — the exact flux law: a region's ledger changes by precisely the flux terms of the exchange partners it contains, for every region and every non-degenerate move.
- `ws2_region_interior` / `ws2_region_exterior` — both partners inside, or both outside: the region's ledger is conserved.
- `ws2_boundary_flux` — one partner inside: the change equals that partner's charge change exactly.
- `ws3_flow_preserves_capacity` — the flow never changes any self's capacity, through any number of rounds.
- `ws3_orbits_are_capacity` — connectivity is exactly capacity equality: the flow's orbits are the capacity classes, fully characterized (backward direction is 3.0's connectivity theorem).
- `ws4_creation_not_flow` — capacity change (where Program 2 located creation) is provably outside the flow.
- `ws4_holonomy_not_conserved` — a transport moves Series 2.8's holonomy while the total ledger stays closed: the loop structure is the ledger's blind spot, the forward-note to the phase series.
- `ws5_verdict_tied` / `ws5_verdict_eq` — the tied verdict.

Build green, gate green, all headlines on the standard three axioms or fewer (`ws5_verdict_eq` on none), sorry-free, no `native_decide`, no vacuous audits. `transport_self` shows the flux law's `y ≠ z` hypothesis excludes only the identity move.

## Deviations and notes

None from the outline. Built in the program seat under the revised protocol; awaits the gate review.

## For the gate review to press on

- The charter's "creation at the boundary of sight or where holonomy lives" lands here as two theorems (`ws4_creation_not_flow`, `ws4_holonomy_not_conserved`); the positive account of creation events (capacity-changing moves as import-driven) is deliberately not built — the flow group excludes them by design. Check the prose claims no more than the orthogonality.
- The region laws quantify over all regions and moves; the carrier is still three selves. The gate review should weigh the scale honestly.
