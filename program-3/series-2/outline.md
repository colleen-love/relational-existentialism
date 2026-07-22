# Series 3.2 — The Ledger

The third series of the core. One question: does conservation return as a theorem about closed regions — a self-relative ledger with an exact flux law — with creation orthogonal to the flow?

## The objects

- Series 3.0's state space, transports, charge, capacity, and connectivity, imported through the chain (`P3S1` at the boundary, reaching `P3S0` transitively).
- The region: any set of selves `r : Finset (Fin 3)`; the region's ledger `regionCharge g r`, the sum of its members' charges.

## Targets

Workstream 1, the closed ledger:
- `ws1_total_charge_zero` — the whole world's ledger is identically zero: the sum of all charges vanishes in every state, by double counting (every unit of attention given is a unit received). Structural.

Workstream 2, the region laws (the heart):
- `ws2_region_flux` — the exact flux law: under any transport, a region's ledger changes by precisely the flux terms of the exchange partners it contains, and by nothing else.
- `ws2_region_interior` — both partners inside: the region's ledger is conserved.
- `ws2_region_exterior` — both partners outside: conserved.
- `ws2_boundary_flux` — one partner inside: the change equals that partner's charge change exactly. Conservation is local and relative to the region; it fails only at the boundary, and there by an exact accounting.

Workstream 3, the orbits:
- `ws3_flow_preserves_capacity` — the flow never changes any self's capacity, through any number of rounds.
- `ws3_orbits_are_capacity` — connectivity is exactly capacity equality: the flow's orbits are the capacity classes. One direction is 3.0's connectivity theorem; the other is the preservation above.

Workstream 4, creation orthogonal:
- `ws4_creation_not_flow` — any change of capacity (the attention-expansion where Program 2 located creation) is provably outside the flow: capacity-differing states are never connected.
- `ws4_holonomy_not_conserved` — a witness that the flow can move Series 2.8's holonomy while the ledger's totals stay closed: the loop structure is a finer quantity than the charges, the residual freedom where interference lived. A forward-note theorem to the phase series.

Workstream 5, the verdict:
- Outcomes: `ledger` (all land), `unbalanced` (the total is not closed), `porous` (a region law fails), `partial'`.
- `ws5_verdict_tied` in the tying pattern; `ws5_verdict_eq` beside it. No vacuous audits.

## Reuse

| Reused object | From | Bridge obligation |
|---|---|---|
| charge, capacity, transports, `Connected`, `ws4_flow_connects` | `P3S0` (via `P3S1`) | direct import (same program, chain) |
| `hol` (the holonomy) | `P2S8` | used in a witness theorem, reached transitively; no re-seat |

## Pre-registered outcomes

- **ledger** — the expected close: a closed global ledger, exact regional flux, orbits equal to capacity classes, creation orthogonal.
- **unbalanced** — the total charge is not identically zero; would refute the charge's design.
- **porous** — a region's ledger can change without a boundary crossing; would refute the locality of the exchange.
- **partial** — a target lands only in weakened form; disclosed.

## Build and registration

Namespace `P3S2`, sources at `program-3/series-2/formal/`. Registered in the lakefile (roots `P3S2`, `P3S2.AxiomCheck`) and the gate:

```
check program-3/series-2 "^import (P3S1|P3S2)(\.[A-Za-z0-9_]+)*$"
```

Universal targets structural; `decide` for witnesses and single states only. Sorry-free, axiom-clean, house-style docstrings. The flux law takes `y ≠ z` (the degenerate move is the identity, `transport_self`); this is stated, not hidden.
