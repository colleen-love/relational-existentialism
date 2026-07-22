# Series 3.0 — The Flow

The ground of Program 3. One question: does a reversible, capacity-conserving, charge-exchanging flow dynamics exist on the whole state space of attention graphs?

## Step zero result

The scratch de-risk (`program-3/spec/derisk/Derisk.lean`, self-contained, compiled by hand) passed all three checks over the full 512-state space:

1. the transport moves (a self moves one unit of attention between two targets) are involutions, hence bijections, on the whole space;
2. every transport conserves each self's attention capacity, and moves signed charge zero-sum between exactly the two exchange partners;
3. the direction-erasing summary is lossy, and the macro-step reads the erased microstate (the seed of 3.1's arrow).

The design exists. This series builds it properly.

## The objects

- The state space: `G := Fin 3 → Finset (Fin 3)`, taken whole. There is no witness carrier; the universe of the series is all 512 states, and universal quantifiers range over all of it.
- The move: `transport x y z : G → G` — if `x` attends `y` and not `z`, the attention moves to `z`; in the mirror case it moves back; otherwise identity. The de-risk file has a working definition the executor may reuse or improve.
- The capacity: `capacity g x := (g x).card` — attention given.
- The charge: `charge g x` — attention given minus attention received, the sum over targets of Series 2.8's signed increment.
- The reachability: a computable closure of the transport moves (fuel-based, the `P2S9.reachN` shape), defining when the flow connects two states.

## Targets

Workstream 1, the ground:
- `ws1_moves_reversible` — every transport is an involution on `G`. Quantified over all moves and all states.
- `ws1_move_local` — a transport changes only the moving self's row, and acts only when the swap precondition holds: the generator is a function of the attention alone, with no free parameter.

Workstream 2, conservation:
- `ws2_capacity_conserved` — every transport preserves every self's capacity.
- `ws2_exchange_zero_sum` — under any transport, every self other than the two exchange partners keeps its charge, and the partners' total is unchanged.
- `ws2_charge_is_incr_sum` — the bridge: `charge g x` equals the sum over `y` of `P2S8.incr g x y`. This is the reuse of Program 2's signed increment, entering by theorem, not prose.

Workstream 3, non-degeneracy (the witness discipline, discharged inside the flow world):
- `ws3_wall_is_a_state` — the two-sided wall carrier of Program Review 2-1 (`PR2R1.attV`: a leaf and two loops) is literally a state of `G`, and the review's three wall facts hold there: plain bisimilarity not total, a non-constant recoverable label, a non-constant import. Enters by bridge to the `PR2R1` theorems.
- `ws3_wall_reachable` — the wall state is connected by transports to other states of its capacity class: the non-degenerate world is not an isolated exhibit but a place the flow passes through.

Workstream 4, connectivity:
- `ws4_flow_connects` — any two states with the same capacity vector are connected by transports. Suggested route: prove it row-wise (transports on one row connect any two equal-size target sets, by cases on the size; then compose across rows), not by a whole-space `decide`, which is likely infeasible in the kernel. If only a weaker form lands (connectivity within named classes), that is the pre-registered partial outcome, stated as such.

Workstream 5, the verdict:
- Outcome type: `flowing` (all targets land), `rigid` (a move fails bijectivity — the design refuted at the ground), `leaky` (conservation fails), `partial'` (connectivity or non-degeneracy lands only in witnessed form).
- `ws5_verdict_tied` — the verdict computed through flags bound to their justifying propositions by equivalence hypotheses, the `PR2R1` tying pattern. No literal booleans standing in for theorems.
- One audit theorem at most, and only if it has content. No `True := trivial`.

## Reuse

| Reused object | From | Bridge obligation |
|---|---|---|
| `incr` (signed increment) | `P2S8` | `ws2_charge_is_incr_sum` |
| the two-sided wall (`attV`, its three theorems) | `PR2R1` | `ws3_wall_is_a_state` |
| fuel-closure reachability shape | `P2S9` (pattern only) | none — a fresh definition, named as fresh |

## Pre-registered outcomes

- **flowing** — the expected close: all five workstreams land at full strength.
- **rigid** — some move is not a bijection. Refutes the ground; the program's charter is revised, not worked around.
- **leaky** — capacity or zero-sum exchange fails. Same consequence.
- **partial** — ws4 or ws3 lands only in witnessed form; honest, disclosed, and the gate review weighs it.

## Build and registration

Namespace `P3S0`, sources at `program-3/series-0/formal/`. Register in `lake/lakefile.toml` (`[[lean_lib]] name = "P3S0"`, roots `P3S0` and `P3S0.AxiomCheck`, added to `defaultTargets`) and in `scripts/gate.sh`:

```
check program-3/series-0 "^import (PR2R1|P3S0)(\.[A-Za-z0-9_]+)*$"
```

`PR2R1` reaches `P2S8` and the rest of the built arc transitively; nothing else is imported directly. Sorry-free, axiom-clean on Mathlib's standard three or fewer, no `native_decide`, no custom axioms. Docstrings in the house style: plain statements, no all-caps emphasis, interpretation never exceeding the theorem.

## Disciplines checklist (charter law; the series review will check each)

1. Non-degenerate carrier — discharged by ws3 inside the state space.
2. Derived quantities — capacity and charge are computed from the state, never painted; any `decide` runs over the whole space or is labeled a consistency check.
3. Tied verdict — `ws5_verdict_tied`; no meta-flags.
4. Bridges — the two reuse rows above.
5. No vacuous audits.
6. Prose matches Lean.
