# Paper two — the modular self-relation paper (scope)

> **Status: scoped, not yet forked.** `paper-2/formal/` is empty: the **modular slice** is forked from
> `theory/` when paper two is built (lazy fork-and-freeze). It forks the modular slice only — **not** the
> A2-priority or A3-generative work, which serve the conservation and sparsity papers — so "not relevant to
> paper two" is enforced by the fork, not by judgment.

## Headline (proved-now)

*Self-relation is modular flow; the trace is its infinite-temperature limit, and time's arrow is the
dissipative complement the flow cannot supply.* Thermal-time positioning is the contribution; the
conservation law and the single-generator coherence are the frontier.

The mechanization already exists in [`theory/formal/Theory/ModularFlow.lean`](../../theory/formal/Theory/ModularFlow.lean)
(handoff X, `sorry`-free), with scope in [`theory/spec/modular-frontier.md`](../../theory/spec/modular-frontier.md)
and the mathlib-gap audit in [`theory/spec/modular-mathlib-audit.md`](../../theory/spec/modular-mathlib-audit.md).

## Structure

1. **Trace → modular flow**, the modular Hamiltonian as Stone generator `[proved]`
   (`modPow_mul`, `modularHamiltonian`, `modPow_eq_generator`).
2. **Lead here — the trace is infinite-temperature time** (`modularFlow_maximally_mixed`): the clean bridge,
   and the retroactive justification of paper one's choice `[proved]`.
3. **Energy = `spec(K)`, Gibbs/KMS** `[proved]` (`modularEnergy`, `gibbs_kms`).
4. **The arrow boundary** (`modular_reversible`: the flow is reversible, hence carries time's *flow* not its
   *arrow*; the arrow is the dissipative complement, sourced from the seam; "two faces of one generator" is
   the frontier, at honest strength). `[proved that flow is reversible; one-generator coherence open]`.
5. **Positioning** vs thermal time (Connes–Rovelli) + named frontiers (single generator, conservation law,
   type III — the last scoped in `modular-frontier.md`).

## Reading to flag, not assert

Trace / infinite-temperature ↔ *universe* (atemporal); a definite state with nontrivial modular flow ↔
*cosmos* (temporal). A candidate operator-algebra backbone for the conservation paper. Keep `[reading]`.

## The decision (open)

Ship the modular paper **as scoped** (all proved, a real contribution) and let conservation be the next
paper; *or* make paper two the conservation law (needs the single-generator coherence + a relocation law
proved, and pulls in the A2-priority fork). **Recommendation:** ship what's proved, name the frontier, lead
with the trace bridge — and cite paper one's arrow result rather than importing it.

## Dependency on paper one

Paper two depends **fundamentally** on the theory paper one is built from, and on paper one's headline (the
arrow) as a **cited** prior result — its flow/arrow division of labor leans on it. That dependency is honored
in prose and through the shared `theory/`/`foundation/` layers, **never** by a `paper-2 → paper-1` import
(see [`../../STRUCTURE.md`](../../STRUCTURE.md)). If a `paper-1/` result is found to be needed here, it is
hoisted to `theory/` and forked into both papers — never imported across.
