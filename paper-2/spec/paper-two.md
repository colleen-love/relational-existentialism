# Paper two — the modular self-relation paper (scope)

> **Status: scoped, not yet forked.** `paper-2/formal/` is empty: the **modular slice** is forked from
> `theory/` when paper two is built (lazy fork-and-freeze). It forks the modular slice only — **not** the
> A2-priority or A3-generative work, which serve the conservation and sparsity papers — so "not relevant to
> paper two" is enforced by the fork, not by judgment.

## Headline (proved-now)

*Self-relation is modular flow; the trace is its infinite-temperature limit, time's arrow is the
dissipative complement the flow cannot supply — and the two are **two faces of one generator**, proved at
equilibrium.* Thermal-time positioning is the contribution; the **single-generator coherence is now proved in
the equilibrium case** (`Theory.OneGenerator`), and the conservation law and the *out-of-equilibrium*
identification remain the frontier.

The mechanization already exists in [`theory/formal/Theory/ModularFlow.lean`](../../theory/formal/Theory/ModularFlow.lean)
(handoff X, `sorry`-free) and [`theory/formal/Theory/OneGenerator.lean`](../../theory/formal/Theory/OneGenerator.lean)
(handoff XV, the open-system capstone — assembles `K` from the state and `𝒟` from paper one and *checks*
their commutation), with scope in [`theory/spec/modular-frontier.md`](../../theory/spec/modular-frontier.md)
and the mathlib-gap audit in [`theory/spec/modular-mathlib-audit.md`](../../theory/spec/modular-mathlib-audit.md).

## Structure

1. **Trace → modular flow**, the modular Hamiltonian as Stone generator `[proved]`
   (`modPow_mul`, `modularHamiltonian`, `modPow_eq_generator`).
2. **Lead here — the trace is infinite-temperature time** (`modularFlow_maximally_mixed`): the clean bridge,
   and the retroactive justification of paper one's choice `[proved]`.
3. **Energy = `spec(K)`, Gibbs/KMS** `[proved]` (`modularEnergy`, `gibbs_kms`).
4. **The arrow boundary** (`modular_reversible`: the flow is reversible, hence carries time's *flow* not its
   *arrow*; the arrow is the dissipative complement, sourced from the seam). `[proved that flow is reversible]`.
5. **Two faces of one generator — proved at equilibrium** (`Theory.OneGenerator`). The modular clock (`K`
   from the state) and paper one's dissipative arrow (`𝒟 = schur μ`) assemble into a **single** GKLS
   generator `𝓛 = -i[(1/β)K, ·] + 𝒟`. The KMS bridge gives `K = β·H + (log Z)·I` (`modularHamiltonian_eq_gibbs`),
   so the unitary face is the modular flow at rate `1/β` (`commGen_modular_eq_beta`). The crux: the two
   *independently defined* pieces **commute** — derived, not imposed — from `B1 = eigenbasis(ρ)`
   (`modularFlow_diagonal_eq_schur` + `schur_comm` ⟹ `modular_dephaseFlow_commute`,
   `liouville_dephase_commute`), with the genuine modular operator `modPow_diagonal` as the anti-tautology
   anchor. The joint semigroup's law `combinedFlow_add` *consumes* this commutation. **The headline upgrades
   from "located as the unitary and dissipative parts" to "proved one generator" — at equilibrium, under the
   named alignment `B1 = eigenbasis(ρ)`.** `[proved, at equilibrium; out-of-equilibrium = Connes–Rovelli, open]`.
6. **Einselection forces the alignment; presence, derived** (`Theory.Einselection`, foundation for paper
   three). Spec XV's `B1 = eigenbasis(ρ)` is no longer assumed: it follows from the modular state being the
   dissipator's **rest-state** (`𝒟(ρ) = 0 ⟹ ρ` diagonal, `stationary_eq_diagonal_real`). The einselected
   conserved band `Peri` splits into fixed (knowing) ⊕ rotating (energy), and **presence** := its HS weight is
   *conserved* (`presence_conserved`) and *Pythagorean* (`presence² = knowing² + energy²`, `pythagorean`).
   The honest negative: the arrow is **loss, not relocation** (`arrow_is_loss_not_relocation`) — pure
   phase-damping erases the transient rather than feeding the record, so paper three's conservation law needs
   a population-transfer dissipator. `[presence: proved at equilibrium; relocation: refuted for the minimal
   generator]`.
7. **Positioning** vs thermal time (Connes–Rovelli) + named frontiers (out-of-equilibrium thermal time; the
   conservation law as a *continuity equation* with population transfer, not pure conservation; type III — the
   last scoped in `modular-frontier.md`).

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
