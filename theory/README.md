# theory — the living frontier

The theory-specific development already *beyond* paper one: the modular reading of A1, the generative A3, the
A2-priority work, the equilibrium one generator, and the einselection principle + presence. Lean namespace
`Theory.*` (sources in [`formal/`](formal), prose in [`spec/`](spec)). Imports only `theory/` +
`foundation/`; references no paper. The only root that moves freely — papers **fork a frozen copy** of the
slice they need. See [`../STRUCTURE.md`](../STRUCTURE.md).

## The canonical axioms (handoff XX)

`theory/` is also the **legible canonical home of the one shared axiomatization** `{A1, A2, A3, D1}`. Handoff
XX reframed **A3 as a process** — *relations co-direct attention asymmetrically in the relata* — and **derived**
the per-paper readings of the self (eigenform, generative, modular) as theorems of that one process. The
result is a single **stable, version-pinned** axiom layer the three papers share, not per-paper forks.

- **For an outside reader:** [`spec/AXIOMS.md`](spec/AXIOMS.md) — the four axioms stated plainly, each with its
  derived per-paper consequences.
- **The mechanization:** [`formal/Theory/Axioms.lean`](formal/Theory/Axioms.lean) (`Theory.Axioms`,
  `sorry`-free). Provenance and the reversal of spec XIII's freeze: [`spec/PROVENANCE.md`](spec/PROVENANCE.md).
