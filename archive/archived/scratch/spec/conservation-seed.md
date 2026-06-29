# Conservation — the located global (paper-four seed)

> *The frontier thread, recorded so it isn't lost.* Lean: [`../formal/Conservation.lean`](../formal/Conservation.lean)
> (workbench, not gated). Unnumbered until the paper-four promotion.

## What is settled (the located global)

Decoherence **conserves** coherence — it does not destroy it, it **relocates** it into what you traced out.
In the matrix model, for a system entangled with its environment:

- the **global** state stays fully coherent (`not_isClassical_entangle`) — nothing decohered globally;
- the coherence the system "lost" sits, exactly, at the **global cross-term** `(i,i)–(j,j)` with magnitude
  `aᵢ·aⱼ` (`copyDefect_entangle_ne`) — the weight the partial trace folded into the system–environment
  correlation.

So the conserved-globally / absent-locally split is a **theorem** of the model: presence is conserved
globally and **apportioned by the trace** between the system and what it is folded into.

This is the positive face of paper three's negative: paper three's `arrow_is_loss_not_relocation` (T3.02) says
that *within* the system's own conserved ledger the arrow is **loss**, not relocation. The two are the same
fact from two cuts — relocation across the system/environment boundary reads as loss from inside the system.

## The open frontier

- **The population-transfer dissipator.** The constant-capacity generative law (`T0.07`) forbids extraction;
  genuine depletion/transfer needs a dissipator that *moves population* between branches (dynamical capacity
  `α` falling under depletion). That dissipator, and its conserved Noether quantity, is the paper-four
  engine — not yet built.
- **The Noether coincidence.** Whether the globally-conserved presence is the Noether charge of the modular
  flow's symmetry (the equilibrium one generator, `T3.01`) is the identification paper four would close.

## Coupling to resolve at promotion

`Conservation.lean` currently **imports** paper two's `Scratch.Decoherence` (the matrix decoherence model).
On the workbench this is fine. At the paper-four promotion it becomes a **prose citation** of paper two's
decoherence (or the needed lemma is hoisted to `theory/`), per the cite-don't-import convention.
