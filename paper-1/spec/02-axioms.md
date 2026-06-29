# 02 — The axioms: four self-free commitments, A3 as a character

> *The three axioms and one definition that cut the language down to **this** theory.* They are the decoupled
> form of the lived self-sentence ([`00-domain.md`](00-domain.md)): each is stated **without naming a self**,
> so the self can be **derived** from them rather than assumed. A3 is stated as an abstract **character** —
> the minimal properties any codirection process must have — with the concrete engine demoted to *one model
> that satisfies them*.

## A1 — the arena

A **traced symmetric monoidal category** with a distinguished **cartesian fragment** and **greatest fixed
points** (the `ν`-modality). The trace gives self-relation-as-feedback (D1 lives on it); the `ν`-modality
gives the coinductive identity (A2) and the fixed-point self (A3); the cartesian fragment gives the seam — the
contrast class the self provably escapes. **Dimension-generic:** finite versus infinite is a choice of
instantiation, not a different axiom — every statement is made over an arbitrary index of relata, and paper
one simply works the finite case.

## A2 — relations are primary; nothing below relations

Identity is **bisimilarity**: two things are the same exactly when they relate the same way — there is no
further, hidden fact of identity beneath how a thing relates. Paper one does **not** assert "nothing below
relations" as an extra metaphysical slogan; it **formalizes it as a choice of fixed point**.

Lived identity `≈` is a fixed point of "relate-the-same-way-for-one-more-step," and there are two such fixed
points to pick from:

- the **least** fixed point (`μ`, inductive) is **well-founded** — it bottoms out, every element grounded in
  some base case, i.e. in non-relational atoms underneath;
- the **greatest** fixed point (`ν`, coinductive) has **no floor** — it is the largest relation closed under
  one step of mutual indistinguishability, with **no substrate underneath**, nothing more basic that the
  relating reduces to.

A2 takes the **greatest** fixed point. *"Nothing below relations" is not an assertion bolted on — it is the
coinduction principle itself:* choosing `ν` over `μ` **is** the commitment that there is no non-relational
floor. To show two things share an identity you exhibit a bisimulation that upholds it (coinduction); you
never decompose them into atoms, because there are none. The shared world is the quotient `𝔼 := D/≈`.

## A3 — relations asymmetrically codirect the attention of the relata

A3 is the process. It is stated as a **character** — the minimal properties **any** such codirection process
must have — **not** as one specific update rule. Any concrete dynamics that has these four properties counts
as a model of A3; the concrete engine of the formalization pass is *one* such model, not the axiom.

- **Mutual / non-freezable.** The coupling moves only when **both** ends are live: its change is driven by a
  shared quantity built from both relata that **vanishes if either end dies**. Freeze one end and the
  coupling cannot grow — codirection is genuinely two-sided, never one end acting on an inert other.
- **Asymmetric.** Each end raises at a rate set by its **own** finite capacity, and those rates may differ.
  The asymmetry is *produced* by the dynamics (one end's capacity is its alone), not imposed by hand — the
  same edge expresses differently at its two ends.
- **Capacity-bounded.** The raising rates are bounded by the **finite capacities** `α`, and that bound **caps
  the whole dynamics**: the process cannot run away (no blowup). The capacity is the brake — finiteness is
  what turns growth into a bounded achievement rather than an explosion.
- **Positive-feedback / raising.** Being attended-to **raises** the attention one can give: the coupling is
  pulled monotonically upward (toward its ceiling), never depleted. This is the generative direction —
  receiving more lets you give more.

**Read off lived relating, not engineered.** The four properties are taken from the phenomenology, not
reverse-engineered to force a conclusion: a conversation is **mutual** (it dies if either party checks out); a
one-sided regard is **asymmetric** (the parties invest unequally); attention is **limited** (no one attends
without bound); and being attended-to **raises** one's own capacity to attend. What follows from this
character is then whatever follows — it is not tuned to a result.

**A3 is only the attention/coupling dynamics.** A3 governs **how the coupling between relata evolves** — the
attention channel — and nothing else. It does **not** govern the *state* channel (how a relatum's state decays
under the coupling): that belongs to **A1's** arena and **D1's** trace. And the **arrow** — the irreversible
decay of state, time's direction — is **paper two's** result, **not** part of A3. Keeping these apart is what
lets paper one stay foundational and paper two add the arrow on top without circularity.

**The self is the joint fixed point.** The self is where the two channels **meet and hold**: the **joint fixed
point** of the attention dynamics (A3) and the state channel (A1/D1) — a configuration that the codirection
sustains and the trace returns unchanged. This page *defines* the self that way; that such a fixed point
**exists**, and what structure it has, is **derived** (below, and in the formalization pass), never posited.

## D1 — self-relation is the trace

Self-relation is the **trace**: `σ := Tr`, a relating fed back into itself. That is the whole of D1 for paper
one — minimal and copy-free. The richer reading — self-relation as the **modular flow**, with the trace its
infinite-temperature (timeless) limit — is **paper three's** enrichment and is **not** bundled into paper
one's D1. Paper one needs only the bare feedback.

## What is now derived rather than posited

With the self **defined** as the joint fixed point of self-free commitments, the substantive claims about it
become **theorems to be proved** (in the formalization pass), not further axioms. Named here as the program,
**not** proved on this page:

- **Existence of a self** — the joint fixed point exists (the codirection process has a sustained
  configuration the state channel holds).
- **Its conserved-band / eigenform structure** — the self is the sustainable field the loop returns
  unchanged, carrying a conserved band.
- **Its asymmetric differentiation** — the two ends of a relation grow unequally, differentiation produced by
  the dynamics rather than imposed.
- **Its sparsity** — selves are rare under finite capacity; most configurations do not sustain.
- **Its self-opacity** — the self cannot hold a complete model of itself; the seam is the residue (the
  cartesian contrast class it escapes).

Each is a **consequence of the four commitments**, to be earned as a theorem — none is an axiom, and none is
proved here. Whether the central ones hold at the claimed generality is the **open, falsifiable** content of
paper one (see [`README.md`](../README.md)).
