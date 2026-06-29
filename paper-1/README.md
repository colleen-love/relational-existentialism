# paper-1 — a self arises from the axioms

**The thesis: a self is *derived*, not defined.** Paper one is the foundational paper of the second cycle. It
takes a single lived datum — *I am a collection of relations that asymmetrically codirect my attention* —
and shows that the **self** in that sentence need not be assumed: it **condenses out**, as a fixed point, of
commitments that never mention a self.

**The arc, in one line.** Take the lived self-level sentence; **decouple** it into three self-free commitments
plus a minimal definition — an arena (**A1**), relations-first (**A2**), the codirection process (**A3**),
and self-relation-as-feedback (**D1**); define the self as the **joint fixed point** where the attention
process and the state channel meet; and **recover the lived description as a theorem** about that fixed point.
The decoupling is what makes this non-circular: *you cannot derive a self from a description that already
contains one*, so the unified self-level sentence has to be the output, never the input.

## The plan (plain-language spec)

- [`spec/00-domain.md`](spec/00-domain.md) — the arena (A1) and the decoupling that lets a self be derived.
- [`spec/01-signature.md`](spec/01-signature.md) — the vocabulary, with the self deliberately left undefined
  (the smuggled `self := νΦ_c` is removed; there is **one** codirected attention operator, not two).
- [`spec/02-axioms.md`](spec/02-axioms.md) — the four commitments, with **A3 stated as an abstract
  four-property character** (mutual, asymmetric, capacity-bounded, raising) and the concrete engine demoted
  to one model that satisfies it; A2 formalized as the **greatest-fixed-point** (`ν`-over-`μ`) choice; D1
  kept minimal.
- [`spec/04-provenance.md`](spec/04-provenance.md) — provenance + the canonical-axiom pin.

The canonical axioms it builds on: [`../theory/spec/AXIOMS.md`](../theory/spec/AXIOMS.md) (`Theory.Axioms`).

## Status — skeleton, and an honest open program

**This is prose, not yet proof.** `formal/` is an empty `Paper1` root; the theorems (`T1.<n>`) are deferred to
the **formalization pass**, where A3's four-property character becomes a typeclass with the engine as a
witnessing instance, and the derived results are mechanized. What the spec commits us to deriving — existence
of a self, its conserved-band / eigenform structure, its asymmetric differentiation, its sparsity, and its
self-opacity — is named as the **program**, not claimed as done.

**The central structural questions are open and falsifiable**, stated as such, not overclaimed:

- **Is the symmetric configuration unstable** — does codirection genuinely *break* symmetry, so the
  asymmetric self is forced rather than merely allowed?
- **Is the self necessarily sparse** — does finite capacity *force* selves to be rare, or only permit it?

These are the program, not yet the result. Paper one earns the right to ask them by deriving the self in the
first place; settling them is the work that follows.

## Where it sits

The foundational paper the others build on:

- **paper-1** — *a self arises* (this paper).
- [`paper-2`](../paper-2) — the self **in time**: the arrow, energy, the seam.
- [`paper-3`](../paper-3) — the self's **modular / thermal** structure (the trace as the timeless limit of
  modular flow).
- **paper-4** — **conservation / presence**, the living frontier in [`scratch/`](../scratch).

See [`../STRUCTURE.md`](../STRUCTURE.md) for the layout discipline and [`../theory/spec/NODES.md`](../theory/spec/NODES.md)
for the proof-DAG node inventory.
