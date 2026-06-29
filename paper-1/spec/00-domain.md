# 00 — Domain: the arena, and the decoupling that lets a self be derived

> *Paper one's thesis is that **a self arises from the axioms** — it is derived, not defined.* This page
> fixes the arena (A1) in plain language, and states the move the whole paper turns on: the **decoupling**
> of the lived self into self-free commitments, so that the self can be recovered as a theorem rather than
> assumed as a primitive.

## The lived datum, and why it must be taken apart

The datum paper one starts from is one sentence, stated at the level of the self:

> *I am a collection of relations that asymmetrically codirect my attention.*

That sentence is true to the experience, but it is **fused** — it already names a self, and inside that one
self-level description it bundles three different commitments: that there is an **arena** of things-in-relation
at all (A1), that those relations are **primary**, with identity nothing but how a thing relates (A2), and
that relation is a **process** that codirects attention asymmetrically (A3). If we kept the sentence whole and
wrote it down as our axiom, we would have *posited* the self — and then any "derivation" of the self would be
circular, recovering only what we had already put in.

So paper one **decouples** it. It commits to the three pieces **separately**, and in a form where **none of
them mentions a self**: an arena (this page), relations-first (A2), and the attention process (A3) — plus the
minimal definition that self-relation is feedback (D1). The claim of the paper is then that the self
**condenses out** of those self-free commitments as a **fixed point**, and that the fused lived sentence is
*recovered* — as a theorem about that fixed point, not as an input.

**This decoupling is not bookkeeping.** It is exactly what makes the derivation non-circular: you cannot
derive a self from a description that already contains one. The unified, self-level sentence is the **output
the paper earns back**, never the premise it starts from.

## A1 — the arena, in plain language

The arena is a world of **systems** (relata) and the **relatings** between them, set up so that you can only
ever speak of a thing **through** its relatings. Formally it is a category: objects are system-types — the
kinds of thing that can stand in relation — and morphisms `f : A → B` are *relatings*, a relating of `A` to
`B`, composing associatively (`g ∘ f` is "relating through" an intermediary). The category is **symmetric
monoidal**: a tensor `A ⊗ B` reads as *`A` and `B` coexisting* in parallel, with no implied communication
(communication is a separate morphism), order-indifferent (`A ⊗ B` and `B ⊗ A` agree up to the symmetry).

The governing discipline is **Yoneda**: in a category you cannot pick out an object except by its pattern of
morphisms into and out of it. An object's identity *is* its relatings. So in the arena, **morphisms are the
data and objects are bookkeeping** — the relating comes first, the thing-related is whatever its relatings
determine. We do **not** start from "selves with relations attached"; we start from relatings, and let selves
appear later, as fixed points.

## The three structural ingredients, and what each one buys

The arena is not generic. It carries exactly three extra pieces of structure, and each is load-bearing for a
specific commitment downstream — none is ornament.

- **The trace** — *self-relation as feedback.* A trace feeds an output wire back into an input wire: it turns
  a relating into a **loop**, a relating returned to itself. This is the formal content of self-relation, and
  it is what **D1** lives on (`σ := Tr`). Crucially the trace needs **no copying** — it is definable even in
  the quantum (compact-closed) fragment — so self-relation-as-feedback survives where self-relation-as-mirror
  cannot.

- **Greatest fixed points** (the `ν`-modality) — *coinductive identity, and the fixed-point self.* For the
  processes we care about, the arena provides their **greatest** fixed points (final coalgebras), where the
  inhabitants are *ongoing behaviors* rather than static data — a self is maintained, not given. This buys
  two things at once: **A2's** lived identity (the greatest bisimulation — two things the same iff they relate
  the same way) and **A3's** self (the greatest sustainable field of codirected attention). Both are `ν`, and
  the choice of the *greatest* fixed point over the least is itself a commitment — see
  [`02-axioms.md`](02-axioms.md).

- **The cartesian fragment** — *the seam, load-bearing precisely because it fails.* A distinguished fragment
  of the arena has **copying** (a natural diagonal `Δ : A → A × A`) and **deleting**. This is the fragment in
  which a self could try to hold a complete model of itself — and the one in which, by Lawvere's diagonal
  argument, it provably **cannot**: any total self-copy leaves a residue it omits. That residue is the
  **seam**. The cartesian fragment is the **contrast class the self escapes**: *you cannot copy a self*, and
  the seam is load-bearing not as a structure the self inhabits but as the structure it provably **fails** to
  be reduced to. (Paper two takes the seam up as the un-decohereable floor that orders the arrow; here it is
  named as the contrast the derivation needs.)

## Dimension is an instantiation, not part of the arena

The arena is stated over an **arbitrary** index of relata: finite or infinite is a choice of *instantiation*,
not a different axiom. Paper one works the finite case; the infinite/general case is the same A1 instantiated
(see A1 in [`02-axioms.md`](02-axioms.md)).

The next file fixes the **signature** — the vocabulary this arena is described in, including attention as
codirected structure — and is careful to fix only the *language*, never to name the self.
