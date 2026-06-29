# 02 — The foundation: one definition, one theorem

> *What paper one actually establishes.* A **single definition** on the seam-chosen arena
> ([`00-domain.md`](00-domain.md)) — **no axioms** — and from it the headline: **self-relation generates the
> irreversibility of time.** Mechanized in [`../formal/Paper1/Arrow.lean`](../formal/Paper1/Arrow.lean).

## D1 — self-relation is the trace (the one definition)

A **self-relation** is a relation `A ⇸ A`. **Self-relation as feedback is the trace** — the relation routed
back through itself, the **diagonal**:

> **D1.** `reenter S = S ⨾ S`.

That is the whole foundation. There are **no axioms** — no asymmetry axiom, no co-direction axiom, no
self posited. (Asymmetry, co-direction, and the existence and shape of "a self" were explored separately and
are archived; see the end of this page. None is needed for the result below.)

## The theorem — self-relation is irreversible

**Self-composition loses information, so it cannot be run backward.** Concretely, on the canonical relational
model (`Q = Prop`, ordinary relations; the value-product is `∧`):

- the **identity** relation and the **swap** relation (each `a` relates to `¬a`) are **distinct**;
- yet **both self-compose to the identity** — `reenter(id) = reenter(swap) = id`. *Going out and coming back
  is standing still; the swap's direction is destroyed by squaring.*
- Therefore `reenter` is **not injective** (`Paper1.Arrow.reenter_not_injective`): a relation **cannot be
  recovered** from its self-composition. There is **no way back.**

This is the precise, intrinsic sense in which self-reference has a **direction**: a reversible flow is a
**group** (runs both ways); self-relation is a **semigroup** (forward only). The proof uses **only
`{relations, the diagonal, completeness}`** — no axioms, no self, no operator theory:

```
Paper1.Arrow.reenter_not_injective   depends on axioms: [propext, Classical.choice, Quot.sound]
```

**This is the irreversibility of time**, derived from self-relation alone.

## The honest edge — irreversibility, not orientation

The theorem establishes that there **is** a forward-only direction (irreversibility). It does **not** by
itself fix the arrow's **orientation** — *which* end is the future. That self-composition runs `S ↦ S ⨾ S` is
shown; calling that the future (rather than the past) is an extra step, and **we do not import a thermodynamic
arrow** (a low-entropy boundary, an entropy-increase postulate) to take it. So the earned claim is **"the
irreversibility of time,"** not "the arrow of time." Where the orientation *could* come from — the modular
structure's own one-sidedness (Borchers / half-sided modular inclusions) rather than an imported tiebreaker —
is the natural next question, recorded in the archived exploration.

## One structure, two faces (a reading)

Self-reference is also where **opacity** lives: a self cannot fully *trace* the relation that includes it
(Lawvere — the **seam**). The two are plausibly **one fact**: the diagonal loses information, read once as
**irreversibility** (you cannot recover `S` from `S ⨾ S` — no way back) and once as **opacity** (you cannot
fully know yourself — no way to close the account). Recorded as a **reading**, not a theorem.

## The exploration this distills

Existence of a fixed self-relation, the seam, the type III modular identification `A3 = σ ⊕ arrow`, the
assumed modular-theory interface and its assumed/constructed disclosure — the longer development that found
and surrounds this result — is preserved as structural reference (not deleted) in
[`../../archive/archived/paper-1-exploration/`](../../archive/archived/paper-1-exploration/). Paper one stands
on the single definition and the single theorem above.
