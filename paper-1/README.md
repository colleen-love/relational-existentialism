# paper-1 — self-relation generates the irreversibility of time

> **The result, in one line.** A relation that refers to itself — **self-relation, the diagonal**
> `reenter S = S ⨾ S` — is **irreversible**: it loses information, so it cannot be run backward. That
> one-way-ness *is* the irreversibility of time, and it falls out of **a single definition on a seam-chosen
> arena, with no axioms.**

## The whole paper, in four pages

1. [`spec/00-domain.md`](spec/00-domain.md) — **the arena.** A quantaloid/allegory where relations are
   primitive (no carrier underneath), with the value-object the hyperfinite **type III₁ factor**, chosen by
   the **seam** (a self whose accounting never closes ⇒ no trace ⇒ type III) — never by asymmetry.
2. [`spec/01-signature.md`](spec/01-signature.md) — **the vocabulary.** Relation, converse, composition,
   order. **No self is named** — the self is what the diagonal turns out to be, not a primitive.
3. [`spec/02-foundation.md`](spec/02-foundation.md) — **the one definition and the one theorem.**
   **D1:** self-relation is the trace, the diagonal `reenter S = S ⨾ S`. **There are no axioms.** From it:
   **self-relation is irreversible** (`reenter` is non-injective — a relation cannot be recovered from its
   self-composition; a semigroup, not a group). Mechanized, `τ`-free.
4. **The proof** — [`formal/Paper1/Arrow.lean`](formal/Paper1/Arrow.lean) (the theorem) on
   [`formal/Paper1/Arena.lean`](formal/Paper1/Arena.lean) (the arena). Two files, `lake build` green.

```
Paper1.Arrow.reenter_not_injective   —   self-relation is irreversible
   depends on axioms: [propext, Classical.choice, Quot.sound]   (no custom axioms, no self, no operator theory)
```

## What is claimed — and what is not

- **Claimed (proved):** self-relation creates the arrow's **irreversibility** — that there is a forward-only
  direction, intrinsic to self-reference, below any notion of "a self."
- **Not claimed:** the arrow's **orientation** (which way is the future). That self-composition runs forward
  is shown; *which* end we call the future is **not** fixed by self-reference alone, and we do **not** import a
  thermodynamic arrow to decide it. We say "the irreversibility of time," **not** "the arrow of time." (The
  honest edge is spelled out in [`spec/02-foundation.md`](spec/02-foundation.md).)

## The full exploration (archived)

This focused result was found by a longer exploration — existence of a fixed self, the seam (Lawvere), the
type III modular identification `A3 = σ ⊕ arrow`, the assumed modular-theory interface and its disclosure.
That work is preserved as structural reference, not deleted, in
[`../archive/archived/paper-1-exploration/`](../archive/archived/paper-1-exploration/) (see its
[`README.md`](../archive/archived/paper-1-exploration/README.md)). Paper one itself stands on the single
theorem above.
