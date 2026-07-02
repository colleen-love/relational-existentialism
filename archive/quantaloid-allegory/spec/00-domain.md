# 00 — The arena

> *Paper one stands on a single definition on this arena.* The arena is a **quantaloid / allegory in which
> relations are the primitive arrow**, with the value-object the hyperfinite **type III₁ factor** — chosen by
> the **seam**, never by asymmetry.

## Relations are the primitive

The arena has objects `A, B, …`, but the objects are not the point — between any two there are **`Q`-valued
relations** `R : A ⇸ B`, and **the relation is the primitive arrow**. There is **no carrier underneath** a
relation, no set of points it is "really" about: the relation is the thing. "Relational primacy" and "nothing
below" therefore hold **by construction**, not by axiom — there is simply nothing more basic than a relation.

It carries, natively:

- **Converse** `R°` — a free involution `(R°)° = R`, **not** identified with `R` (the "other end" of a
  relation; the operator analogue is the modular conjugation `J`).
- **Composition** `R ⨾ S` — relating through, with an identity relation as unit.
- **The inclusion order** with meets, joins, and **completeness** (arbitrary suprema exist).

A **self-relation** is a relation `A ⇸ A`. Its **re-entry through the trace** — the diagonal,
`reenter S = S ⨾ S` — is the one definition the paper turns on ([`02-foundation.md`](02-foundation.md)).

## The value-object `Q` — the type III₁ factor, chosen by the seam

`Q` is the hyperfinite **type III₁ factor**, and the justification is the **seam / opacity** — *only* that
(anchoring the arena in asymmetry would be circular):

- A self **provably cannot fully account for the relation that includes it** (Lawvere) — its self-accounting
  **never closes**. "No complete accounting" is the **defining property of a type III factor**: it has **no
  trace** (no semifinite "how much"). The von Neumann types make this a dichotomy — type I has atoms (a
  non-relational floor, rejected by "nothing below"); type II has no atoms *but a finite trace* (the
  accounting *can* close); **type III has no atoms and no trace** (it never closes). The seam votes type III.
- **III₁** specifically is the generic, unique hyperfinite case (modular spectrum all of `ℝ₊`).
- A faithful normal state on `Q` generates a **modular flow** `σ` — reversible time. The headline below needs
  none of this operator structure; it is recorded because it is where *time* (the reversible flow) lives, so
  that the *arrow* (the irreversible diagonal) can be seen as its complement.

## The arena is kept abstract

The mechanized development ([`../formal/Paper1/Arena.lean`](../formal/Paper1/Arena.lean)) fixes the arena over
an **abstract** `Q` (a complete lattice with a value-product), and the headline theorem is witnessed on the
cleanest concrete model, `Q = Prop` (ordinary relations). The full operator-theoretic justification of "`Q` =
the type III₁ factor" is part of the archived exploration
([`../../archive/archived/paper-1-exploration/`](../../archive/archived/paper-1-exploration/)); paper one's
result needs only `{relations, the diagonal, completeness}`.

The next file fixes the **vocabulary**; it names **no self**.
