# 00 — Domain: the relational arena

> *Paper one derives a self; it does not define one.* This page fixes the arena in plain language — a
> **quantaloid / allegory in which relations are the primitive arrow** — and flags the three **open seams**
> the arena rests on, to be tested by the exploration ([`03-theorem-debt.md`](03-theorem-debt.md)), not
> assumed.

## The arena: relations are the primitive

The arena is a **quantaloid / allegory**. It has objects `A, B, …`, but the objects are not the point —
between any two there are **`Q`-valued relations** `R : A ⇸ B`, and **the relation is the primitive arrow**.
There is **no carrier underneath** a relation, no set of points the relation is "really" about: the relation
is the thing. This is why **relational primacy** and **"nothing below"** hold here *by construction*, not by
axiom — in the previous (traced-SMC) arena they had to be argued for via a greatest-fixed-point choice; here
there is simply nothing more basic than a relation to choose against.

The arena carries, **natively** (these are structure the quantaloid/allegory has, not things we posit):

- **Converse** `R° : B ⇸ A` — a free involution `(R°)° = R`. It is **not** identified with `R`: a relation
  and its reverse are different arrows. (This is what lets asymmetry be stated — A1.)
- **Relational composition** `R ; S : A ⇸ C` (for `R : A ⇸ B`, `S : B ⇸ C`) — relating through, with an
  identity relation `1_A : A ⇸ A` as unit.
- **The inclusion order** `R ≤ S` with **meets and joins**, and **completeness**: arbitrary suprema exist, so
  monotone processes on relations have **fixed points** (relational Knaster–Tarski — the floor the existence
  theorem stands on).
- **The modular law** — the allegory's compatibility between composition, converse, and meet:
  `(R ; S) ∧ T ≤ R ; (S ∧ (R° ; T))`. It is what makes the order and the composition cohere into an allegory
  rather than two unrelated structures.

Attention is **not a separate object** added on top. It is the relation's own **`Q`-weight, read at each
end** — `R` bears its weight on one end, `R°` on the other. Two-endedness *is* co-direction (A2); there is no
field of attention over the relata and no agent who "has" it.

## The value-object `Q` — the hyperfinite II₁ factor

The values relations take live in **`Q`**, chosen to be the **hyperfinite II₁ factor**. Two reasons, and one
honest caveat:

- **Self-similarity, made honest.** The II₁ factor is **self-similar**: `Q ≅ Q ⊗ M₂` (matrix amplification
  leaves it unchanged) — "relations all the way down," a relation that contains a scaled copy of the whole
  relational world. This is what lets *"nothing below"* be a structural fact about the value-object, not a
  slogan.
- **A native trace and modular flow.** The II₁ factor carries a **canonical (finite) trace** and a **modular
  flow** intrinsically. That is the bridge to the archived operator work: D1's self-relation-as-trace, and
  the later modular/thermal material (papers two–four), have a home in `Q` without bolting on extra
  structure.
- **Caveat (a seam, below).** That `Q` *is* the II₁ factor, and that its operator structure genuinely matches
  the order/relational structure, is a **bet** — load-bearing for the philosophy, not (yet) for the
  theorems. The exploration treats it as open.

## The three arena seams — open, to be tested

The arena is not asserted to be sound; three joints are **open**, flagged here and probed by the exploration.
They are confined to paper one (the archived downstream papers do not depend on them).

1. **The trace in the quantaloid.** Does the arena carry the **traced / feedback** structure D1 needs
   *natively*, or does it need an added condition, or does it **fight** the quantaloid structure? If it
   fights, the arena itself reshapes — this is the **highest-priority** seam. *(Settled to **B / conditional**
   in [`05-trace-seam.md`](05-trace-seam.md): the feedback trace `Tr` is real and `τ`-free; it connects to the
   factor trace `τ` via the dimension function under an orthogonality side condition — with a residual tension
   that ties into seam 2.)*
2. **Order vs. operator.** Does the relational/order structure (joins, fixed points) genuinely **match** the
   operator structure of `Q` (the II₁ factor's trace, modular flow, comparison of projections)? The two could
   come apart.
3. **`Q` self-similarity.** Is `Q ≅ Quantaloid(Q)` real, and **faithfully realized** by `R ≅ R ⊗ M₂`? This is
   the deepest bet — load-bearing for the *philosophy*, not for the theorems, so it is left to fall out or
   not rather than assumed.

## What the arena is for

It is the self-free ground on which paper one derives a self: an arena (this page), with two relations-only
axioms and one definition ([`02-axioms.md`](02-axioms.md)), from which the self **condenses out** as a fixed
relation of the co-direction dynamics. The next file fixes the **vocabulary** — relation, converse,
composition, order — and is careful to name **no self**.
