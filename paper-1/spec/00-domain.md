# 00 — Domain: the relational arena

> *Paper one derives a self; it does not define one.* This page fixes the arena in plain language — a
> **quantaloid / allegory in which relations are the primitive arrow**, with `Q` the hyperfinite **type III₁
> factor**, chosen by the **seam** (opacity ⇒ tracelessness ⇒ type III) — **never** by asymmetry. The
> foundation that sits on it is a **single definition, no axioms** ([`02-foundation.md`](02-foundation.md)).

## The arena: relations are the primitive

The arena is a **quantaloid / allegory**. It has objects `A, B, …`, but the objects are not the point —
between any two there are **`Q`-valued relations** `R : A ⇸ B`, and **the relation is the primitive arrow**.
There is **no carrier underneath** a relation, no set of points the relation is "really" about: the relation
is the thing. This is why **relational primacy** and **"nothing below"** hold here *by construction*, not by
axiom — in the previous (traced-SMC) arena they had to be argued for via a greatest-fixed-point choice; here
there is simply nothing more basic than a relation to choose against.

The arena carries, **natively** (these are structure the quantaloid/allegory has, not things we posit):

- **Converse** `R° : B ⇸ A` — a free involution `(R°)° = R`. It is **not** identified with `R`: a relation
  and its reverse are different arrows. (Native structure — the "other end" of every relation; the
  operator-world analogue is the modular conjugation `J`.)
- **Relational composition** `R ; S : A ⇸ C` (for `R : A ⇸ B`, `S : B ⇸ C`) — relating through, with an
  identity relation `1_A : A ⇸ A` as unit.
- **The inclusion order** `R ≤ S` with **meets and joins**, and **completeness**: arbitrary suprema exist, so
  monotone processes on relations have **fixed points** (relational Knaster–Tarski — the floor the existence
  theorem stands on).
- **The modular law** — the allegory's compatibility between composition, converse, and meet:
  `(R ; S) ∧ T ≤ R ; (S ∧ (R° ; T))`. It is what makes the order and the composition cohere into an allegory
  rather than two unrelated structures.

Attention is **not a separate object** added on top. It is the relation's own **`Q`-weight, read at each
end** — `R` bears its weight on one end, `R°` on the other. (Whether this two-endedness is *load-bearing* —
the former "co-direction" reading — is an **open question**, [`10-open-questions.md`](10-open-questions.md); it
is not assumed here.)

## The value-object `Q` — the hyperfinite type III₁ factor, chosen by the seam

The values relations take live in **`Q`**, the **hyperfinite type III₁ factor**. The justification is the
**seam / opacity**, and *only* that — never asymmetry (anchoring the arena in asymmetry would make the
dissolution of A1 circular):

- **The seam forces tracelessness.** The headline opacity result (Lawvere; [`02-foundation.md`](02-foundation.md))
  is that a self **provably cannot fully account for the relation that includes it** — its self-accounting
  **never closes**. "No complete accounting" is exactly the **defining property of a type III factor**: it has
  **no trace** (no semifinite normal "how much"). The von Neumann types make this a dichotomy — type I has
  atoms (a non-relational floor, rejected by "nothing below"); type II has no atoms *but a finite trace* (the
  accounting *can* close); **type III has no atoms and no trace** (the accounting never closes). The seam votes
  type III. **III₁** specifically is the generic, unique hyperfinite case (modular spectrum all of `ℝ₊`).
- **Tracelessness is not "no measure ever."** Quantity is recovered on the **type II∞ core** of the Takesaki
  decomposition, not from a (non-existent) global trace — see [`06-type-III-modular.md`](06-type-III-modular.md).
- **The modular flow comes for free.** A faithful normal state on `Q` generates a modular automorphism group
  `σ` (reversible time) — the substrate the interface assumes ([`07-interface.md`](07-interface.md)).

## Open joints (tested across the exploration, not assumed)

The arena was **not** asserted sound; its joints were probed:

- **The trace in the quantaloid** — *settled* **B / conditional** ([`05-trace-seam.md`](05-trace-seam.md)): the
  feedback trace `Tr` is real and `τ`-free; it connects to a measure via the dimension function under an
  orthogonality side condition. The type III move **dissolved** the residual order-vs-operator tension (no
  global trace to conflict with `Tr`).
- **Order vs. operator** — the same question; partly resolved by the type III choice, the operator-level parts
  paper-level (the mathlib gap, [`06-type-III-modular.md`](06-type-III-modular.md) Part D).
- **`Q` self-similarity** (`Q ≅ Q ⊗ M₂`, "relations all the way down") — the deepest bet, **load-bearing for the
  philosophy, not for the theorems**; left to fall out or not.

## What the arena is for

It is the self-free ground on which paper one derives a self: this arena, plus the **single definition** D1
([`02-foundation.md`](02-foundation.md)) — **no axioms** — from which the headline cluster (existence, the
seam, the arrow's irreversibility) follows `τ`-free. The next file fixes the **vocabulary** — relation,
converse, composition, order — and names **no self**.
