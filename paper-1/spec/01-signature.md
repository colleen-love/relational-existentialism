# 01 — The vocabulary

> *The arena ([`00-domain.md`](00-domain.md)) fixed the kind of structure; this fixes the **language** — and
> fixes the language only.* **It names no self.** The self is what the diagonal turns out to be
> ([`02-foundation.md`](02-foundation.md)), never a primitive — a signature that named it would posit the
> paper's conclusion.

## Sorts

- **Objects** `A, B, …` — bookkeeping only; nothing of interest lives *in* an object.
- **Relations** `R : A ⇸ B` — the **`Q`-valued relation**, the primitive arrow, the inhabitant we care
  about. There is **no sort of "self."**

## Generators (all native to the arena)

| Generator | Type | Reading |
|---|---|---|
| `1_A` | `A ⇸ A` | the identity relation |
| `R ⨾ S` | `(A ⇸ B), (B ⇸ C) → (A ⇸ C)` | relating through |
| `R°` | `(A ⇸ B) → (B ⇸ A)` | **converse** — a free involution, not identified with `R` |
| `≤`, `⨆`, `∧` | order on `A ⇸ B` | inclusion, joins (completeness), meets |

No further relating generators are primitive. The content is in the **one definition** D1 (self-relation = the
trace, the diagonal) on the seam-chosen arena — **there are no axioms** — not in a stock of named arrows.

## No self-definition — on purpose

The signature fixes the language; the self is what the language's diagonal turns out to be — a **result**, not
a name. The whole point of paper one is that the self's signature property, **irreversibility**, *arises* from
self-relation; naming a self here would throw that away. The next file states the definition and the theorem.
