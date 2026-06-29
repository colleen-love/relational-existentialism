# 01 — Signature: the vocabulary, no self

> *The arena ([`00-domain.md`](00-domain.md)) fixed the kind of structure. This page fixes the **specific
> language** — and fixes the language only.* **It does not name the self.** The self is the *derived* fixed
> relation of the co-direction dynamics ([`02-axioms.md`](02-axioms.md)); a signature that named it would
> posit the paper's conclusion and make the derivation circular.

## Sorts

- **Objects** `A, B, …` — bookkeeping only; nothing of interest lives *in* an object.
- **Relations** `R : A ⇸ B` — the **`Q`-valued relation**, the primitive arrow. This is the inhabitant we
  care about. There is **no sort of "self"** — "a self" will be a distinguished *relation* (a fixed
  self-relation), derived, never a primitive.

## Generators (all native to the arena)

| Generator | Type | Reading |
|---|---|---|
| `1_A` | `A ⇸ A` | the identity relation |
| `R ; S` | `(A ⇸ B), (B ⇸ C) → (A ⇸ C)` | relating through |
| `R°` | `(A ⇸ B) → (B ⇸ A)` | **converse** — a free involution, `(R°)° = R`, not identified with `R` |
| `≤`, `⨆`, `∧` | order on `A ⇸ B` | inclusion, joins (completeness), meets |

No further relating generators are primitive. Specific relations enter per-model; the content of the theory
is in the **two axioms** and the **one definition**, not in a stock of named arrows.

## Attention is not a separate object

There is **no attention field** and no separate "attention" generator. **Attention is the relation's own
`Q`-weight, read at each end:** the weight `R` carries bears on one end, the weight of its converse `R°` on
the other. "Co-directed attention" is just this two-endedness of a single relation (A2) — it needs no agent,
no field, and nothing added to the vocabulary above.

## No self-definition — on purpose

> Earlier (traced-SMC) drafts defined `self := νΦ_c` in the signature. That is **not done here, and not to be
> reintroduced.** The signature fixes the language; the self is what the language's co-direction dynamics
> turns out to have as a **fixed relation** — a result, derived in the exploration, not a name. The whole
> point of paper one is that the self **arises**; naming it here would throw that away.

The next file states the two axioms (asymmetry, co-direction) and the one definition (self-relation = trace),
and marks **A3 / generativity as a theorem to derive**, not an axiom.
