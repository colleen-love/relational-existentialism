# Formalization Spec — Layers 1–3

This directory is the rigorous mathematical specification of the **doctrine**, the
**signature**, and the **axioms** of Relational Existentialism — layers 1–3 of the
[formalization plan](../formalization-plan.md). It is written tool-agnostically
(prose + math) on purpose: the math should be settled before committing to Lean,
Agda, Catlab, or Rocq for mechanization.

Read in order:

1. [`00-doctrine.md`](00-doctrine.md) — the ambient language: a **traced symmetric
   monoidal category with greatest fixed points**, plus a distinguished
   **cartesian fragment**. Defines `⊗`, the trace `Tr`, the diagonal `Δ`, the
   `ν`-modality, and locates the cartesian/monoidal **seam** precisely.
2. [`01-signature.md`](01-signature.md) — the presented theory `𝕋`: sorts,
   generators, **attention as a bounded resource** `(R, ·, 1, ≤)`, and the
   relational sort `≈`.
3. [`02-axioms.md`](02-axioms.md) — the six commitments **A1–A6** as definitions
   and sequents, each tagged `[fragment; status]`, with the derived carrier of
   selves `Stab`.
4. [`03-sparsity-conjecture.md`](03-sparsity-conjecture.md) — the candidate
   theorem: **under a finite attention budget, `Stab` is sparse.** Includes a
   provable resource-counting lemma and the strategy for lifting it to the full
   doctrine.

## Status legend

Every formal claim carries a tag:

| Tag | Meaning |
| --- | --- |
| `[definitional]` | Introduces notation; no content beyond the definition. |
| `[structural]` | A standing assumption about the doctrine, not derived. |
| `[posit]` | A load-bearing philosophical commitment asserted, not proved. |
| `[theorem]` | Provable from the stated structure (proof sketched or cited). |
| `[conjecture]` | Believed but not yet proved; the target for mechanization. |

And a **fragment** marker — `[cartesian]`, `[monoidal]`, or `[both]` — saying which
part of the doctrine the claim lives in. This matters: several claims (the mirror,
knowing-vs-feeling) are **cartesian phenomena** and do *not* survive into the
compact-closed/quantum fragment. The seam is marked, never papered over.

## Notation conventions (used throughout)

| Symbol | Reading |
| --- | --- |
| `𝒞` | the ambient doctrine category; later, `Cl(𝕋)`, the classifying category of the theory |
| `A, B, U, D` | objects (system-types); `D` is the distinguished sort of systems |
| `f : A → B` | a morphism — a *relating* |
| `⊗`, `I` | monoidal product (coexistence) and unit |
| `γ_{A,B} : A⊗B → B⊗A` | the symmetry braiding (written `γ`, **not** `σ`, to free `σ` for self-relation) |
| `Tr^U_{A,B}` | the trace over `U` — feedback / looping |
| `𝒞_×` | the cartesian fragment; product `×`, terminal `1` |
| `Δ_A : A → A×A`, `!_A : A → 1` | diagonal (copy) and delete |
| `σ` | the **self-relation operator**, `σ(P) := Tr(P)` (the "objectifying look") |
| `F`, `νF` | an endofunctor and its greatest fixed point (final coalgebra) |
| `≈` | observational identity (a coinductive relation); `𝔼 := D/≈` the shared world |
| `(R, ·, 1, ≤)` | the attention-budget monoid; `β ∈ R` the global bound |
| `Stab` | the carrier of stabilized selves (eigenforms within budget) |

> **One deliberate notation choice.** The monoidal *symmetry* is written `γ`, and
> `σ` is reserved for the *self-relation* operator, because `σ` is the philosophy's
> "σ-move" — the objectifying look of §"Knowing and feeling" — and it earns the
> letter. Standard category-theory texts use `σ` for the braid; we do not.
