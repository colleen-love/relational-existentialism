# Formalization Spec — Layers 1–4

This directory is the rigorous mathematical specification of the **doctrine**, the
**signature**, the **axioms**, the **theorems**, and the **functorial semantics** of Relational
Existentialism. The prose + math here settles the mathematics; the [`formal/`](../../formal)
directory carries the Lean mechanization, which now reaches all the way through Layer 4 (the free
traced SMC `Cl(𝕋)`, its coherent refinement, and all five domain functors).

Read in order:

1. [`00-doctrine.md`](00-doctrine.md) — the ambient language: a **traced symmetric
   monoidal category with greatest fixed points**, plus a distinguished
   **cartesian fragment**. Defines `⊗`, the trace `Tr`, the diagonal `Δ`, the
   `ν`-modality, and locates the cartesian/monoidal **seam** precisely.
2. [`01-signature.md`](01-signature.md) — the presented theory `𝕋`: sorts,
   generators, **attention as a bounded resource** `(R, ·, 1, ≤)`, and the
   relational sort `≈`.
3. [`02-axioms.md`](02-axioms.md) — the **basis**: the **axioms A1–A3** and the
   **definition D1**, each tagged `[fragment; status]`. (Only what is *assumed*.)
4. [`03-theorems.md`](03-theorems.md) — what is *proved*: the theorems **T1–T3** and the
   derived notions, each with a status tag and Lean name. The structural results split into
   four pages:
   - [`03.1-sparsity.md`](03.1-sparsity.md) — the candidate theorem: **under a finite
     attention budget, `Stab` is sparse.** A provable resource-counting lemma, the
     mechanized topological form, and the strategy for the full lift.
   - [`03.2-limits-of-knowing.md`](03.2-limits-of-knowing.md) — the relational typology and the
     Lawvere obstruction: *to relate is to make the other unknowable.*
   - [`03.3-decoherence.md`](03.3-decoherence.md) — what knowing does to a relation
     (decoherence, selective attention, the conserved coherence, and the **seam** — the one
     trace a self cannot take on itself).
   - [`03.4-the-self-quantified.md`](03.4-the-self-quantified.md) — the Banach-algebra limit of
     self-in-other, the quantitative eigenform, and the unification of the two selves.
5. [`04-functorial-semantics.md`](04-functorial-semantics.md) — **Layer 4**: the
   domains as functors `Cl(𝕋) → 𝒟_domain`, with verdicts. All five domains
   (**physics** — a literal matrix model with trace = partial trace, plus the
   **decoherence** retraction onto the classical fragment; **chemistry** and
   **biology** — eigenforms; **AI** — feedback = the trace; and the **firewall** for the
   cartesian/social domains), the **free traced SMC `Cl(𝕋)`** with its universal functor,
   and the **monoidal-coherence** refinement are all mechanized.

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
