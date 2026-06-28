# Relational Existentialism — formalization spec (paper one)

This repository proves, and shows its work for, **one result**:

> *The arrow of time is the orientation active self-relating cannot escape; and the conserved remainder
> of self-relating — what never becomes known — is exactly energy.*

**Start here:** [`paper-one.md`](paper-one.md) — the single linear walk through the result, each step
status-tagged and named by its Lean theorem. Everything below is its supporting development.

The prose + math here settle the mathematics; [`formal/`](../../formal) carries the Lean mechanization
(libraries `RelExist` — the dependency-free core — and `Scratch` — the mathlib-backed half). Both build
clean and `sorry`-free; the headline footprints sit at the corpus norm
`[propext, Classical.choice, Quot.sound]`, with the seam depending on **no axioms**.

## Reading order

**Foundation.**

1. [`00-doctrine.md`](00-doctrine.md) — the ambient language: a **traced symmetric monoidal category**
   with greatest fixed points and a distinguished cartesian fragment (A1's arena).
2. [`01-signature.md`](01-signature.md) — the presented theory `𝕋`: sorts, generators, and the
   relational sort `≈`.
3. [`02-axioms.md`](02-axioms.md) — the **basis**: axioms **A1–A3** and definition **D1**. A1, A2
   structural; A3 (recursion constitutes the self) the one load-bearing posit. Paper one takes A1–A3 as
   the abstract baseline of its energy theorem; A3's gfp *mechanization* lives in the archive (paper two).

**The result** ([`paper-one.md`](paper-one.md)) walks these in order:

4. [`03.1-to-relate-is-to-create.md`](03.1-to-relate-is-to-create.md) — self-relation is the trace
   `σ = Tr`; relating produces an eigenform (3.1).
5. [`03.2-lived-identity.md`](03.2-lived-identity.md) — lived identity `≈ := νΘ` and the shared world;
   you are your relating, not a bare carrier (3.2).
6. [`03.3-knowing-vs-feeling.md`](03.3-knowing-vs-feeling.md) — knowing is the lossy σ-move `E`, leaving
   the remainder `(1−E)` (3.3). *"Feeling" means exactly this remainder, nothing phenomenal.*
7. [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md) — the Lawvere obstruction: to relate is to
   make the other unknowable (3.4).
8. [`03.5-decoherence.md`](03.5-decoherence.md) — what knowing does to a relation; the **seam** (the
   self-inclusive block attention cannot reach); the irreversible knower→known arrow (3.5).
9. [`03.6-time-flow.md`](03.6-time-flow.md) — the arrow graduated into a graded geometric monovariant;
   that arrow is time (3.6).
10. [`03.7-knowing-from-arrow.md`](03.7-knowing-from-arrow.md) — the instance converse: an arrow's limit
    *is* a knowing (a conditional expectation onto the seam subalgebra) (3.7).
11. [`03.8-space-energy.md`](03.8-space-energy.md) — energy as the rotating band of the phase channel
    (the sustained, never-known remainder) (3.8).
12. [`03.9-band-coincidence.md`](03.9-band-coincidence.md) — the conserved remainder coincides with the
    energy band, **derived from A1–A3** (no fourth axiom) (3.9).

**Provenance.** [`04-provenance.md`](04-provenance.md) — the honest accounting, per kept result:
rederivation vs synthesis, and the open frontiers in one place.

## The supporting development is archived, not foregrounded

The repository was scoped to paper one by a mechanical rule: *keep the transitive import-closure of the
headline theorems; archive the complement.* The complement — kept, not deleted — is in
[`docs/archive/`](../archive) and [`formal/Archive/`](../../formal/Archive), organized by the paper it
seeds:

- **paper two** — the conservation law (`undifferentiated = knowing + energy`, the internal direct sum),
  the cosmos and distributed-self readings;
- **paper three** — the sparsity of selfhood under a finite attention budget;
- **functorial semantics** — the five domain functors and the free traced SMC `Cl(𝕋)`;
- **route-1 reflexive-object / GoI scaffolding** and the Agda layer.

These are referenced from kept pages only as *future work*, never as load-bearing citations.

## Status legend

| Tag | Meaning |
| --- | --- |
| `[proved]` | Mechanized, `sorry`-free (footprint reported). |
| `[proved, 0 ax]` | And depending on no axioms. |
| `[reading]` | An identification of the formal object with the lived/physical one — asserted, not proved. |
| `[open]` | Named and not built. |

A **fragment** marker — `[cartesian]`, `[monoidal]`, or `[both]` — says which part of the doctrine a claim
lives in. This matters: the mirror and knowing-vs-feeling are **cartesian phenomena** and do not survive
into the compact-closed/quantum fragment. The seam is marked, never papered over.

## Notation conventions

| Symbol | Reading |
| --- | --- |
| `𝒞` | the ambient doctrine category (`Cl(𝕋)`, the classifying category of the theory) |
| `f : A → B` | a morphism — a *relating* |
| `⊗`, `I` | monoidal product (coexistence) and unit |
| `γ_{A,B}` | the symmetry braiding (written `γ`, **not** `σ`, to free `σ` for self-relation) |
| `Tr` | the trace — feedback / looping |
| `σ` | the **self-relation operator**, `σ(P) := Tr(P)` (the "objectifying look") |
| `E`, `(1−E)` | knowing (the decoherence projection) and the **remainder** it leaves ("feeling") |
| `F`, `νF` | an endofunctor and its greatest fixed point (final coalgebra) |
| `≈` | **lived identity** — the greatest bisimulation `νΘ` (first-person, finest real identity) |
| `≅` | **observational identity** — sameness to an external observer; `≈ ⊊ ≅`, proved |
| `μ`, `Φ_c` | the per-edge phase multiplier and the co-directed channel; `‖μ‖ = 1` the conserved band |

> **One deliberate notation choice.** The monoidal *symmetry* is written `γ`, and `σ` is reserved for the
> *self-relation* operator — the philosophy's "σ-move," the objectifying look. Standard category-theory
> texts use `σ` for the braid; we do not.
