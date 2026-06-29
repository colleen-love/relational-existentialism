# Relational Existentialism — formalization spec (paper one)

This repository proves, and shows its work for, **one result**:

> *The arrow of time is the orientation active self-relating cannot escape; and the conserved remainder
> of self-relating — what never becomes known — is exactly energy.*

**Start here:** [`paper-one.md`](paper-one.md) — the single linear walk through the result, each step
status-tagged and named by its Lean theorem. Everything below is its supporting development.

The prose + math here settle the mathematics; [`formal/`](../../lake) carries the Lean mechanization
(libraries `RelExist` — the dependency-free core — and `Scratch` — the mathlib-backed half). Both build
clean and `sorry`-free; the headline footprints sit at the corpus norm
`[propext, Classical.choice, Quot.sound]`, with the seam depending on **no axioms**.

## Reading order

**Foundation.**

1. [`00-doctrine.md`](../../theory/spec/00-doctrine.md) — the ambient language: a **traced symmetric monoidal category**
   with greatest fixed points and a distinguished cartesian fragment (A1's arena).
2. [`01-signature.md`](../../theory/spec/01-signature.md) — the presented theory `𝕋`: sorts, generators, and the
   relational sort `≈`.
3. [`AXIOMS.md`](../../theory/spec/AXIOMS.md) — the **canonical basis** (now in `theory/spec/`): axioms
   **A1–A3** and definition **D1**, with **A3 reframed as a process** and the self its *derived* fixed point
   (handoff XX). Paper one cites these; the per-node map of paper one's own development is
   [`NODES.md`](../../theory/spec/NODES.md) (the `P1.x` nodes).

**The result** ([`paper-one.md`](paper-one.md)) walks these in order:

4. [`P1.1-to-relate-is-to-create.md`](P1.1-to-relate-is-to-create.md) — self-relation is the trace
   `σ = Tr`; relating produces an eigenform (3.1).
5. [`P1.5-lived-identity.md`](P1.5-lived-identity.md) — lived identity `≈ := νΘ` and the shared world;
   you are your relating, not a bare carrier (3.2).
6. [`P1.6-knowing-vs-feeling.md`](P1.6-knowing-vs-feeling.md) — knowing is the lossy σ-move `E`, leaving
   the remainder `(1−E)` (3.3). *"Feeling" means exactly this remainder, nothing phenomenal.*
7. [`P1.10-limits-of-knowing.md`](P1.10-limits-of-knowing.md) — the Lawvere obstruction: to relate is to
   make the other unknowable (3.4).
8. [`P1.8-decoherence.md`](P1.8-decoherence.md) — what knowing does to a relation; the **seam** (the
   self-inclusive block attention cannot reach); the irreversible knower→known arrow (3.5).
9. [`P1.13-the-arrow.md`](P1.13-the-arrow.md) — the arrow graduated into a graded geometric monovariant;
   that arrow is time (3.6).
10. [`P1.14-knowing-from-arrow.md`](P1.14-knowing-from-arrow.md) — the instance converse: an arrow's limit
    *is* a knowing (a conditional expectation onto the seam subalgebra) (3.7).
11. [`P1.15-phase-bearing.md`](P1.15-phase-bearing.md) — energy as the rotating band of the phase channel
    (the sustained, never-known remainder) (3.8).
12. [`T.3-band-coincidence.md`](../../theory/spec/T.3-band-coincidence.md) — the conserved remainder coincides
    with the energy band, **derived from A1–A3** (no fourth axiom). *(Now a `theory/` node, `T.3`, since the
    band layer is shared by papers one and two.)*

**Provenance.** [`04-provenance.md`](04-provenance.md) — the honest accounting, per kept result:
rederivation vs synthesis, and the open frontiers in one place.

## The supporting development is archived, not foregrounded

The repository was scoped to paper one by a mechanical rule: *keep the transitive import-closure of the
headline theorems; archive the complement.* The complement — kept, not deleted — is in
[`docs/archive/`](../../archive/spec) and [`formal/Archive/`](../../archive/formal/Archive), organized by the paper it
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
