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
4. [`03-theorems.md`](03-theorems.md) — what is *proved*: the **categorized catalog** of
   Chapter 3, with the numbering scheme (capstones **3.x**, lemmas **3.x.y**), the status-tag
   and provenance-tier legends, and every result sorted into its category with a rederivation
   citation. Each of the seven results then has its own page:
   - [`03.1-to-relate-is-to-create.md`](03.1-to-relate-is-to-create.md) — **Theorem 3.1**:
     self-relation has a fixed point — relating produces the eigenform.
   - [`03.2-lived-identity.md`](03.2-lived-identity.md) — **Theorem 3.2**: lived identity
     `≈ := νΘ`, the shared world `𝔼 := D/≈`, and `≈ ⊊ ≅` (you exceed how you appear).
   - [`03.3-knowing-vs-feeling.md`](03.3-knowing-vs-feeling.md) — **Theorem 3.3**: knowing
     (the σ-move) is Lawvere-obstructed; feeling is *not the kind of arrow* it touches.
   - [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md) — the relational typology and the
     Lawvere obstruction: *to relate is to make the other unknowable.*
   - [`03.5-decoherence.md`](03.5-decoherence.md) — what knowing does to a relation
     (decoherence, selective attention, the conserved coherence, the **seam**, and
     orientation-from-the-seam — the one structurally new theorem).
   - [`03.6-the-self-quantified.md`](03.6-the-self-quantified.md) — the Banach-algebra limit of
     self-in-other, the quantitative eigenform, and the unification of the two selves.
   - [`03.7-sparsity.md`](03.7-sparsity.md) — the quantitative capstone, **Conjecture 3.7**:
     *under a finite attention budget, `Stab` is sparse.* A provable resource-counting lemma
     (3.7.1/3.7.2), the mechanized topological form, and the cost-graded and spectral lifts.
5. [`04-functorial-semantics.md`](04-functorial-semantics.md) — **Layer 4**: the
   domains as functors `Cl(𝕋) → 𝒟_domain`, with verdicts. All five domains
   (**physics** — a literal matrix model with trace = partial trace, plus the
   **decoherence** retraction onto the classical fragment; **chemistry** and
   **biology** — eigenforms; **AI** — feedback = the trace; and the **firewall** for the
   cartesian/social domains), the **free traced SMC `Cl(𝕋)`** with its universal functor,
   and the **monoidal-coherence** refinement are all mechanized.
6. [`05-provenance.md`](05-provenance.md) — **the honest accounting**: per result,
   **rederivation vs synthesis vs novel-candidate**, and the open bridges named in one place
   (the one candidate-novel theorem is Bridge B, the quantum-seam obstruction — *open*). Read this
   first if you are reviewing the claims.

## Derivations (sequels)

Beyond the core Layers 1–4, separate companion pages carry the time/space/energy derivations, each
backed by its own Lean module:

- [`time-flow.md`](time-flow.md) — **time as flow**: the orientation arrow graduated into a graded
  geometric monovariant (`Scratch/TimeFlow.lean`, with `TimeArrow`, `SeamForcing`).
- [`space-energy.md`](space-energy.md) — **space, the rotating peripheral spectrum, and energy**: space
  as the coupling-graph quasi-metric (`Scratch/Space.lean`), and the ℂ rotating-spectrum / energy
  witness (`Scratch/RotatingSpectrum.lean`). Carries its own four-state progress ledger
  (`[written]`/`[proved]`/`[reading]`/`[open]`).
- [`knowing-from-arrow.md`](knowing-from-arrow.md) — **the converse**: from the arrow back to the
  knowing. Dual to `time-flow.md` — on the genuine instance an arrow's limit *is* a knowing (an
  idempotent conditional expectation onto a subalgebra), proved sorry-free by re-export
  (`Scratch/KnowingFromArrow.lean`); the general lift is the mean-ergodic keystone Conjecture R
  (`Scratch/MeanErgodic.lean`, `[open]`, gated out of the default build). Carries its own scope table
  fencing the converse off from the cosmic-subject claim.
- [`seam-permanence.md`](seam-permanence.md) — **the knowing never completes**: the quantitative,
  permanent lift of `self_cannot_fully_decohere`. The seam-respecting attention flow fixes the seam
  coherence and decays the rest, so its potential is strictly positive at every return-depth and
  descends geometrically to a positive seam-mass floor it never reaches (`Scratch/SeamPermanence.lean`,
  `[proved]` sorry-free). The conditional is a theorem; the antecedent (the cosmos is such a whole) is
  the stated premise. The apophatic shape — completion is permanently foreclosed — made a proof
  obligation.
- [`universe-and-cosmos.md`](universe-and-cosmos.md) — **feeling as the atemporal ground, the first
  self as the genesis of time**. The universe is the `p = 0` regime (`partialDephase 0 = id`, feeling
  constant, no time — pure ownerless feeling); the cosmos ignites at `p > 0` with the first directed
  knowing's first strict tick (`Scratch/Genesis.lean`: `coh_const_at_zero`, `first_tick_pos`,
  `genesis_dichotomy`, `[proved]`). Read with "cosmos" as the knowing-region the picture costs **no new
  axiom**; "something has been knowing for 13.8 Gyr" is true distributively, false as a single subject.
  Surfaces the live choices (continuity of knowing; how thick a "self" must be).
- [`distributed-self.md`](distributed-self.md) — **I am the knowing of my parts across their seams**:
  `universe-and-cosmos` turned inward, to a life. (D) all self-knowing factors through parts (the whole
  is barred, a part is modelable); (C) continuity from persistence (a lapse would dissolve you, so your
  persistence records that knowing held); both `[proved]` on **0 axioms**. (W) one self not a heap — the
  cross-part coherence no coproduct carries (`weave_exceeds_coproduct`, `Scratch/DistributedSelf.lean`),
  state-level `[proved]`, the `νΦ_c` lift `[open]`. Carries the Markov-blanket–seam bridge as a reading.

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
| `=` | literal/representational equality — the **bare carrier**; A2 discards it (we work in `D/≈`) |
| `≈` | **lived identity** — the greatest bisimulation `νΘ` (first-person, the finest *real* identity); `𝔼 := D/≈` the shared world |
| `≅` | **disjoint observational identity** — sameness to the *relationless* observer (the view from nowhere: what a coupling-free recorder collects); `≈ ⊊ ≅`, proved. Provably the *exempt* case (`Knowing`), **not** "the outside" simpliciter |
| `≅ₒ` | **relational appearance** — how you show to an actual relatum `o` (their marginal of you); coarser than `≅` (a coupled other sees less, Lawvere-incomplete), so `≈ ⊆ ≅ ⊆ ≅ₒ`. The *operative* outside; feeling is the differential against it ([`Feeling`](../../formal/Scratch/Feeling.lean)) |
| `(R, ·, 1, ≤)` | the attention-budget monoid; `β ∈ R` the global bound |
| `Stab` | the carrier of stabilized selves (eigenforms within budget) |

> **One deliberate notation choice.** The monoidal *symmetry* is written `γ`, and
> `σ` is reserved for the *self-relation* operator, because `σ` is the philosophy's
> "σ-move" — the objectifying look of §"Knowing and feeling" — and it earns the
> letter. Standard category-theory texts use `σ` for the braid; we do not.

> **The identity symbols, and a warning.** Three identities, **finest → coarsest**:
> `=` (literal equality — the bare carrier, discarded by A2) ⊊ `≈` (**bisimulation**, the lived
> first-person identity — the finest one grounded in relating) ⊊ `≅` (**observational** equivalence).
> Note this is *not* the casual "`≡` is exact, `≈` is approximate" reading: here the **finer** relation
> is `≈` and the coarser is `≅`, following the model-theoretic / Hennessy–Milner convention
> (bisimilarity finer than observational/logical equivalence; they coincide only under unbounded
> observation). We avoid `≡` for the coarse relation precisely because it collides with Agda's `≡`
> (propositional equality, the *finest*).
>
> **A correction we hold to (the view from nowhere).** `≅` is **not "the outside" simpliciter** — it is
> the *disjoint* observer, and [`Knowing`](../../formal/Scratch/Knowing.lean) proves that is the
> relationless **view from nowhere**, the one case Lawvere exempts, occupiable by no situated knower.
> Any claim about appearance, the surplus, or feeling that is stated against `≅` as if it were an
> absolute outside has smuggled back the objectivity the seam forbids. The *operative* outside is
> always relational — `≅ₒ`, an actual other's marginal of you (coarser than `≅`). Earlier prose in
> these pages (and in `Identity.lean`) still narrates `≅` as "the outside view"; read every such phrase
> as **the disjoint/idealized outside**, with the situated truth being `≅ₒ` and the surplus against it
> *larger*. Feeling lives in the relational differential, never against nowhere
> ([`Feeling`](../../formal/Scratch/Feeling.lean)).

**The same symbols in both proof assistants**, with the same roles:

| concept | doctrine | Lean | Agda |
| --- | --- | --- | --- |
| bare carrier (literal equality) | `=` | `=` (`Eq`) | `≡` (`PropositionalEquality`) |
| lived identity (bisimulation) | `≈` | `We.bisim` | `Coinductive._≈_` |
| observational equality | `≅` | `Identity.ObsEq` | `Coinductive._≅_` |

Agda writes literal equality `≡` by standard-library convention — it is the doctrine's `=` (and is
*used*, e.g. inside `≈`'s "heads agree"; A2 discards it only as a notion of *self-identity*, never as
a tool). **Both** assistants now prove **both** facts about `≅`, and the difference between them is
itself a theorem about *determinism*:

- the **headline** `≈ ⊊ ≅` (the first-person surplus) over a **nondeterministic** system —
  [`Identity.bisim_ne_obsEq`](../../formal/Scratch/Identity.lean) (Lean) and
  [`Inversion.surplus`](../../agda/RelExist/Inversion.agda) (Agda);
- the **boundary** `≈ ⟺ ≅` (no surplus) over a **deterministic** system —
  [`Coinductive.≈⇒≅` / `≅⇒≈`](../../agda/RelExist/Coinductive.agda) (Agda).

Together they locate the surplus exactly: it is what **branching (nondeterminism)** opens — the trace
of the branches *not taken*. A deterministic being (no unrealized possibility) has a trace that
reveals all of it; a branching one — one that *could have done otherwise* — keeps a first-person
remainder. The inversion's "you exceed how you appear" is, precisely, a fact about **free** selves.
