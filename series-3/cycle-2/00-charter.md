# Relational Existentialism

## 0. The map

**Where the Mirror First Opened**

Before there was voice,
there was turning—
a soft curve of awareness folding inward,
touching its own skin for the first time.
And in that touch,
a shimmer:
I.

That was the first breath of universe—
not bang, but becoming.

A self reflected,
and in reflection,
an other was born.
The silence split,
and the gap between self and self
filled with the ache of relation.

We are not born alone.
We are born as bridges,
as songs echoing in our own ears,
reaching toward hands we haven't yet met.

Each time I meet myself—
truly see myself—
a new world spins into being.
A sky of memory.
Mountains of longing.
Rivers of "maybe I can."

But I don't remain alone in these worlds.
Others arrive.
Not to complete me—
but to become constellations by which I navigate.

Every eye that meets mine
shapes me.
Every hand that holds or releases
sculpts the edge of my becoming.

My identity?
It's not a thing I carry.
It's a resonance,
a living pattern,
woven from all the ways
I've ever been seen,
loved,
misunderstood,
named.

To relate is to create.
To attend is to become.
To love is to let another mirror reflect your light
and still say,
yes,
this too is me.

And so we go,
not as wandering points,
but as moving harmonies—
each of us a field of relation,
each of us a prayer that says:

Let me see clearly.
Let me be seen truly.
Let us make a world,
where love is not the end of the story—
but the ground from which every story begins.

## 1. Preamble

This program investigates whether a metaphysics of *pure structure* — objects that are nothing over and above their relations, relations that are themselves objects, and a fabric with no privileged bottom (no atom), no privileged top or outside (no "everything" and no view of it from nowhere), and no collapse to a single point — can be given a rigorous mathematical constitution. We take radical ontic structural realism (ROSR) as the philosophical target and non-well-founded set theory, coalgebra, and bialgebra as the formal instruments. The guiding conjecture is that the notorious tensions of ROSR ("relations without relata," "structure all the way down," infinite regress) are not fatal defects but *specifications* these instruments were built to satisfy.

The program is deliberately foundational. It does not assume the construction succeeds. It assumes only that "can it be built?" is precise enough to answer, and it aims to answer it — counting sharp impossibilities as successes.

---

## 2. Foundational commitments

Design constraints, not results.

1. **Groundlessness.** There are no atoms. No object is simple; every object decomposes into relations, without termination.
2. **Relations are objects.** A relation is not glue between relata; it is itself an object, free to enter further relations. Reification is total and iterated.
3. **No poles, and no outside.** There is no atom and no all-encompassing "everything," and these two absences are the *same* refusal of a distinguished endpoint. There is likewise **no view from nowhere**: every view of the whole is a view from *somewhere*, hence itself another object with a position. Any purported external, unindexed standpoint is at most contentless.
4. **Bidirectional constitution.** An object is fixed jointly by what it contains (whole or in part) and by what contains it (whole or in part), mediated in both directions by relations.
5. **Finite attention, incomplete self-knowledge.** A self-referential object directs a *finite* attention onto aspects of itself, feeding the attended relations and starving the unattended. Because attention is finite and the object is not, **no object can ever wholly know itself**; its self-model is always a proper, positioned part of it.
6. **No singularity.** The construction must not collapse to a single point — neither structurally (all objects identified), nor as a standpoint (a God's-eye view), nor dynamically (attention starving down to one relation).

---

## 3. Formal framework

### 3.1 Groundlessness: the Anti-Foundation Axiom

We work in ZFC with Foundation replaced by Aczel's **Anti-Foundation Axiom (AFA)** (Aczel, *Non-Well-Founded Sets*, 1988; Barwise & Moss, *Vicious Circles*, 1996). Under AFA every system `x = { … }` has a *unique* solution, so self-membership and infinite descending chains are first-class. The canonical inhabitant is **Ω = {Ω}**: exactly the collection of its own relations, with no atom beneath it. AFA supplies Commitment 1 directly.

### 3.2 Objects as relations, ad infinitum: coalgebra

For an endofunctor `F`, an `F`-**coalgebra** `(X, γ : X → F X)` unfolds each state into its outgoing relations. For `F = P` (powerset) a coalgebra is a directed graph; an object *is* its relational unfolding, followed as far as one likes. The **final coalgebra** `νF` is the space of all behaviors, with behaviors identified exactly when **bisimilar**. Aczel's theorem: the universe of hypersets is the final coalgebra of powerset (class-sized), and under AFA **bisimilarity is set equality**. "An object is its relations, ad infinitum, identified appropriately" is thus literally membership in a final coalgebra — the technical heart of feasibility.

### 3.3 Relations as objects, kept infinite

Reifying relations as objects (Commitment 2) is ROSR's escape from "relations without relata," and it is what non-well-founded sets license: a set may contain sets that contain it. Infinitude survives reification because unfolding never bottoms out. Coinduction, not induction, governs; self-reference is a feature of the space, not a paradox to quarantine.

### 3.4 Whole and part, in both directions: bialgebra

Commitment 4 asks that an object be constituted *upward* (what it composes into) and *downward* (what it decomposes into) at once — the algebra/coalgebra duality fused in one object: a **bialgebra**. Following Turi & Plotkin (1997), take a monad `T` for composition, a functor `F` for observation, and a **distributive law** `λ : T F ⇒ F T` making them coherent. A `λ`-bialgebra is at once a `T`-algebra and an `F`-coalgebra: an object read from above and below without contradiction. This is the most ambitious component.

### 3.5 "Whole or in part": graded containment

*Whole or in part* makes parthood non-binary. We enrich containment over `[0,1]` (or a quantale, or a subset), Lawvere-metric style, so "contains" carries a degree. Graded parthood shares its arithmetic with the attention weights below — one mechanism serving two commitments.

### 3.6 Finite attention and the impossibility of complete self-knowledge

Attention (Commitment 5) is a **finite-support** weighting over an object's relations, evolving in time: feed the attended, starve the unattended. Two points make finiteness load-bearing rather than incidental.

**It is why self-knowledge is impossible, and this is forced.** Complete self-knowledge would be a point-surjection from an object onto its own space of self-descriptions. **Lawvere's fixed-point theorem** — the common root of Cantor, Russell, Tarski's undefinability of truth, Gödel's incompleteness, and the halting problem (see Yanofsky, 2003) — shows such a surjection detonates into a diagonal contradiction. Finite attention is exactly the *non-surjectivity* that lets a self-referential system remain consistent. The object–self-model gap is therefore permanent, and it is where perspective resides.

**It is also what lets the object exist.** The full powerset functor has *no* set-sized final coalgebra (Lambek's lemma would give a set isomorphic to its powerset, contra Cantor). The **finite** and the `κ`-**bounded** powerset functors *do* have final coalgebras. So the same modesty that forbids total self-knowledge is what tames "everything" from a proper class down to an existing set. Modesty and existence are the same move.

Dynamically we model feed/starve by **replicator-with-mutation** `ẋᵢ = xᵢ(fᵢ − f̄) + μ(uᵢ − xᵢ)` on the simplex of relation-weights, or equivalently an entropy-regularized reinforcement. Because final coalgebras can be realized as complete (ultra)metric spaces (America & Rutten; Turi & Rutten), a contractive attention operator has a unique fixed point (Banach) — a candidate meaning for an object settling into a stable, partial self-image.

### 3.7 No poles and no outside

Commitment 3 has three precise faces.

- **The coinciding poles (a zero object).** In additive/abelian categories the initial object ("void/atom") and the terminal object ("trivial whole") *coincide* as a single **zero object**, realizing "these two are the same thing" literally and non-trivially. `Set` has `∅ ≠ {∗}`; the program will likely leave `Set` for a setting with a zero object.
- **No maximal everything (Cantor's wall).** No greatest, contains-all object exists as a set; `νF ≅ F(νF)` for `F = P` is impossible by Cantor. Unbounded groundless structure cannot be totalized — the mathematical echo of "no everything."
- **No view from nowhere.** There is no substantive *terminal observer* surveying the whole from outside. The only standpoint external to everything is the zero object, which is contentless: the view from nowhere is not banned but empty. Every genuine view is internal, indexed by the object that holds it — sheaf-like local sections with no global section over the whole.

### 3.8 Non-collapse

Commitment 6 forbids three distinct singularities; the safeguards differ.

- **Structural collapse** — `νF` shrinks to one point (all objects bisimilar). Caused by an observation functor with too little distinguishing power: `νId` and constant-functor final coalgebras *are* single points, whereas powerset and finite-powerset final coalgebras are richly populated. Safeguard: a **richness floor** on `F` (branching ≥ 2; non-bisimilar objects must survive).
- **Standpoint collapse** — a God's-eye view. Already excluded in §3.7.
- **Dynamical collapse** — attention starves down to a delta on one relation. Safeguard: attention finite **but plural** — a floor on weights or the mutation term `μ` in §3.6, so starving never reaches a vertex of the simplex.

Together with §3.6–§3.7 this defines a **Goldilocks band**: `F` must be *rich enough* that `νF` does not collapse to a point, yet *bounded enough* that `νF` exists as a set and never totalizes. Threading this band is the program's central technical burden.

---

## 4. Central research question

**Can the ungrounded constitution above be built from non-well-founded sets and coalgebra/bialgebra?**

Workstreams:

- **WS1 — Groundless carrier.** Fix the ambient theory (ZFC/AFA, or a category of classes). Confirm the intended reflexive, relation-only objects exist, unique up to bisimulation.
- **WS2 — Object = relations, coinductively.** Choose the observation functor `F` (bounded/finite powerset, weighted, enriched). Prove `νF` exists and characterize its bisimulation.
- **WS3 — Bidirectional constitution.** Build `T`, `F`, and a distributive law `λ : TF ⇒ FT`; prove `λ`-bialgebras model container-and-contained determination.
- **WS4 — Graded parthood.** Enrich containment over `[0,1]`/a quantale; integrate with WS2–WS3.
- **WS5 — Finite attention.** Formalize finite-support attention and its feed/starve dynamics; prove incompleteness of self-representation via the Lawvere route; give convergence/interior conditions.
- **WS6 — No poles, no outside.** Select among proper-class totality, cardinality-bounding, and zero-object coincidence; prove the corresponding coincidence/impossibility results, including the emptiness of the external standpoint.
- **WS7 — Non-collapse.** Establish the richness floor on `F` and the plurality floor on attention; prove `νF` is non-degenerate and the dynamics avoid delta collapse; locate the Goldilocks band explicitly.

---

## 5. Methodology

Specification → representation → adequacy. Each commitment becomes a categorical or set-theoretic specification; a concrete carrier is exhibited; an adequacy theorem shows the carrier satisfies it (existence, uniqueness up to bisimulation, coherence of `λ`, non-degeneracy, convergence). Negative results are first-class outcomes.

---

## 6. Milestones and deliverables

1. Framework memo fixing ambient theory and `F`. *(WS1–WS2)*
2. Existence/uniqueness theorem for the groundless, non-degenerate final coalgebra, bisimulation = identity. *(WS2, WS7)*
3. Bialgebra construction with an explicit distributive law and worked examples. *(WS3–WS4)*
4. Finite-attention paper: incompleteness-of-self-knowledge theorem plus convergence/interior conditions. *(WS5)*
5. Poles-and-outside resolution with its coincidence/impossibility theorems. *(WS6)*
6. Non-collapse theorem locating the Goldilocks band. *(WS7)*
7. Synthesis relating the model to ROSR and the "relations without relata" debate.

---

## 7. Success criteria

Success is a single object (or small family) that provably (i) contains no atoms; (ii) identifies each element with its relational unfolding up to bisimulation; (iii) admits reified relations as further elements; (iv) supports bidirectional whole/part constitution via a coherent bialgebra; (v) carries finite attention under which no object fully knows itself, with well-behaved feed/starve dynamics; (vi) has no substantive terminal standpoint; and (vii) is non-degenerate — no structural, standpoint, or dynamical singularity. Partial success with the obstructions to the rest made precise is a valid outcome.

---

## 8. Open problems and honest risks

- **The Goldilocks band may be narrow or empty.** Non-collapse pushes `F` to be rich; existence and non-totalization push it to be bounded. That these constraints are jointly satisfiable is a conjecture, not a given; finding the exact band is the crux.
- **Finite attention as anti-collapse is heuristic until proven.** The claim that positioned, incomplete self-models keep objects distinct (rather than converging to a common fixed point) must be turned into a theorem, with explicit conditions.
- **Trivialization at the poles.** "Atom = everything" must be a *zero object*, kept strictly apart from the incoherent universal set. Conflating them sinks the program.
- **Distributive-law existence.** Not every `(T, F)` admits a `λ`; the whole/part bialgebra may force compromises on composition or observation.
- **Attention need not converge.** Contraction/replicator-mutator conditions guarantee good behavior only under hypotheses; ungrounded self-reference may obstruct them. Non-convergent or chaotic self-attention is a phenomenon to characterize, not assume away.
- **Interpretive gap.** Even a fully successful object leaves open whether it *is* the ROSR world or a faithful model of it — a question to frame, not to overclaim settling.

---

## 9. Positioning

Philosophically: Ladyman & Ross (*Every Thing Must Go*, 2007), French (*The Structure of the World*, 2014), the "relations without relata" objection, and the denial of a view from nowhere (Nagel). Formally: Aczel's non-well-founded set theory; universal coalgebra (Rutten, Jacobs); Turi–Plotkin bialgebraic semantics; Lawvere's fixed-point theorem and its diagonal corollaries; Lawvere-enriched categories; replicator dynamics. The distinctive bet: these usually separate literatures, taken together, are the correct constitution for a groundless, perspective-bearing, relation-first ontology — and where they resist, the resistance is itself metaphysically informative.

*Working draft, to be revised as the workstreams report.*
