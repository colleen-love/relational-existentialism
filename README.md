Licensing
This repository is dual-licensed, with a deliberate split between code and writing. The boundary is drawn explicitly so there is no ambiguity about which file falls under which license.

Code — Apache License 2.0
All source code is licensed under the Apache License, Version 2.0. The full text is in LICENSE at the repository root.

This covers everything that is software: scripts, proof-assistant developments (Lean / Agda / Rocq), Julia and Python sources, configuration, build tooling, and any other executable or machine-readable code, wherever it sits in the tree (including any code embedded in or shipped under /docs or /writing — e.g. runnable example files).

Writing — Creative Commons Attribution 4.0 International (CC BY 4.0)
All prose, philosophy, and other written/creative material is licensed under CC BY 4.0. The full text is in LICENSE-docs.

This covers everything in the per-root spec/ directories (and any /writing) — the philosophy itself, explanatory essays, notes, diagrams-as-exposition, and the formalization write-up — plus any prose documentation elsewhere in the repository (such as this README.md).

Under CC BY 4.0 you are free to share and adapt this material for any purpose, including commercially, provided you give appropriate credit, link to the license, and indicate if changes were made.

Where the line falls
Material	License	File
Source code (anywhere in the tree)	Apache 2.0	LICENSE
Prose / philosophy / docs in per-root spec/ and /writing	CC BY 4.0	LICENSE-docs
This README and other prose docs	CC BY 4.0	LICENSE-docs
Final manuscripts in /papers	All rights reserved	papers/README.md
Exception — /papers (all rights reserved). The /papers directory is expressly excluded from the CC BY 4.0 grant. Its contents are © 2026 Colleen Love, all rights reserved; no license is granted. The "prose elsewhere in the repository is CC BY 4.0" rule does not reach into /papers, so copyright in the final manuscripts stays free to assign at submission.

The governing rule when a directory or file contains both kinds of material: code is Apache 2.0; the surrounding prose is CC BY 4.0. When in doubt, the nature of the file decides — a .lean, .jl, .py, or other source file is code (Apache 2.0); a .md or other prose document is writing (CC BY 4.0). The one exception is /papers, above, which is all rights reserved.

© 2026 Colleen Love. Code under Apache-2.0; written material under CC BY 4.0.

# Spec II.0 — Ontology, Arena, and Axioms

> *Before there was voice, / there was turning — / a soft curve of awareness folding inward, / touching its own skin for the first time.*

**Series II, document 0.** This is the foundational specification for the mathematical formalization of relational existentialism and for the repository's central argument. It is written to be read cold: a visitor with no prior contact with this project should be able to reconstruct the claim, the design, and the reasons for every load-bearing choice from this document alone. Successor documents (II.I, II.II, ...) refine construction details; II.0 is the document of record for *what is being built and why*.

**Status:** normative for the ontology, arena, signature, and axiom ledger. Open items are marked `OPEN` and are the intended subjects of successor specs. The document is honest about which theorem targets have known proof routes and which are research (§5, §8).

---

## 0. The claim, for a cold reader

Radical ontic structural realism (ROSR) holds that reality is *relations all the way down*: there are no fundamental objects, only structure. Critics answer with a well-rehearsed sequence of objections:

1. **The relata objection.** Relations require relata. A web with no nodes is incoherent.
2. **The renaming objection.** Any formal model offered in defense will contain individuated, self-identical, quantified-over entities — and those are objects, whatever the model calls them. The eliminativist has only renamed.
3. **The equivocation objection.** The defense needs the word "relation" twice, in disjoint roles — once for the relating and once for the things related — and the position survives only by sliding between them.

This repository answers all three **by construction**. We specify, and mechanize in Lean 4, a two-layer mathematical structure:

- **The primitive layer: relating.** A process, not a thing. It has no base sort, no slots, no argument places, no external scale of degree. One axiom governs it (A8: observation is lossy and partially transmissible). Nothing at this layer is an object, and nothing at this layer is *related by* objects.
- **The derived layer: objects.** An object is a *pattern of relating that has closed* — coalesced into a self-contained, coherent unfolding. Objecthood is not posited; it is **defined** (closure of a pattern of relating) and then **proved to be instantiated** (the existence of the universe of objects, Ω, is a theorem — T2). Every classical axiom one would want about objects — that they self-relate, that they compose, that they are constituted by what they relate to — returns as a *theorem about the derived layer*.

The relationship between the layers is itself a piece of mathematics, not a metaphor: the **closure operator** taking an arbitrary pattern of relating to the unique object it determines is the anamorphism into the final coalgebra (§2.2). "The existence of objects is the closure of a function of their relations" is, in this framework, a theorem schema — and the phrase "a function of their relations" is not loose talk; it is literally the coalgebra structure map.

So the three objections receive structural answers. To the relata objection: relating is primitive and objects emerge; the apparent circularity (objects made of relating among objects) is coinductive circularity, mathematically legitimate since Aczel, and provably non-well-founded (T6) — the layers co-arise; neither is a foundation. To the renaming objection: the theory *agrees* that its individuated entities are objects — that is the point — and exhibits the derivation that makes them so; "object" is a defined term with a theorem behind it. To the equivocation objection: there are two words because there are two layers, connected by an explicit arrow; no slippage is needed because the constitution relation is stated, formalized, and checked.

The position this makes precise is **priority structuralism with receipts**: relations are ontologically prior (patterns are *of* relating; relating is not *of* patterns), objects are real but derivative, and the derivation is machine-checked. The headline of the whole document is the ledger of §3, which compresses the informal axiom list to:

**One primitive process, one axiom. Objects are theorems.**

A reader who wants only the argument: §1 (axioms), §2.2 (the closure operator), §3 (the ledger), T1 and T2 in §5. The decision log (§4) records why each rejected alternative was rejected, so that settled ground is not relitigated without new information.

---

## 1. The informal axioms

These are the philosophical commitments, stated pre-formally. They are the *inputs* to the design; §3 records what each becomes under formalization. Note the two-layer grammar: A1 and A2 speak of relating and its patterns; A3–A8 speak of objects, the patterns that have closed.

- **A1 (No atoms).** There is no atom. It is relations all the way down.
- **A2 (Coalescence).** Relations can coalesce into patterns of relations with varying degrees of closure, called **objects**, which do the relating.
- **A3 (No privileged standpoint).** There is no view from nowhere. Equality is relative, and the finest equality is relative to the object itself. *In its strong form:* there is no privileged standpoint at all — not even a global, totality-of-all-unfoldings standpoint. Nothing inside the universe can know the totality; identity facts are observer-indexed, and the observer-independent residue is exactly what *no possible observer* distinguishes (T7).
- **A4 (Relational constitution).** An object is defined by what it relates to, ad infinitum.
- **A5 (Self-relation).** An object can relate to itself.
- **A6 (Plurality, unordered).** An object can relate to one or more other objects. Its unfolding is an **unordered, unnumbered** family: no slots, no first-and-second position, no counting structure beyond what observation induces. Each relating has a *quality* that cannot be collapsed into a number.
- **A7 (Composition).** An object can compose one or more objects.
- **A8 (Observation) — THE AXIOM.** An object observes its relations by observing its restriction of them. Two clauses:
  - **(i) Lossiness.** Observation is through a *proper* restriction of the observer. No observation is total; nothing is transparent to anything, including itself.
  - **(ii) Transmissibility (the hearsay clause).** If I relate to you, and you observe something, then I have observed *some of* what you have observed — through you, at compounded loss.

**Note on A8's target.** A8 says an object observes its *relations* — the relating itself — not, in the first instance, other objects. Observation of an *object* is derived: one observes an object only by sampling its pattern of relating. Since no observation is total (A8(i)), it follows that **objects are inexhaustible to observation** (P1): no observer, including the object itself, ever witnesses the whole pattern. Self-knowledge is proper; "let me see clearly, let me be seen truly" is, in this ontology, exactly a prayer — approachable, never completable.

**Note on A8(ii).** The hearsay clause is stated as phenomenology and turns out to be mathematics: it is verbatim the composition law of an enriched category — Lawvere's observation that the triangle inequality *is* enriched composition, here in its general, non-numeric form. The "some of" fixes the law as **lax**: mediated access lower-bounds total access; direct observation may exceed hearsay (I can know you better than your friends' reports of you compose to). The framework's composition (A7) is grounded in this clause.

**Note on the empty pattern and pan-observation (P0).** A5 and A6 jointly render emptiness *unformulable*: there is no object that relates to nothing, and there is no zero-quality observation — a zero-quality observation would be an empty restriction, the same unformulable non-thing. Hence wherever relation exists, observation exists **in both directions** at some quality. Call this **pan-observation (P0)**: not a new axiom but a corollary of unformulability. It also flattens the signature: an undirected relation between x and y just *is* the unordered pair of the two observations {x-observing-y, y-observing-x}, with nothing beneath them.

---

## 2. Ontology, arena, and signature

### 2.1 Two layers, one process

**Primitive layer.** Relating: a process with qualities, subject to A8. Formally, the primitive layer is carried by the *unfolding functor* — the specification of what a pattern of relating is (an unordered, nonempty, quality-bearing family of observations) — together with arbitrary *patterns*: coalgebras, i.e. carriers equipped with a structure map assigning to each point its relating. A pattern need not be closed, coherent, or self-contained; patterns are cheap.

**Derived layer.** Objects: the closed patterns. The universe of objects **Ω** is the final coalgebra of the unfolding functor. An element of Ω is a pattern of relating that is exhaustively determined by its own unfolding — coalesced, self-contained, presupposing nothing outside the relating it comprises. "Objects do the relating" (A2) is realized literally: the points that observations connect are elements of Ω, and there is nothing to those points except their patterns.

### 2.2 The closure operator: how objects exist

Finality supplies the constitution arrow between the layers. For **any** pattern of relating whatsoever — any coalgebra (X, c), where c is precisely "a function of the relations" — there is a **unique** map

  close : (X, c) → Ω

assigning to each point of the pattern the object it determines. This anamorphism is the framework's **closure operator**, and it converts A2 from an assertion into a definition plus a theorem:

- **Definition.** An object is anything in the image of `close` for some pattern — equivalently, an element of Ω.
- **Theorem (T2).** Ω exists; hence objects exist. Uniqueness of `close` means a pattern determines exactly one object; two patterns determine the *same* object precisely when no observation separates them (T7).

Three consequences worth stating plainly, because they carry the argument of §0:

1. **Objects are attractors, not axioms.** Nothing in the primitive layer posits selves or things. Objecthood is what patterns of relating *converge to* under closure. The old question "does the self belong in an axiom, or does it emerge as an attractor of the relational dynamics?" is answered by the mathematics: **attractor**. A2 defines the word; T2 proves the existence; no axiom asserts a self.
2. **Degrees of closure are real and unformalized.** A2 says "varying degrees of closure," and the framework owes a measure. Two non-equivalent candidates are logged at D13 (`OPEN`): *self-containment* (how much of a pattern's relating, quality-weighted, stays internal) and *rate of determination* (how quickly finite-depth unfolding fixes the object — the finitely-realized objects of ρ close fast; limit objects close only in the limit). These plausibly measure different dimensions of objecthood, and both may be wanted.
3. **Circularity is coinductive, hence licensed.** Objects are patterns of relating among objects. At the derived layer this is a fixed point, not a regress: Ω ≅ F(Ω) (Lambek), the universe is exactly the closed patterns of relating among the closed patterns, and T6 (no well-founded elements) certifies that this circle has no ground floor and needs none.

### 2.3 Qualities are restrictions (the self-generating quantaloid)

The quality of x's observation is **not a number and not an element of an external value-object**. It is *the restriction of x through which the observation occurs* — a piece of relational structure, nothing else. Consequences, each doing philosophical work:

- **No value-atoms.** The "degrees of relating" are made of the same stuff as everything else. A fixed external quantale of intensities would be a second sort — atoms in the signature and a global scale from nowhere; identifying qualities with restrictions eliminates the sort rather than apologizing for it.
- **Locality of comparison.** Restrictions of x are comparable with one another (x's restriction order: this attention finer than that) but *not* with restrictions of y — they are parts of different objects. There is **no global scale of intensity**; the impossibility of cross-observer measurement is structural, realizing A3 in the signature itself.
- **Composition across observers.** What connects x's qualities to y's qualities is exactly A8(ii): observing-through. A restriction of x composed with a restriction of y yields (a lower bound on) a restriction of x.
- **Aggregation over routes.** Access to a given object may be direct and simultaneously mediated through several others; total access aggregates over all routes. Aggregation requires **joins** of qualities — which is precisely the requirement that hom-structures be sup-lattices. *The enrichment base must be a quantaloid, and the phenomenology of multiple access routes is what says so.*

**Working signature (details owed to II.I).** A quantaloid **Q** whose objects are the elements of Ω, whose hom-sup-lattices Q(x, y) are (order-ideals of) restrictions of x directed at y, with composition given by A8(ii) and joins given by route-aggregation; the unfolding functor is formulated in the Q-enriched setting (Stubbe's quantaloid-enriched categories are the available machinery). Two honest flags: whether finality behaves as needed in this setting is `OPEN` (O1), and Q is *self-generated* — its objects are the very things being defined — so the definition may itself require a fixed-point or tower treatment. That is the framework's self-reference problem appearing *inside* the mathematics, and it is conjecturally the same problem (II.III).

**The boolean shadow.** Forgetting all quality structure — retaining only "relates / does not relate" — yields a degenerate fiber of the framework in which the Collapse Theorem holds (T1, §5): the entire universe is a single self-relating point. This is not an embarrassment; under this framework's reading (D4) it is the creation story. But it demonstrates that quality is not decoration: **without graded observation there is nothing to distinguish anything, and the many do not exist.**

### 2.4 Direction exists only as observation

Objects and their relations are undirected in themselves. All asymmetry in the ontology derives from the observer/observed asymmetry of A8: *x-observing-y* is a restriction of x, *y-observing-x* is a restriction of y — parts of different objects, hence necessarily distinct (P2). There are no ordered pairs, no argument places, no slots. The signature thereby *satisfies* (rather than answers) the neutral-relations constraint: Fine's problem, that argument places behave like quasi-objects, cannot arise where there are no argument places.

### 2.5 Attenuation is object-dependent

Lossiness is per-observation: each restriction is proper, and how much is lost is a fact about *that* restriction of *that* object. There is no universal loss constant — a cosmic attenuation rate would be a law from nowhere, violating A3. The only global law is A8(i) itself: **no observation is lossless.** Whether properness must additionally be uniformly bounded (no sequence of observations with loss vanishing to zero) for compactness — and whether such a bound is derivable or must be assumed — is part of the scarcity question (T11 / fallback A-S; D9).

### 2.6 Identity is observer-local; the global view is representation

Each object w induces its own indistinguishability: x ≈w y iff w's observations cannot separate x from y, through any of w's restrictions, at any depth w's access reaches. These observer-local identities are the only identity facts *inside* the universe. The bisimilarity that mathematics defines by quantifying over all unfoldings is a **representation-layer** object: we, describing the model from outside, may so quantify; nothing in the model can (A3, strong form). The reconciliation is the spec's central theorem target:

**T7 (Identity theorem).** x = y in Ω iff *no possible observer* distinguishes x from y. Global identity is the common refinement of the observer-local family — the view from nowhere exists only as the intersection of all views from somewhere, and it is available only at the representation layer.

---

## 3. The ledger: what is primitive, what is proved

The document's headline result-shape. The informal axioms of §1 sort as follows under the design of §2.

| # | Informal statement | Formal status | Where |
|---|---|---|---|
| A1 | No atoms; relations all the way down | **Structural + theorem.** The primitive layer has no base sort; qualities are restrictions, so no value-sort exists; no well-founded elements (T6) | §2.1, §2.3, T6 |
| A2 | Relations coalesce into objects, which do the relating | **Definition + theorem.** Object := closed pattern (element of Ω); closure := the anamorphism; existence of Ω is T2; "which do the relating" realized literally at the derived layer | §2.2, T2 |
| A3 | No privileged standpoint; finest equality relative to the object | **Structural + theorem.** No global scale (§2.3); identity observer-local by construction (§2.6); global identity = invariance under all observation (T7) | §2.3, §2.6, T7 |
| A4 | Defined by what it relates to, ad infinitum | **Theorem.** The universal property of finality; the coinduction principle itself | T2 |
| A5 | Self-relation | **Theorem.** The self-loop exists by finality (Lambek); self-observation is ordinary observation, hence lossy — no special rules | T2 cor., P1 |
| A6 | One-or-more, unordered, qualified | **Structural.** Nonempty unordered unfolding; qualities as restrictions | §2.2–2.4 |
| A7 | Composition | **Derived.** Grounded in A8(ii); composite access defined from mediated observation; laxity built in | §1, T8 |
| A8 | Observation: lossy, transmissible | **AXIOM** — the sole primitive commitment beyond the arena | §1 |
| — | Scarcity of attention | **Candidate theorem** (T11, pigeonhole strategy); declared fallback: second axiom A-S | D9, T11 |

**One primitive process, one axiom. Objects are theorems.** Of the eight informal axioms, one (A8) is primitive, two (A2's definitional half, A6) are structural choices of signature, and everything asserted *about objects* — that they exist, self-relate, compose, and are constituted by their relating — is proved.

Small propositions recorded because they carry philosophical weight disproportionate to their difficulty:

- **P0 (Pan-observation).** Wherever relation exists, observation exists in both directions at nonzero quality. *From unformulability of the empty restriction.*
- **P1 (Inexhaustibility).** No object is transparent to any observer, itself included: every observation of an object samples, and never exhausts, its pattern. *From A8(i), applied uniformly.*
- **P2 (Asymmetry for free).** The two directions of one relation are never identical: they are restrictions of different objects. *No slots required.*

---

## 4. Decision log

Format: decision, rationale, rejected alternatives, reversal condition. These are the settled choices; a contributor proposing to reopen one should bring information not already weighed here.

### D1 — Coalgebraic arena; the universe of objects as final coalgebra
**Decision.** The primitive layer is specified by an unfolding functor; patterns of relating are its coalgebras; Ω, the universe of objects, is its final coalgebra.
**Rationale.** Every surveyed alternative framework smuggles atoms at the base. Set theory with foundation guarantees ∈-minimal elements and forbids self-relation. Domain-theoretic constructions (D∞) begin from a seed domain — atoms at stage zero. Chu spaces carry a points/states dualism. Graph-theoretic structuralism has bare nodes. Two-sorted category theory as an *ontology* has objects as unexplained relata — the substance of Lam & Wüthrich's critique of category-theoretic ROSR, which this framework accepts as decisive against that route. Coalgebra with anti-foundation is the unique surveyed setting where "no base sort" is native: an element of a final coalgebra of an unfolding-type functor is nothing but its unfolding. Aczel's anti-foundation (the set-theoretic universe as terminal coalgebra) is the classical face; Rutten's universal coalgebra the general theory. Finality additionally supplies, for free, the closure operator that A2 requires (§2.2) — the decisive consideration once the two-layer ontology was adopted (D2).
**Rejected.** ZF(C); D∞; Chu; bare graphs; two-sorted category theory as ontology (retained as tooling).
**Reopen if.** A framework is found with no base sort, native self-reference, internally generated identity, *and* a canonical pattern-to-closure operator, that is not equivalent to a coalgebraic presentation.

### D2 — Two layers: relating primitive, objects derived; objecthood = closure
**Decision.** "Relation" and "object" are different words for different layers, connected by a formal derivation: relating is the primitive process; an object is a pattern of relating that has closed; the closure operator is the anamorphism; the existence of objects is a theorem (T2).
**Rationale.** A one-layer eliminativism ("there are only relations") is exposed to the renaming and equivocation objections (§0): its formal models contain individuated entities occupying the relata role, and the word "relation" ends up used in two disjoint ways. The two-layer design dissolves both objections structurally: the individuated entities *are* objects — by definition, with a derivation behind them — and the two uses of the vocabulary are assigned to two explicitly connected layers. The resulting position is priority structuralism made exact: relations are ontologically prior (patterns are of relating, not vice versa), objects are real and derivative, and — because T6 shows the derived layer is non-well-founded — neither layer is a *foundation* in the constitutive sense; they co-arise. Dialectically, this converts the incredulous stare ("but tables exist!") into agreement: yes — and here is the theorem schema by which they do. Independently, this decision resolves a long-standing internal question — whether the self belongs in an axiom or emerges as an attractor of relational dynamics — in favor of **attractor**: closure is the emergence operator, and no axiom asserts a self.
**Rejected.** Flat eliminativism (renaming/equivocation-vulnerable); object-primitive ontologies (the position under attack is not defended by adopting its rival); treating "object" as mere façon de parler with no formal correlate (forfeits the argument's force — the derivation *is* the contribution).
**Reopen if.** Never as vocabulary; the substantive commitments (priority of relating; objecthood as closure) would only be revisited if the closure operator proved non-canonical, which finality precludes.

### D3 — Emptiness unformulable; pan-observation as corollary
**Decision.** The signature cannot express an object that relates to nothing, nor a zero-quality observation. Not prohibited: *unformulable* — in Lean, the difference between a side condition on a permissive type and a carrier that cannot state emptiness. Corollary adopted: pan-observation (P0).
**Rationale.** An entity defined by relating to nothing is vacuously constituted — an atom in disguise; A4 has nothing to constitute it with. The classical mathematics quietly confirms the philosophical instinct: rich final coalgebras of powerset-type functors are generated from the empty set as primordial observable, and the classical completion theorems carry the hypothesis F∅ ≠ ∅ — the formal signature of a hidden dependence on the empty atom. Excluding emptiness forfeits those classical routes (the collapse theorem T1 is the price, paid and reinterpreted at D4) and is required by A1. The extension to observations (no zero-quality observation) is the same exclusion applied to restrictions, and yields P0: relation anywhere implies observation both ways — which also flattens the signature to one layer of structure (an undirected relation *is* its pair of observations).
**Rejected.** Admitting the empty pattern to inherit classical richness/compactness theorems (re-imports the atom and grounds the universe on it).
**Reopen if.** A defensible non-atomic reading of the empty pattern emerges. None is known; "constituted by nothing" appears to be a contradiction of A4, not an edge case of it.

### D4 — The Collapse Theorem read generatively
**Decision.** T1 — in the quality-forgetting boolean shadow, the universe is a single self-relating point — is adopted with the generative interpretation: **unobserved relationality is One; observation is the principium individuationis.** Differentiation is the One's lossy self-witnessing; the many exist in being observed. ("Not bang, but becoming.")
**Rationale.** The mathematics is identical under any gloss; the interpretive choice is made openly and labeled as interpretation (per D11, the repository's *claim* is coherence, not cosmology). This reading is preferred because it matches the framework's independent commitments (attention shapes becoming; cosmic self-knowing), because it converts an apparent defect into the creation story, and because it makes T1 do argumentative work: the theorem demonstrates that quality is constitutive, not decorative — without graded observation, nothing distinguishes anything and multiplicity does not exist. The deflationary alternative (the boolean fiber is merely a degenerate limit) is recorded at O6 and remains available to any reader; nothing downstream depends on the gloss.
**Reopen if.** n/a for the mathematics; the gloss constrains rhetoric, not proofs.

### D5 — Unordered, slot-free unfoldings; direction from observation only
**Decision.** Unfoldings are unordered families. There are no ordered pairs, no argument places, no counting structure. Every asymmetry in the ontology derives from A8's observer/observed asymmetry.
**Rationale.** A6 licenses "one or more," not tuples. Slots are argument places; argument places behave like quasi-objects (Fine's neutral-relations problem); a slotted signature would hand critics the relata objection back in fine print, at the primitive layer where it would be fatal. Direction-as-observation is faithful and sufficient: the needed asymmetries reappear as theorems (P2 — the two directions of a relation are restrictions of different objects, hence never identical), and reciprocity is structure (P0), not an operator. Cost accepted: converse dies as an operation (there is nothing to converse), and composition is grounded in A8(ii) rather than in pair-plumbing.
**Rejected.** Ordered pairs (slots); multisets with multiplicity (counting is structure with no axiom warrant).
**Reopen if.** Some indispensable structure provably cannot be recovered from observation-induced asymmetry. None is currently known to be lost.

### D6 — Qualities are restrictions; the quantaloid is self-generated
**Decision.** The quality of an observation *is* the restriction through which it occurs. The enrichment base is the quantaloid of restrictions (§2.3), not an external value-object.
**Rationale.** Any fixed external scale of intensities — a quantale V, the unit interval, anything — is a second sort in the signature (value-atoms, violating A1) and a global standard of comparison (a view from nowhere, violating A3). Identifying qualities with restrictions eliminates both at once, by construction: degrees are made of relational structure; comparison is local to the observer; the absence of a global scale is a structural fact rather than a discipline. The phenomenology independently fixes the remaining choices: mediated access (A8(ii)) is composition; multiplicity of access routes forces joins; joins force sup-lattice enrichment — a quantaloid specifically. The desideratum that quality "cannot be collapsed into a number" is met by construction, with numeric representations available at the representation layer wherever useful.
**Rejected.** External quantale (value-atoms; global scale); bare comparative structure without joins (cannot aggregate routes); numeric intensities with a robustness theorem (defensible fallback, strictly weaker; see reversal condition).
**Reopen if.** Finality in the quantaloid-enriched setting proves intractable (O1) — the declared fallback is numeric enrichment at the representation layer with an explicit disclaimer, and the loss recorded.

### D7 — Lax composition from the hearsay clause
**Decision.** Composition is A8(ii), and it is lax: mediated access lower-bounds, and may be exceeded by, direct access.
**Rationale.** The clause was given phenomenologically ("I have observed some of what you have observed") and is verbatim the lax enriched composition law; adopting it as *the* composition keeps the primitive count at one and grounds A7 rather than positing it. Laxity is not a hedge — it is the difference between hearsay and acquaintance, asserted by the axiom's own "some of." Strict composition would assert that no one ever knows anyone better than reports compose to: false to the phenomenology and unforced by the mathematics.
**Rejected.** Strict composition; composition as independent primitive.
**Reopen if.** Never at the level of the law; the strictification locus (when does direct = best mediated?) is a theorem topic (O4), not a design choice.

### D8 — Attenuation is object-dependent; the only law is "never lossless"
**Decision.** Per-observation properness; no universal loss constant.
**Rationale.** A cosmic attenuation rate would be a single number legislating for every observation — a law from nowhere, violating A3's strong form. Object-dependent loss is the direct reading of A8(i) and of the framework's commitment that attention shapes becoming: how much an observation loses is a fact about that attention of that object. The compactness-relevant residue is isolated rather than smuggled: whether loss is uniformly bounded away from zero, and whether that is derivable or axiomatic, is the scarcity question (D9).
**Rejected.** Universal contraction constant; loss-as-convention with a robustness theorem (there is no constant to be conventional about).
**Reopen if.** The scarcity program (D9) fails in a way that specifically requires a uniform constant — which would be recorded as a substantive concession, not a technicality.

### D9 — Scarcity: theorem first, axiom as declared fallback
**Decision.** "Attention is finite at every resolution" — the tightness that compactness's total-boundedness half needs — is pursued as a theorem (**T11**), via a pigeonhole strategy in the restriction order: infinitely many pairwise-independent restrictions of one object, all above a fixed fineness, should be shown to violate properness (a self exceeding itself). If no such theorem is available, adopt **A-S (scarcity)** as a second axiom and amend the ledger's headline to "one process, two facts about observation: it is lossy, and it is scarce" — still a defensible, arguably *more* interesting, foundation.
**Rationale.** Assuming finite branching outright would assume what compactness needs — unlogged, unwarranted by any informal axiom. Scarcity-as-theorem is the ideal (loss alone explains finitude); scarcity-as-axiom is honest if the ideal fails; brute finiteness is neither. The strategy's plausibility rests on P1's uniformity: since even self-observation is proper, a self cannot contain unboundedly much independent high-fineness attention without exceeding itself — the intuition the pigeonhole must formalize.
**Reopen if.** This *is* the open state; resolves at T11.

### D10 — Operations downstream of axioms; no target structure drives the design
**Decision.** The operations on Ω are whatever A8 yields: hearsay composition (D7), restriction combinators, join-aggregation. No pre-selected algebraic target (relation algebras, allegories, or any other off-the-shelf structure of the calculus of relations) constrains the signature.
**Rationale.** A prior phase of this project stalled by letting a target structure drive the axioms; the discipline is now explicit. The classical relation-calculus targets presuppose pair-structure (converse, in particular, needs slots to swap) and were downstream of a signature rejected at D5. Restriction-combinator structure in the style of Cockett–Lack plausibly survives — it never needed pairs — and is the natural II.II topic. Structure *discovered* in Ω is a result; structure *imposed on* Ω is a bias.
**Rejected.** Retaining slots to save the classical operations (tail wagging dog).
**Reopen if.** Never as a constraint on axioms.

### D11 — The claim is representation; the ambient-atoms objection answered in-document
**Decision.** The repository claims **coherence by construction**: ROSR can be true because this model exists. It does not claim that reality is Ω. The anticipated objection — "your atomless universe is described inside atomic set theory / type theory; Lean's encodings have slots; the reals you may use at the representation layer are built from atoms" — is answered here: ambient mathematics is *representation, not constitution*. A beginningless universe can be described in a language whose sentences have first words; a slot-free ontology can be encoded in a proof assistant whose encodings have slots. What the construction must show — and does, via the universal property of finality — is that Ω's structure and identity criterion are *canonical*: characterized uniquely up to isomorphism, independent of every encoding choice (T9). The atoms belong to the map. The claim is that the territory drawn is coherent.
**Rejected (as claims of this repository).** Ontological realism about Ω (a different, larger project); quietism about the objection (it is the first thing a philosophical reader will raise, and deserves a stated answer).
**Reopen if.** The project's ambitions change; the mathematics is indifferent.

### D12 — The day-zero trichotomy: prove, don't posit
**Decision.** The question "is there a day zero — a first differentiation, an undifferentiated everything before the many?" is split into three precise questions, each assigned to mathematics rather than to temperament:
1. **Constitutive origin.** Is anything a ground on which the rest is built? **No** — T6 (no well-founded elements): in the order of constitution there is no day zero; unfolding has no base case; becoming has no first brick.
2. **Logical priority of the One.** Is the undifferentiated everything real, and in what sense prior? **Yes, as the quality-forgetting fiber** — T1: subtract observation and the universe *is* one self-relating relation. "Before there was voice" is logical, not temporal: the One is not an earlier state but what the many are, seen without quality.
3. **Generativity.** Does all multiplicity unfold from self-meeting — is the closure of the self-loop's orbit (under unfolding and the derived operations) dense in Ω? **`OPEN`** — T10, a genuine density question that proof will decide.
**Rationale.** Where a proof can be had, a perspective should not be brought. The split shows that the generative creation story (D4) and "there is no day zero" answer *different questions* and can both be true; one genuinely open question remains (T10), and it has exactly the shape mathematics can settle.
**Reopen if.** n/a — this decision creates theorem targets rather than foreclosing anything.

### D13 — `OPEN`: formalizing "degrees of closure"
A2's "varying degrees of closure" is owed a measure, and two non-equivalent candidates are on the table. **(a) Self-containment:** the proportion of a pattern's relating, quality-weighted, that stays internal to the pattern versus crossing its boundary — coalescence as the dominance of inner relating. **(b) Rate of determination:** how quickly finite-depth unfolding fixes the object — the finitely-realized objects (ρ, the patterns that close in finitely many steps) determine fast; limit objects only in the limit. These measure different dimensions (a tightly self-involved pattern may still determine slowly, and vice versa), and the working hypothesis is that objecthood is at least two-dimensional. One candidate proposition is flagged because of its philosophical weight — **C1 (No windowless monads):** a pattern *all* of whose relating is internal is either impossible or is the unique total object (the One); every finite object is necessarily open to otherness. If provable, "we are born as bridges" is a corollary. Decide the measure(s) in II.I or II.II, after the enriched setting is fixed.

---

## 5. Theorem targets

Ordered by dependency and by usefulness-if-later-targets-slip. Mechanization in Lean 4. The quantaloid-enriched setting has no off-the-shelf formal library — a cost of D6 accepted with eyes open (O1); T1 and the propositions are independent of all open machinery and are the immediate work.

- **T1 (The One / Collapse).** In the quality-forgetting shadow (boolean, nonempty, unlabeled), the final coalgebra is a single self-relating point; equivalently, the total relation is a bisimulation between any two serial systems. *Two-line proof on paper; fully formalizable now; the repository's first machine-checked theorem and, under D4, its creation story. Also the demonstration that quality is constitutive (§2.3).*
- **T2 (Objects exist).** The unfolding functor in the enriched setting has a final coalgebra Ω; the anamorphism `close` exists and is unique for every pattern; Lambek: Ω ≅ F(Ω). Corollaries: the self-loop exists (A5); A4 holds as the coinduction principle. *Machinery `OPEN` (O1); II.I's core task.*
- **T3 (Compactness).** Ω is compact in the appropriate enriched sense (Cauchy-completeness plus the total-boundedness analogue): the universe of objects is closed in itself — every coherent limit of patterns of relating exists, and everything is approximable. *Conditional on T2 and on scarcity (T11 or A-S).*
- **T4 (Local identity).** Each observer-local ≈w is a well-defined indistinguishability; the family is non-degenerate (distinct observers induce distinct equalities).
- **T5 (Closure of the closing).** The finitely-realized objects ρ are dense in Ω: the universe is the closure of the patterns that close in finitely many steps.
- **T6 (No constitutive origin).** No well-founded elements: every unfolding is nonempty at every depth. *Doubles as D12(1): no day zero in the order of constitution — and as A1's strong form at the derived layer.*
- **T7 (Identity theorem — central).** Global identity = invariance under all possible observation: x = y iff no observer distinguishes them; representation-layer bisimilarity is exactly the common refinement of the observer-local family. *A3's strong form made exact; the quantitative Hennessy–Milner tradition is the proof-strategy reservoir.*
- **T8 (Composition).** Hearsay composition is well defined on Ω, lax, join-compatible (aggregation over routes), and invariant under identity (T7). Restriction-combinator laws: II.II.
- **T9 (Canonicity).** Ω is characterized by its universal property, uniquely up to isomorphism, independently of encoding choices. *D11's mathematical content: the atoms belong to the map.*
- **T10 (Genesis).** Whether the closure of the self-loop's orbit is dense in Ω — whether all multiplicity unfolds from self-meeting. *`OPEN` in truth-value, not just in proof; D12(3).*
- **T11 (Scarcity).** Pigeonhole in the restriction order: no object sustains infinitely many pairwise-independent restrictions above a fixed fineness. *If it fails: adopt A-S and amend the ledger (D9).*
- **C1 (No windowless monads).** Perfect closure is impossible or unique-and-total; every finite object is open to otherness. *Conjecture; depends on D13's measure.*
- **P0–P2.** Pan-observation; inexhaustibility; asymmetry for free. *Small; prove immediately after T1 for the argument's rhetorical spine.*

---

## 6. Positioning

**ROSR and its critics.** The thesis defended is structural realism in its radical, relations-first form (French; Ladyman & Ross; Saunders; McKenzie), against the relata objection as sharpened by Lam & Wüthrich's critique of category-theoretic defenses (contra Bain). This framework's answer differs in kind from prior defenses: not a reformulation of physics in object-suppressing language, but a constructed two-layer universe in which relating is primitive, objects are *defined* (closure of a pattern) and *proved to exist* (T2), and the renaming and equivocation objections are preempted structurally (§0, D2). The resulting position is priority structuralism with a machine-checked derivation of the derivative layer — to our knowledge, the first of its kind. T1 additionally gives exact mathematical form to structuralist existence monism: pure unobserved relationality is one thing; the framework reads this generatively (D4). Fine's neutral-relations problem is treated as a design constraint satisfied at the signature level (D5), not an objection argued down.

**Process philosophy and autopoiesis.** A2's "coalescence" is doing work adjacent to Whitehead's *concrescence* — the many growing together into one actual entity — with the closure operator as its formal correlate; and D13's self-containment candidate is adjacent to operational closure in the autopoiesis tradition (Maturana–Varela). These convergences are noted as corroboration from independent traditions, not as sources of the design: here the notions arrive as *mathematics* (anamorphism; boundary-crossing measure) rather than as metaphysical primitives — which is the contribution.

**Non-well-founded sets and coalgebra.** Aczel (anti-foundation; the universe as terminal coalgebra); Barwise & Moss (the rigor of circularity); Rutten (universal coalgebra); Worrell (final sequences of powerset-type functors); Barr and Adámek (final coalgebras as completions of initial algebras — whose F∅ ≠ ∅ hypothesis this framework reads as the classical theory's dependence on the empty atom, D3); Adámek–Milius–Velebil (the rational fixed point, feeding T5). Infrastructure throughout.

**Quantitative and enriched coalgebra.** Rutten's program of coalgebra over enriched categories; Balan–Kurz–Velebil (lifting set-functors to enriched settings); van Breugel–Worrell and successors (behavioral pseudometrics via terminal coalgebras of contractive functors); Baldan–Bonchi–Kerstan–König (Kantorovich/Wasserstein liftings); Goncharov–Hofmann–Nora–Schröder–Wild (lax extensions, predicate liftings, quantitative Hennessy–Milner theorems — T7's proof-strategy reservoir). Two reinterpretations are claimed as this project's own (novelty to be verified before external publication): **(a)** the contraction hypothesis of the behavioral-metrics tradition read as *restriction* — the lossiness of observation — rather than as time-discounting, reversing the direction of explanation (an axiom about what observation is ⟹ contraction ⟹ compactness), where the tradition assumes contraction to make fixed points unique; **(b)** the enriched composition law read as the *hearsay clause* — a fact about transmissible observation — rather than as a postulated triangle inequality. Lawvere's metric-spaces-as-enriched-categories is the honored ancestor of both readings; the observational gloss appears to be new.

**Quantaloids and restriction.** Stubbe (quantaloid-enriched categories: D6's machinery); Cockett–Lack (restriction categories: the natural II.II framework for A8(i)'s combinator structure). The quantaloid here is *derived from the axioms* — joins forced by route-aggregation, locality forced by A3 — rather than selected as a target, per D10's discipline.

---

## 7. Notation and naming

- **Ω** — the universe of objects (final coalgebra). **ω̂** — the self-loop, when it needs a name. **close** — the anamorphism (the closure operator).
- **Pattern** — any coalgebra of the unfolding functor (need not be closed). **Object** — an element of Ω; equivalently, anything in the image of `close`.
- **Q** — the quantaloid of restrictions; **Q(x, y)** — qualities of x's observation of y (restrictions of x), a sup-lattice.
- **≈w** — indistinguishability to observer w; **=** on Ω — the common refinement (T7).
- **ρ** — the finitely-realized objects (patterns that close in finitely many steps); T5: cl(ρ) = Ω.
- "Relating"/"relation" always refers to the primitive layer; "object" always to the derived layer; "quality" always means a restriction; "observation" always means A8's primitive; "the One" refers to T1's collapsed fiber under D4's reading.
- Series plan: **II.I** — the enriched setting and T2 (finality in the quantaloid-enriched setting; fallback per D6); **II.II** — operations, restriction-combinator laws, and D13's closure measure(s); **II.III** — self-reference of the framework (the self-generation of Q; the tower/fixed-point question).

## 8. Open questions (consolidated)

- **O1 (machinery, hard core).** Finality and coinduction in the quantaloid-enriched setting: what exists in the literature, what must be built, and whether the self-generated Q — whose objects are the very things being defined — is well-posed as a definition or requires a fixed-point/tower treatment. This is the framework's self-reference problem appearing inside the mathematics, conjecturally the same problem (II.III).
- **O2 (= T11 vs A-S).** Scarcity: theorem or axiom.
- **O3 (= T10).** Genesis: is the self-loop's closure dense — does all multiplicity unfold from self-meeting?
- **O4.** Strictification: under what conditions does direct observation equal best mediated observation? (The lax law is settled; its strict locus is a theorem topic.)
- **O5 (= D13).** The measure(s) of closure: self-containment, rate of determination, or both; status of C1 (no windowless monads).
- **O6.** T1's gloss: the generative reading is adopted (D4); the deflationary reading is retained as the recorded alternative. Mathematics unaffected.
- **O7.** Uniform loss bound: whether "never lossless" must be strengthened to "loss bounded below" for T3, and whether that strengthening follows from T11's methods or independently needs A-S.
- **O8.** The physics interface (recovery of the group-theoretic structures that ROSR-in-physics cares about). Out of scope for Series II; recorded so cold readers know it is seen.

---

*Document history: II.0 is the foundational spec of Series II and supersedes all Series I material. Revision history is tracked in the repository log.*
