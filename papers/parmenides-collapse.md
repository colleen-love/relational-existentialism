# The Parmenides Collapse: A No-Go Theorem for Relations Without Relata

**Colleen Love**

*First draft. Copyright © 2026 Colleen Love. All rights reserved.*

*Status note: this is a working draft. The formal claims are machine-checked and stable. The related-work positioning is grounded in the source-quoted literature sweep recorded in `literature-review.md`; citation metadata was hand-verified in rounds 3 through 5 of that file, and Eva 2016 has been read in full. Remaining before submission: the specialist sanity pass on the mathematics, and the minimal artifact repository and DOI for the verification footnote (which is being retained).*

---

## Abstract

Eliminativist ontic structural realism holds that the world is structure all the way down: relations without relata, or at least without relata that are anything over and above their relational roles. This paper proves an impossibility theorem for a natural formal precisification of that view. Model a purely relational world as a coalgebra of the bounded powerset functor, so that a thing simply is its outgoing relating and nothing else. Say the world is *behaviorally identified* when structurally indiscernible things are identical (bisimilarity implies equality), *atomless* when no thing's relating ever bottoms out in something that relates to nothing, and *plural* when it contains at least two things. The theorem: no such world is behaviorally identified, atomless, and plural. Purely relational, atomless universes hold at most one thing. We call this the Parmenides collapse, since it recovers, as a theorem about arbitrary relational structures, the Eleatic conclusion that a world of pure undifferentiated being is One. Each hypothesis is shown to be load-bearing by an explicit countermodel, and complete proofs, all short, are given in an appendix. We argue that the theorem sharpens the central dilemma for ontic structural realism: an eliminativist about relata must either embrace existence monism or admit a distinction that the relating itself cannot carry, and we show that the formalism can classify such a distinction as exogenous while remaining provably silent on whether it is given or chosen.

---

## 1. Introduction

Ontic structural realism (OSR) began as an epistemological modesty and became a metaphysical ambition. In its eliminativist or "radical" form, the view holds that structure is ontologically fundamental: there are relations without relata, or relata are nothing but nodes in a relational web, individuated entirely by their relational roles (French & Ladyman 2003; French 2010; Ladyman & Ross 2007). The standard objection is ancient and simple: relations need relate *something*, and if the relata have no identity apart from their relations, nothing individuates them, so plurality itself is in danger (Chakravartty 1998 gives the canonical formulation: one cannot intelligibly subscribe to the reality of relations without commitment to some things being related). The standard reply is equally well developed: weak discernibility. Even qualitatively identical objects can be discerned by an irreflexive relation holding between them, as Saunders argued for fermions, and this is claimed to be individuation enough (Saunders 2006; Muller & Saunders 2008; Muller & Seevinck 2009).

This paper changes the terms of that exchange by proving a theorem. Rather than asking whether relations can discern, we ask what follows if a world genuinely satisfies the eliminativist's own commitments, formalized without shortcuts, and we show the answer is: at most one thing exists.

The literature has anticipated this outcome informally without ever having it as a result. Esfeld and Lam, surveying the debate, describe the standing objections to eliminativism as informal (metaphysical, empirical, logical) and explicitly decline to rule out the coherence of relations-without-relata a priori; their own moderate structural realism accepts a numerical plurality of related objects as a primitive posit precisely because they do not see how relational structure could deliver it. And the same authors describe a "super-holist" scenario on which, entanglement being generic, there is fundamentally only one object: a Spinozistic monism under which structural realism would fail as fundamental ontology. The theorem below converts that anticipation into mathematics: plurality really is undeliverable from plain atomless relating, and the collapse to the One really is where the eliminativist package lands.

The theorem is stated and proved for coalgebras of the bounded powerset functor, a standard mathematical home for "systems that are nothing but their transitions." Three conditions formalize the eliminativist package:

1. **Plainness.** The world is a bare coalgebra: a carrier X and a map `dest : X → P_κ(X)` assigning to each thing the set of things it relates to. There are no labels, no intrinsic properties, no coordinates. All structure is relational structure.
2. **Behavioral identity.** Structurally indiscernible things are identical: every bisimulation on the world is contained in equality. This is the structuralist identity criterion taken at full strength; a thing is exactly its relational unfolding.
3. **Atomlessness.** No thing's relating ever bottoms out: every thing relates to something, hereditarily. There is no ground floor of relata that just sit there, unrelating. (We write this condition SHNE, for self-hereditarily non-empty, following the formal development.)

**Theorem (the Parmenides collapse).** No plain coalgebra is behaviorally identified, atomless, and plural. Formally: for every `dest : X → P_κ(X)`, it is not the case that (behavioral identity) and (every x is SHNE) and (there exist x ≠ y).

The proof is short once the right lemma is found, and the lemma is the philosophical heart of the paper: *on any plain coalgebra, the relation "x and y are both atomless" is itself a bisimulation.* Pure relational unfolding, if it never hits bottom, is featureless; any two never-bottoming things are structurally indiscernible, because there is nothing left for a difference to consist in. Behavioral identity then collapses them into one. Atomless purity is qualitative identity, and structuralist identity turns qualitative identity into numerical identity. The Eleatic One falls out as a corollary.

Three features distinguish this from an informal collapse argument of the kind the OSR literature has traded in prose:

First, **each hypothesis is proved load-bearing by an explicit countermodel**, so the theorem is not a definitional sleight of hand. Drop atomlessness and there is a behaviorally identified plural world with a leaf (a thing that relates to nothing): the empty node grounds difference, exactly as the traditional relata-theorist expects. Drop plainness and a two-element labelled world survives: a label is precisely a non-relational distinction. Drop behavioral identity and a plural world of two indiscernible loops survives: plurality is saved by primitive numerical difference, in either its haecceitistic or its structural-primitivist reading, exactly what the eliminativist forswears. The three escapes from the theorem are the three classical positions in the debate, recovered as the three ways of negating a hypothesis.

Second, **the theorem is fully general.** It quantifies over every carrier at every cardinal bound κ. Nothing depends on finiteness, on a chosen example, or on a particular construction. This matters because collapse worries in the OSR literature are usually pressed against particular toy structures and answered by exhibiting other toy structures; the theorem closes that loop.

Third, **the proofs are elementary and given in full.** Nothing is deferred to the reader's trust: the engine lemma is four lines, the countermodels are two-element structures whose properties can be checked by inspection, and Appendix A contains complete proofs of every numbered claim.[^lean]

The paper proceeds as follows. Section 2 motivates coalgebras and bisimulation as the right formal home for eliminativist OSR and states the three conditions precisely. Section 3 states the theorem, sketches the proof, and presents the countermodels. Section 4 defends the adequacy of the formalization: it addresses weak discernibility directly, arguing that weak discernibility is a claim *about* certain structured worlds while behavioral identity is the identity criterion the eliminativist is committed to; and it confronts the consensus that set theory is no proper home for eliminativism, showing that the world of the theorem is native to the category of sets and relations, that its hypotheses are categorical properties, and that its conclusion is carrier-free. Section 5 locates the mathematics honestly with respect to known facts about non-well-founded sets and final coalgebras: the collapse phenomenon has citable kin, including a published instance, and we state precisely what is and is not new here. Section 6 draws the consequences: the eliminativist's live options are existence monism or the admission of an exogenous distinction, and we prove a supplementary result about that distinction: the formalism can detect that it is not carried by the relating, but provably cannot distinguish whether it is given or chosen. Section 7 concludes. Appendix A gives the proofs.

[^lean]: All results in this paper, including those in the appendix, are additionally machine-verified in Lean 4 against Mathlib, resting on no axioms beyond Lean's standard classical triple; the artifact is available at [repository/DOI to be inserted]. We rest nothing on this: the printed proofs are complete, and the checker cannot certify the one thing a reader should scrutinize, namely whether the definitions capture the philosophy. That argument is Section 4.

## 2. The formal home: worlds as coalgebras

### 2.1 Why coalgebras

A formalization of "relations without relata" must walk a line. If the model gives objects intrinsic features, it has smuggled in what the eliminativist denies. If it gives them nothing at all, there is no model. The coalgebraic resolution is that an object *is* exactly one datum: the set of objects it relates to. A world is a pair (X, dest) with `dest : X → P_κ(X)`, where P_κ is the powerset functor bounded at cardinal κ (the bound ensures the mathematics is well behaved; κ can be as large as one likes, and nothing in the paper depends on its value).

This is not an exotic choice. Coalgebras of powerset-like functors are the standard semantics for transition systems, for non-well-founded sets, and for Kripke frames. Their canonical notion of indiscernibility, bisimilarity, is the accepted formalization of "same observable structure" across computer science and modal logic. When the eliminativist says an object is its relational role, the coalgebraist has a precise paraphrase: an object is its behavior under `dest`, and two objects have the same role exactly when they are bisimilar.

We stress what the carrier X is and is not. The elements of X are not relata in the traditional metaphysical sense, bearers of intrinsic natures. They are positions: bare indices whose entire content is given by `dest`. A plain coalgebra with behavioral identity is exactly a world in which positions with the same relational content are the same position. This is, we will argue in Section 4, the strongest honest reading of "relata are nothing over and above their relational roles."

### 2.2 The three conditions

**Plainness** is built into the signature. `dest` lands in P_κ(X), the *unlabelled* bounded powerset. A labelled variant would be `dest : X → L × P_κ(X)` for some label object L; the countermodel in Section 3.3 shows exactly what labels buy, namely everything, which is why the eliminativist cannot have them.

**Behavioral identity.** A relation R on X is a bisimulation when related states have matching unfoldings: if R(x, y), then everything in `dest x` is R-related to something in `dest y` and conversely. The world is *behaviorally identified* when every bisimulation is contained in equality. Equivalently: bisimilar implies identical. In the non-well-founded set theory literature this property is called strong extensionality, and it is precisely the identity criterion that anti-foundation set theories adopt as an axiom.

**Atomlessness.** Call x *hereditarily non-empty* (SHNE) when its unfolding never reaches an empty stage: `dest x` is non-empty, everything in `dest x` is hereditarily non-empty, and so on, coinductively. Formally SHNE is defined as a greatest fixed point, so it expresses genuine every-moment atomlessness rather than atomlessness up to some stage. An *atom*, in this paper, is a thing with empty relating: a leaf, a terminus, something that is in the world but does not relate. Atomlessness says there are no leaves anywhere in anyone's hereditary unfolding: the world is relating all the way down.

**Plurality** is the bare claim that some x and y are distinct.

Each condition is a commitment the eliminativist has actually made. Plainness is "structure is all there is." Behavioral identity is "same role, same thing," which is what individuation by relational role means when it is not hedged. Atomlessness is "no relata beneath the relations": the denial of a ground floor of intrinsically constituted individuals. Plurality is the datum: there is more than one thing. The theorem says the four cannot be had together.

## 3. The theorem

### 3.1 The engine

**Lemma (the collapse engine).** On any plain coalgebra (X, dest), the relation "x is SHNE and y is SHNE" is a bisimulation.

*Proof sketch.* Suppose x and y are both hereditarily non-empty and take any u in `dest x`. We must find v in `dest y` with u, v both SHNE. Since y is SHNE, `dest y` is non-empty; pick any v in it. Since x is SHNE and u is in `dest x`, u is SHNE; since y is SHNE and v is in `dest y`, v is SHNE. So u and v stand in the relation, and the matching condition holds. The converse direction is symmetric. ∎

The proof is four lines, and its brevity is the point. The relation "both atomless" makes no use of *which* things x and y relate to, because atomlessness gives it nothing to use: any successor of an atomless thing is as good as any other, since all anyone can ask of a successor is that it, too, never bottoms out. In a plain world, downward difference is the only difference there is, and atomlessness guarantees the descent never finds any.

**Corollary.** In any plain coalgebra, any two SHNE states are bisimilar.

### 3.2 The theorem

**Theorem (Parmenides collapse).** For every plain coalgebra `dest : X → P_κ(X)`: it is not the case that dest is behaviorally identified, every state is SHNE, and there exist two distinct states.

*Proof.* By the corollary, any two states are bisimilar; by behavioral identity they are equal; so X is a subsingleton, contradicting plurality. ∎

The theorem has a static form, concluding from the first two hypotheses alone that the carrier has at most one element (Appendix A.2). There is also a dynamic sharpening: on the final coalgebra, where behavioral identity holds by construction, all *productive* threads (histories that never bottom out) are not merely bisimilar but literally equal, and equal to the canonical self-looping state Ω (Appendix A.4). A purely relational atomless history is unique: there is exactly one way to relate forever without ground, and it is the One relating to itself.

### 3.3 The strip test: every hypothesis is load-bearing

A no-go theorem earns its keep by the failure of its weakenings. Each hypothesis, dropped, admits an explicit plural countermodel, and each countermodel is a recognizable philosophical position.

**Drop atomlessness: the leaf world (`leafCoalg`).** Two states; one relates to the other; the other relates to nothing. This world is plain, behaviorally identified, and plural. The empty node is discernible from the non-empty node by its relating alone, and everything downstream inherits discernibility from it. This is the traditional picture: a ground floor of atoms (here, one atom) from which all difference flows. The theorem does not refute atomism; it prices it. Difference is available exactly where the relating bottoms out.

**Drop plainness: the labelled world (`labelLoop`).** Two states, each relating only to itself, carrying distinct labels. Behaviorally identified over the *labelled* functor, atomless, plural. A label is a coordinate that the plain relating does not carry; with labels, plurality is trivial. This is the moderate structuralist's world, and the countermodel makes the cost explicit: the labels are doing the individuating, and they are not relational structure. (Section 6 returns to what a label is, semantically rather than syntactically.)

**Drop behavioral identity: the two-loop world (`twoLoop`).** Two states, each relating only to itself, no labels. Plain, atomless, plural, and *not* behaviorally identified: the total relation is a bisimulation not contained in equality. The two loops are structurally indiscernible yet distinct, and their difference has no discernible ground. This horn has two philosophically distinct occupants, and the theorem is neutral between them. One is haecceitism: primitive thisness intrinsic to each loop (Keranen's line). The other is structural primitivism: identity and difference taken as components of the structure itself, on a par with its relations, a position Leitgeb and Ladyman defend for exactly such cases (their edgeless two-node graph is this countermodel's twin) while explicitly rejecting haecceities, since permuting the two loops yields the same structure, not a new one; Shapiro and Ketland hold neighboring views. This world is consistent; the theorem does not rule it out. But on either reading it is precisely the world the eliminativist structuralist cannot claim, because admitting it concedes that identity and relational role come apart, which is the denial of the view. What the theorem adds to the existing debate about such structures is the price list: this is the *only* atomless plural option, and it costs the identity criterion.

The three countermodels triangulate the theorem. Atoms, labels, or haecceities: pick one, and plurality is cheap. Refuse all three, and plurality is gone. That trilemma, we take it, is the exact logical geography of the individuation debate in OSR, now with each region certified inhabited or empty by proof.

## 4. Adequacy: is behavioral identity the structuralist's criterion?

The theorem is only as interesting as its hypotheses are faithful. The load falls on behavioral identity, and the objection will come from the weak discernibility literature, so we take it head on.

### 4.1 The weak discernibility reply, and why it does not touch the theorem

Saunders and Muller argued, for quantum cases, that numerically distinct indiscernibles can be *weakly discerned*: an irreflexive relation holds between them that neither bears to itself, and this suffices for a defensible form of the identity of indiscernibles. Stated at its proved scope: Muller and Saunders discern any finite assembly of similar fermions, in all admissible states, in finite-dimensional Hilbert spaces, by permutation-invariant categorical relations; Muller and Seevinck extend the result in two ways, to bosons in finite dimensions and to infinite-dimensional Hilbert spaces for all elementary particles; Caulton later argued the original discerning relations relied on permutation-non-invariant quantities and exhibited symmetric replacements, so the program stands with repaired relations. Whatever its merits in quantum mechanics, note the logical shape of the reply: it *exhibits worlds* in which relations discern. It is an existence claim about certain structures.

The Parmenides collapse is a universal claim about a *class* of structures characterized by an identity criterion. The two do not compete; they pass through each other, and where they meet is instructive. In the two-loop countermodel, is there an irreflexive relation weakly discerning the loops? Over the plain signature, every relation definable from the structure is invariant under the swap automorphism, and the theorem's engine shows that bisimilarity, the finest structurally available equivalence, already identifies them. Weak discernment of the two loops requires a relation that the plain relating does not carry. The weak discernibility strategy, applied to a plain atomless world, must therefore import its discerning relation, and an imported relation is a label in the semantic sense of Section 6. The strategy is not wrong; it is a way of *occupying the labelled-world horn* of the trilemma while describing it in relational vocabulary.

Put differently: weak discernibility saves plurality in worlds that have enough structure to weakly discern. The theorem concerns whether pure, atomless relating can *generate* that structure from nothing, and proves it cannot. The eliminativist who invokes weak discernibility owes an account of where the irreflexive relation came from, and the theorem says: not from the plain relating.

Two features of the existing literature make this reply less radical than it may sound. First, the concession is already on record from within the structuralist camp: Esfeld and Lam argue that weak discernibility establishes only the numerical diversity of objects, not their individuation, and cannot ground any priority of relations over relata; accordingly their moderate OSR takes plurality as a primitive posit. The theorem turns that concession from a judgment call into a forced move. Second, Leitgeb and Ladyman exhibit graph-theoretic structures that violate even weak formulations of the identity of indiscernibles (structurally indistinguishable nodes discerned by nothing, not even an irreflexive relation), so the weak-discernibility strategy is already known not to generalize to pure structures; their own response is to take the identity and difference of positions as primitive facts constituted by the structure as a whole. In the present framework that response has an exact address: it is the two-loop horn, the denial of behavioral identity. The trilemma of Section 3.3 thus has named occupants in the literature for each horn, and the theorem's contribution is to prove the horns exhaustive.

### 4.2 Why bisimilarity, and not isomorphism or definability

A referee may ask why structural indiscernibility is bisimilarity rather than, say, being swapped by an automorphism, or satisfying the same formulas. Three reasons. First, bisimilarity is the canonical process-theoretic notion of "same relational behavior," with fifty years of convergent usage across modal logic, set theory, and computer science; it is not gerrymandered for this result. Second, bisimilarity is exactly the criterion the mathematically serious version of relational fundamentality already adopts: Aczel-style non-well-founded set theory takes "bisimilar implies equal" (strong extensionality) as its identity axiom. Our behavioral identity condition is that axiom transplanted from sets to arbitrary relational worlds. Third, bisimilarity and not automorphism-orbit sameness is what "same relational role" means for a view on which a thing is *nothing but* its role. Two positions play the same role when their relational unfoldings match, and that is bisimilarity. Automorphism-based indiscernibility makes identity hostage to global symmetry: whether two positions count as one comes to depend on whether the rest of the world happens to be arranged symmetrically around them, which is an extrinsic difference-maker of exactly the kind the eliminativist disavows (two positions can unfold identically forever while no automorphism connects them, because the world elsewhere is lopsided). We flag the corresponding transparency point rather than hide it: behavioral identity is a strictly stronger identification than the automorphism-based one, and the collapse genuinely needs it; under the weaker criterion, plural atomless worlds survive. The paper's claim is that the eliminativist's own thesis commits her to the stronger criterion, which is the burden Section 4.1 and the AFA precedent discharge. This is also Dipert's supervenience requirement read at its natural grain: if numerical identity and diversity must supervene on each node's relational facts, and a node's relational facts are its unfolding, the supervenience base of two bisimilar nodes is one and the same.

### 4.3 What the theorem does not show

The theorem also enters a running exchange about mathematical framework. Bain defended radical OSR by arguing that the incoherence charge rests on set-theoretic formulations of structure and that category theory, by de-emphasizing objects, gives relations-without-relata a coherent home; Lam and Wüthrich replied that category theory is no more hospitable (the morphisms-only reformulation is mere relabelling, generalized elements resurrect constituents, and categories like Hilb and nCob lose the relations along with the relata); Lal and Teh pressed a complementary critique aimed at the underlying forms of categorical generalization. Eva then defended Bain on both fronts, arguing that Bain's case survives largely intact (with the category REL of sets and relations as a further exemplar, and categorical quantum mechanics as ROSR's natural formalism), while closing on a concession: such formalisms establish the intelligibility and coherence of ROSR, but, as Eva grants to Wüthrich and Lam, they "do not count as arguments for the truth of ROSR." The present result needs no side in that exchange, because it enters exactly at Eva's boundary. Grant the eliminativist everything the pro-categorical side asks: a fully categorical home (coalgebras of an endofunctor, with bisimulation its native indiscernibility) in which relations-without-relata is coherently articulated. The theorem then shows what the coherently articulated theory says: taken at full strength, it eliminates plurality itself. The framework question was never the deep one; the problem is not whether relations without relata can be expressed, but what relations without relata express.

The graph-world tradition supplies a further precedent for constraints of this shape. Dipert, defending the thesis that the world is a graph, held that facts about numerical identity and diversity must supervene on the relational facts about each node, and concluded on that ground that the world must be an *asymmetric* graph, since symmetric graphs contain nodes with identical structural descriptions. Leitgeb and Ladyman rejected the supervenience requirement rather than the symmetric worlds; Shackel defended the graph-world against a different formal objection while reading it as a monism. The present theorem sharpens Dipert's own move: at the behavioral grain, and in the atomless case, no asymmetric escape exists at all, because atomlessness erases every downward difference an asymmetry could rest on. A graph-world theorist who keeps Dipert's supervenience principle and drops leaves from the ontology is not driven to asymmetric worlds; she is driven to the One.

The theorem does not show that our world is one thing. It does not show OSR is false. It shows that a specific package (plain + behaviorally identified + atomless + plural) is inconsistent, and therefore that every structural realist must decline at least one conjunct and should say which. Moderate OSR declines plainness (relata as thin nodes still admit non-relational numerical diversity, or spacetime points carry it). Priority-based views decline atomlessness at the limit (there is a fundamental level, even if structural). Views that accept primitive numerical diversity decline behavioral identity. And existence monism accepts the collapse and declines plurality. The theorem's contribution is to make this a forced choice with certified exits, rather than a suggestive worry.

### 4.4 Is the carrier a question-begging home?

There is a consensus in this debate, reported on all sides of the Bain exchange, that set theory is no proper home for eliminativist OSR: a set-theoretic relation is a set of ordered pairs of elements, so formalizing "relations without relata" in set theory looks rigged from line one. Our world is a pair (X, dest) with X a carrier set. The objection writes itself: the carrier's elements are relata smuggled in at the signature, and the collapse is an artifact of a home the eliminativist already declined to live in. This subsection answers that objection, and the answer has four parts.

First, the world of the theorem is native to the home the eliminativist's defenders have themselves certified. The data of a plain world is exactly the data of an endomorphism in **REL**, the category of sets and relations: an arrow r : X → X with u r-related to x precisely when u ∈ dest x, the cardinal bound κ bounding its branching. Atomlessness is a standard property of such an arrow (hereditary totality: every state has a successor, hereditarily), and bisimulation is its standard invariant. **REL** is Eva's own exemplar: the category he argues satisfies even Wüthrich and Lam's requirement that morphisms be relations between elements, and which he offers as instantiating "the kind of category theoretic structure required by ROSR." The theorem does not need to be relocated into the ROSR-approved home. It already lives there; the set-with-elements presentation is how one computes with an arrow of **REL**.

Second, the theorem's logical shape is the reverse of the set-theoretic incoherence argument the consensus rightly rejects. That argument says the view cannot be stated, because relations presuppose relata by definition. We grant statement and derive content. The feature of the carrier that would beg the question, primitive non-relational identity facts for its elements, is precisely what the behavioral-identity hypothesis governs: the proof never touches carrier identity except through that hypothesis. The world where brute element-distinctness does individuating work is exhibited, not presupposed: it is the two-loop countermodel, and it is excluded by the eliminativist's own criterion, not by ours.

Third, the conclusion is carrier-free. Corollary 3 (Appendix A.2) states the collapse without mentioning behavioral identity or the carrier's count: in any plain world there is at most one bisimilarity class of atomless states, and the final map sends every atomless state to Ω. A bisimilarity class is a relational role, the only kind of thing the eliminativist recognizes; roles are invariant under everything the structuralist regards as notation. However many carrier elements a presentation uses, an atomless pure relating supports at most one way of being, and it is the One relating to itself. A critic who deletes our carrier as metaphysically idle deletes nothing the theorem needs.

Fourth, the hypotheses themselves are categorical properties, stated without element-talk in the coalgebra literature: bisimulations are Aczel and Mendler's spans of coalgebra morphisms; behavioral identity is Rutten's simplicity, equivalently the condition that the canonical morphism to the final coalgebra is monic; a leaf is a state whose unfolding factors through the distinguished global element ∅ of P_κ(X), and atomlessness is hereditary avoidance of it. All are invariant under coalgebra isomorphism. The carrier is a coordinate system; the theorem is a statement about the manifold. We state the division of labor plainly rather than overclaim: the theorem's *statement* is categorical and its home is an arrow of **REL**; its *proof* in this paper runs in the set presentation, where the checker can also verify it. Nothing in the objection survives this division except a preference about notation.

A scope remark completes the answer, because it is also the honest limit of the theorem's reach into Eva's territory. Eva's exemplars for ROSR-friendly structure, **HILB**, **FHILB**, **REL**-as-quantum-model, and categorical quantum mechanics generally, are not plain worlds: their morphisms carry amplitudes, scalars, and monoidal structure, which in this paper's semantic vocabulary are labels, coordinates the plain relating does not carry (Section 6). So there is no tension between the coherence of object-free physics and the collapse: a formalism rich in labelled structure occupies the labelled horn of the trilemma, exactly as the theorem predicts. What the theorem constrains is the metaphysical thesis, a world that is atomless pure relating; it does not adjudicate whether quantum theory is best formulated object-freely. An eliminativist who retreats to the latter claim escapes the theorem, at the price of no longer asserting a thesis about what fundamentally exists.

## 5. Locating the mathematics honestly

The collapse engine has recognizable kin, and the paper names them. The identity criterion itself is standard under two names: coalgebras in which bisimilar states are equal are Aczel and Mendler's *strongly extensional* coalgebras and Rutten's *simple* systems (Universal Coalgebra, Theorem 8.1 gives the equivalence with the no-proper-quotients formulation). Under Aczel's anti-foundation axiom, every graph has a unique decoration, two nodes decorate to the same set exactly when a bisimulation relates them, and the Quine atom Ω = {Ω} is the unique set satisfying its equation: uniqueness of solutions for circular set equations is textbook material. Final coalgebras for the κ-bounded powerset functors exist (Rutten, Theorems 10.4 and 10.6; the unbounded powerset has none), Worrell characterized the finite-powerset final coalgebra as the set of finitely branching strongly extensional trees, and Adámek, Levy, Milius, Moss and Sousa have mapped the P_λ final chains in detail. Every ingredient of the theorem is established, canonically named machinery. Two further pieces of that machinery serve the paper directly: every coalgebra has a canonical behaviorally identified quotient (Rutten, Proposition 8.2, quotienting by the greatest bisimulation), so the collapse governs every plain world after extensional quotienting, not only worlds that happen to satisfy the identity criterion outright.

And the tree-level instance of the collapse is in print. Adámek, Levy, Milius, Moss and Sousa, in the background section of their study of the powerset final chains, record it as a passing example (Example 2.7): the infinite path is a strongly extensional tree, and "this is the only strongly extensional tree without leaves because for every tree t without leaves the relation *x R y iff x and y have the same depth* is a tree bisimulation." That is the collapse engine's argument, specialized to trees: the both-leafless relation, cut by depth, is a bisimulation, so leaflessness plus strong extensionality pins the structure uniquely. And the unique survivor is the Quine-atom state: as their Example 2.5 notes, every subtree of the infinite path is the infinite path itself, so it is exactly the fixed point of x = {x}. Their Section 2 apparatus (tree expansions of pointed graphs, with strong extensionality transferring in both directions) extends the observation readily from trees to pointed graphs. A systematic sweep found no earlier or more general statement: the canonical survey of non-wellfounded set theory does not discuss the leafless fragment, Worrell's paper supplies the setting without the statement, and a recent fully-formalized treatment of anti-foundation in type theory mentions the Quine atom only as a motivating example [see the accompanying literature review for the verification record]. There is a structural reason the observation stayed a passing example: the literature's headline results run in the opposite direction, establishing how *large* the final coalgebras are (they contain all the leaf-bearing trees), whereas the collapse concerns the leafless fragment, which had no mathematical reason to be isolated before atomlessness became a philosophical premise.

The novelty claims are therefore staked in three tiers:

1. **The philosophical deployment is new.** The standing objections to eliminativist OSR are informal, as Esfeld and Lam's survey records while explicitly declining to rule the position incoherent a priori; no formal impossibility result exists in this debate. This paper supplies one, with the three countermodels mapping the escape routes onto the standard positions. Nothing in the mathematical literature connects the leafless collapse to individuation, ontology, or structural realism.
2. **The packaging is new.** The engine lemma is proved for arbitrary plain coalgebras: no trees, no pointed graphs, no anti-foundation axiom, no terminality, and behavioral identity as an explicit, negatable hypothesis, which is exactly what lets the countermodels map the debate. The strip tests and the machine-checked artifact have no counterpart in the literature.
3. **The mathematics of the engine, taken alone, is not new, and the paper says so plainly.** Its tree-level instance is Example 2.7 of Adámek, Levy, Milius, Moss and Sousa, proved there in one sentence; the general form is the same four lines at coalgebra level. The paper cites Example 2.7 as prior art and claims for the mathematics only the hypothesis-explicit generality and the verification. [Remaining check before submission: a courtesy skim of Barwise and Moss for an even earlier statement, and a specialist sanity pass.]

Distinctness from Newman's problem is worth one paragraph. Newman's objection is that "the world has structure W" is nearly trivial because structure is cheap: any collection of the right cardinality carries W. The Parmenides collapse points the opposite direction: for *plain atomless* worlds under the structuralist identity criterion, structure is not cheap but impossible to diversify; cardinality itself collapses. The two results bracket eliminativist structuralism from both sides: with unconstrained relata, structure says almost nothing (Newman); with no relata at all, structure cannot even say "two" (this paper).

## 6. The exogenous distinction: given or chosen

Suppose the eliminativist accepts the theorem and buys plurality with a label, as the labelled countermodel shows she must if she keeps atomlessness and behavioral identity over the plain part. What has she bought, semantically?

There is a semantic characterization of imports. A coordinate on a world is *recoverable* when it is definable from the plain relating (invariant under plain bisimilarity); it is an *import* when two plain-bisimilar states can differ on it. Two facts follow (Appendix A.5): a free label is an import in this sense, and any recoverable coordinate is constant on the atomless part, collapsing along with the plain structure it supervenes on. So the label that buys plurality is not a notational convenience; it is, provably, a distinction the relating cannot carry. Plurality in an atomless behaviorally identified world is exactly as costly as one exogenous distinction.

A small, strange result follows about that cost, which we offer as the paper's closing observation rather than its thesis. Two metaphysical stories about the exogenous distinction suggest themselves: it is *given* (a pre-existing non-relational fact, an atom in disguise) or it is *chosen* (a freely originated differentiation, a symmetry breaking with no prior ground). The formal result (Appendix A.5): any function of an atomless relational history takes the same value on all of them, since all such histories are equal; hence no internal test, however sophisticated, distinguishes a world whose exogenous distinction was given from one whose distinction was chosen. The formalism can certify *that* the distinction is exogenous and is provably silent on *which kind* of exogeny it is. Readers of the Eleatics may hear in this an old note: what breaks the One cannot, from inside the broken world, be traced to necessity or to act. We state it as a theorem and leave it there.

## 7. Conclusion

Take the eliminativist structural realist at her word. Let the world be relating and nothing else; let same role mean same thing; let there be no bottom. Then there is at most one thing: Parmenides, as a theorem. The result is not a refutation of structural realism but a proved trilemma at its foundation: atoms, labels, or primitive difference. Every escape from the One is one of the three, each is exhibited by a countermodel, and the choice among them is now the precise content of the question "what individuates?" The relating, provably, does not.

---

## Appendix A. Proofs

Throughout, fix an infinite cardinal κ. For a set X, let P_κ(X) be the set of subsets of X of cardinality less than κ. A *plain world* is a pair (X, dest) with dest : X → P_κ(X); we read u ∈ dest x as "x relates to u."

### A.1 Definitions

**Bisimulation.** A relation R ⊆ X × X is a *bisimulation* on (X, dest) when, whenever R(x, y): every u ∈ dest x has some v ∈ dest y with R(u, v), and every v ∈ dest y has some u ∈ dest x with R(u, v). Write x ~ y (*x and y are bisimilar*) when some bisimulation relates x and y.

**Behavioral identity.** (X, dest) is *behaviorally identified* when every bisimulation on it is contained in the identity relation; equivalently, x ~ y implies x = y. (This is Rutten's simplicity and Aczel and Mendler's strong extensionality; see Section 5.)

**Atomlessness.** Consider the operator Φ on predicates over X given by: Φ(P) holds at x iff dest x is non-empty and every u ∈ dest x satisfies P. Φ is monotone, so by Knaster and Tarski it has a greatest fixed point; call it SHNE (*hereditarily non-empty*). Unwinding: SHNE x iff dest x is non-empty and every u ∈ dest x is SHNE, coinductively. A state fails SHNE exactly when its unfolding can reach a *leaf*, a state with empty relating, in finitely many steps; SHNE is genuine every-moment atomlessness. The world is *atomless* when every state is SHNE.

**Plurality.** There exist x, y ∈ X with x ≠ y.

### A.2 The engine and the theorem

**Lemma 1 (collapse engine).** On any plain world, the relation R(x, y) iff (SHNE x and SHNE y) is a bisimulation.

*Proof.* Suppose R(x, y), so x and y are both SHNE. Let u ∈ dest x. Since x is SHNE, u is SHNE. Since y is SHNE, dest y is non-empty; choose any v ∈ dest y. Since v ∈ dest y and y is SHNE, v is SHNE. So R(u, v), and v ∈ dest y as required. The symmetric condition holds by the same argument with x and y exchanged. ∎

**Corollary 2.** In any plain world, any two SHNE states are bisimilar.

**Corollary 3 (carrier-free form).** In any plain world, there is at most one bisimilarity class of SHNE states.

*Proof.* Bisimulations are closed under composition and converse, so bisimilarity is an equivalence relation; by Corollary 2 all SHNE states fall in one class. ∎

(Proposition 7 in Section A.4 identifies the unique class: the canonical map into the final coalgebra sends every SHNE state to Ω.)

**Theorem 4 (static form).** If (X, dest) is behaviorally identified and atomless, then X has at most one element.

*Proof.* Let x, y ∈ X. Both are SHNE (atomlessness), so x ~ y (Corollary 2), so x = y (behavioral identity). ∎

**Theorem 5 (Parmenides collapse).** No plain world is behaviorally identified, atomless, and plural.

*Proof.* Immediate from Theorem 4. ∎

### A.3 The countermodels

Each countermodel drops exactly one hypothesis and satisfies the remaining ones, so each hypothesis is load-bearing. All three have carrier X = {0, 1}; note that singletons and the empty set lie in P_κ(X) since κ is infinite.

**Leaf world (drops atomlessness).** dest 0 = {1}, dest 1 = ∅. *Plural:* 0 ≠ 1. *Behaviorally identified:* let R be a bisimulation and suppose R(0, 1). Then 1 ∈ dest 0 must be matched by some v ∈ dest 1 = ∅, which is impossible; so R does not relate 0 to 1, and symmetrically not 1 to 0, hence R ⊆ identity. *Not atomless:* dest 1 = ∅, so 1 is a leaf (and 0 is not SHNE either, since its unfolding reaches the leaf). The world is plain.

**Labelled world (drops plainness).** Work over the labelled signature dest' : X → L × P_κ(X) with L = {a, b}: dest' 0 = (a, {0}), dest' 1 = (b, {1}). A bisimulation for the labelled signature additionally requires related states to carry equal labels. *Behaviorally identified (labelled):* no labelled bisimulation relates 0 and 1, since a ≠ b; so every labelled bisimulation is contained in identity. *Atomless:* each state relates to itself, hereditarily. *Plural:* 0 ≠ 1. Not plain: the label is a non-relational coordinate, and Section 6's semantic test confirms it (Section A.5).

**Two-loop world (drops behavioral identity).** dest 0 = {0}, dest 1 = {1}. *Plain, atomless, plural* as above. *Not behaviorally identified:* the total relation X × X is a bisimulation (for R(0, 1): the unique u = 0 ∈ dest 0 is matched by v = 1 ∈ dest 1 with R(0, 1), and conversely), and it is not contained in identity. ∎

### A.4 The dynamic sharpening

For P_κ with κ a regular infinite cardinal, a final coalgebra (Z, ζ) exists [Rutten, Theorems 10.3-10.4; Worrell], and final coalgebras satisfy the coinduction principle: bisimilar elements of Z are equal [Rutten, Theorem 8.1 with the finality argument; equivalently, final coalgebras are behaviorally identified].

**Proposition 7.** The SHNE part of the final P_κ coalgebra is exactly {Ω}, where Ω is the unique element with ζ(Ω) = {Ω}.

*Proof.* Existence of Ω: the one-point coalgebra ({∗}, ∗ ↦ {∗}) has a unique coalgebra morphism h into Z; its image Ω = h(∗) satisfies ζ(Ω) = {Ω} by the morphism condition. Ω is SHNE: the predicate "equals Ω" is a post-fixed point of Φ, since ζ(Ω) = {Ω} is non-empty and contains only Ω. Uniqueness and exhaustion: any two SHNE elements of Z are bisimilar (Corollary 2) and hence equal by coinduction; since Ω is SHNE, every SHNE element equals Ω. ∎

It follows that the canonical map h : X → Z sends every SHNE state of every plain world to Ω: the set of homomorphic images of SHNE states is a post-fixed point of Φ (images of non-empty sets are non-empty, and children of images are images of children), so such images are SHNE in Z, and by Proposition 7 they all equal Ω. This discharges the identification promised after Corollary 3.

Reading Z as the space of fully unfolded relational histories, Proposition 7 is the statement quoted in Section 3.2: there is exactly one way to relate forever without ground. The tree-level instance of this proposition, for the finite powerset functor, is Example 2.7 of Adámek, Levy, Milius, Moss and Sousa; see Section 5.

### A.5 Imports, recoverable coordinates, and the given-or-chosen result

Fix a plain world (X, dest) and a set L of labels. A coordinate c : X → L is *recoverable* when it is invariant under plain bisimilarity (x ~ y implies c x = c y), and an *import* otherwise.

**Proposition 8 (a free label is an import).** In the two-loop world with c(0) = a ≠ b = c(1): since 0 ~ 1 under the plain relating (Section A.3: the total relation on the two-loop world is a bisimulation) while c(0) ≠ c(1), c is not recoverable. ∎

**Proposition 9 (recoverable coordinates collapse on the atomless part).** In any plain world, a recoverable coordinate is constant on the SHNE states.

*Proof.* Any two SHNE states are bisimilar (Corollary 2); recoverability transports equality of the coordinate along bisimilarity. ∎

Propositions 8 and 9 together give Section 6's dilemma: a coordinate either supervenes on the plain relating, in which case it cannot separate any two atomless states, or it genuinely individuates, in which case it is provably a distinction the relating does not carry.

**Proposition 10 (given and chosen are indistinguishable from inside).** Let histories be elements of the final coalgebra Z and call a history *productive* when it is SHNE. Then for any function f defined on histories, f takes the same value on all productive histories.

*Proof.* By Proposition 7 there is exactly one productive history, Ω; a function is trivially constant on a one-element set. ∎

The philosophical reading in Section 6 follows: any internal criterion meant to classify the exogenous distinction's origin (given versus chosen) is a function of the atomless relational history, and all such functions are constant, so the classification cannot be made from inside. The force of the observation is that the *only* raw material an atomless relational world offers for such a test is its history, and the history is unique.

---

## References

*[Working list; metadata hand-verified in rounds 3 through 5 of `literature-review.md`. Eva 2016 has been read in full.]*

- Aczel, P. (1988). *Non-Well-Founded Sets*. CSLI Lecture Notes 14. Stanford: CSLI.
- Adámek, J., Levy, P., Milius, S., Moss, L. & Sousa, L. (2015). "On final coalgebras of power-set functors and saturated trees." *Applied Categorical Structures* 23: 609-641. doi:10.1007/s10485-014-9372-9.
- Bain, J. (2013). "Category-theoretic structure and radical ontic structural realism." *Synthese* 190: 1621-1635.
- Barwise, J. & Moss, L. (1996). *Vicious Circles: On the Mathematics of Non-Wellfounded Phenomena*. CSLI Lecture Notes 60. Stanford: CSLI.
- Bigaj, T. (2022). *Identity and Indiscernibility in Quantum Mechanics*. Palgrave Macmillan.
- Chakravartty, A. (1998). "Semirealism." *Studies in History and Philosophy of Science* 29: 391-408. (The relations-need-relata formulation at p. 399.)
- Black, M. (1952). "The identity of indiscernibles." *Mind* 61: 153-164.
- Button, T. (2006). "Realistic structuralism's identity crisis: a hybrid solution." *Analysis* 66: 216-222.
- Carnap, R. (1928). *Der logische Aufbau der Welt*. §14 (the railtrack network).
- Caulton, A. (2013). "Discerning 'indistinguishable' quantum systems." *Philosophy of Science* 80(1): 49-72.
- Dipert, R. (1997). "The mathematical structure of the world: the world as graph." *Journal of Philosophy* 94: 329-358.
- Esfeld, M. & Lam, V. (2011). "Ontic structural realism as a metaphysics of objects." In Bokulich & Bokulich (eds.), *Scientific Structuralism* (Boston Studies in the Philosophy of Science 281). Springer: 143-159. Preprint: philsci-archive 5531.
- Eva, B. (2016). "Category theory and physical structuralism." *European Journal for Philosophy of Science* 6(2): 231-246.
- French, S. (2010). "The interdependence of structure, objects and dependence." *Synthese* 175 (supp.): 89-109. (Section 7: the collapse of intermediate positions into eliminativism.)
- French, S. (2014). *The Structure of the World*. Oxford: OUP.
- French, S. & Ladyman, J. (2003). "Remodelling structural realism." *Synthese* 136: 31-56.
- Gylterud, H., Stenholm, E. & Veltri, N. "Terminal coalgebras and non-wellfounded sets in homotopy type theory." arXiv:2001.06696. (Journal venue unconfirmed; cited from the arXiv version.)
- Ladyman, J. (1998). "What is structural realism?" *Studies in History and Philosophy of Science* 29: 409-424.
- Ladyman, J. (2007). "On the identity and diversity of objects in a structure." *Proceedings of the Aristotelian Society*, supp. vol. 81: 23-43.
- Hawley, K. (2006). "Weak discernibility." *Analysis* 66: 300-303.
- Keranen, J. (2001). "The identity problem for realist structuralism." *Philosophia Mathematica* 9(3): 308-330.
- Ketland, J. (2006). "Structuralism and the identity of indiscernibles." *Analysis* 66: 303-315. (The "dumb-bell" structure, p. 309.)
- Ladyman, J. (2005). "Mathematical structuralism and the identity of indiscernibles." *Analysis* 65: 218-221.
- Ladyman, J. & Ross, D. (2007). *Every Thing Must Go*. Oxford: OUP.
- Lal, R. & Teh, N. (2017). "Categorical generalization and physical structuralism." *British Journal for the Philosophy of Science* 68(1): 213-251. arXiv:1404.3049.
- Lam, V. & Wüthrich, C. (2015). "No categorial support for radical ontic structural realism." *British Journal for the Philosophy of Science* 66: 605-634. doi:10.1093/bjps/axt053.
- Leitgeb, H. & Ladyman, J. (2008). "Criteria of identity and structuralist ontology." *Philosophia Mathematica* 16(3): 388-396. doi:10.1093/philmat/nkm039.
- Moss, L. "Non-wellfounded set theory." *Stanford Encyclopedia of Philosophy* (2008, rev. 2018).
- Muller, F. A. & Saunders, S. (2008). "Discerning fermions." *British Journal for the Philosophy of Science* 59(3): 499-548. doi:10.1093/bjps/axn027.
- Muller, F. A. & Seevinck, M. (2009). "Discerning elementary particles." *Philosophy of Science* 76(2): 179-200. doi:10.1086/647486. arXiv:0905.3273.
- Newman, M. H. A. (1928). "Mr. Russell's 'causal theory of perception'." *Mind* 37: 137-148.
- Oderberg, D. (2011). "The world is not an asymmetric graph." *Analysis* 71(1): 3-10.
- Rutten, J. (2000). "Universal coalgebra: a theory of systems." *Theoretical Computer Science* 249: 3-80.
- Saunders, S. (2003). "Physics and Leibniz's principles." In Brading & Castellani (eds.), *Symmetries in Physics: Philosophical Reflections*. Cambridge: CUP: 289-307.
- Saunders, S. (2006). "Are quantum particles objects?" *Analysis* 66: 52-63.
- Schaffer, J. (2010). "Monism: the priority of the whole." *Philosophical Review* 119(1): 31-76.
- Shackel, N. (2011). "The world as a graph: defending metaphysical graphical structuralism." *Analysis* 71(1): 10-21.
- Shapiro, S. (2008). "Identity, indiscernibility, and ante rem structuralism: the tale of i and -i." *Philosophia Mathematica* 16(3): 285-309.
- Worrell, J. (2005). "On the final sequence of a finitary set functor." *Theoretical Computer Science* 338: 184-199.
