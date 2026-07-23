# The Parmenides Collapse: A Machine-Checked No-Go Theorem for Relations Without Relata

**Colleen Love**

*First draft. Copyright © 2026 Colleen Love. All rights reserved.*

*Status note: this is a working draft. The formal claims are machine-checked and stable. The related-work positioning is grounded in the source-quoted literature sweep recorded in `literature-review.md`; claims marked [TBV] still need manual verification before submission (see that file's confidence tiers and open-actions list).*

---

## Abstract

Eliminativist ontic structural realism holds that the world is structure all the way down: relations without relata, or at least without relata that are anything over and above their relational roles. This paper presents a machine-checked impossibility theorem for a natural formal precisification of that view. Model a purely relational world as a coalgebra of the bounded powerset functor, so that a thing simply is its outgoing relating and nothing else. Say the world is *behaviorally identified* when structurally indiscernible things are identical (bisimilarity implies equality), *atomless* when no thing's relating ever bottoms out in something that relates to nothing, and *plural* when it contains at least two things. The theorem: no such world is behaviorally identified, atomless, and plural. Purely relational, atomless universes hold at most one thing. We call this the Parmenides collapse, since it recovers, as a theorem about arbitrary relational structures, the Eleatic conclusion that a world of pure undifferentiated being is One. Each hypothesis is shown to be load-bearing by an explicit countermodel. The proof is verified in Lean 4 against Mathlib and rests on no axioms beyond the standard three. We argue that the theorem sharpens the central dilemma for ontic structural realism: an eliminativist about relata must either embrace existence monism or admit a distinction that the relating itself cannot carry, and we show that the formalism can classify such a distinction as exogenous while remaining provably silent on whether it is given or chosen.

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

First, **each hypothesis is proved load-bearing by an explicit countermodel**, so the theorem is not a definitional sleight of hand. Drop atomlessness and there is a behaviorally identified plural world with a leaf (a thing that relates to nothing): the empty node grounds difference, exactly as the traditional relata-theorist expects. Drop plainness and a two-element labelled world survives: a label is precisely a non-relational distinction. Drop behavioral identity and a plural world of two indiscernible loops survives: plurality is saved by brute haecceitistic difference, exactly what the structuralist forswears. The three escapes from the theorem are the three classical positions in the debate, recovered as the three ways of negating a hypothesis.

Second, **the theorem is fully general.** It quantifies over every carrier at every cardinal bound κ. Nothing depends on finiteness, on a chosen example, or on a particular construction. This matters because collapse worries in the OSR literature are usually pressed against particular toy structures and answered by exhibiting other toy structures; the theorem closes that loop.

Third, **the proof is machine-checked.** The entire development is verified in Lean 4 against Mathlib, is free of `sorry` and of custom axioms, and every headline theorem is audited to rest on at most the three standard axioms of Lean's classical foundation (`propext`, `Classical.choice`, `Quot.sound`). An artifact repository accompanies the paper with a table mapping every numbered claim to its formal name. The reader need not trust our proof sketches; the checker has already refereed them.

The paper proceeds as follows. Section 2 motivates coalgebras and bisimulation as the right formal home for eliminativist OSR and states the three conditions precisely. Section 3 states the theorem, sketches the proof, and presents the countermodels. Section 4 describes the machine verification. Section 5 defends the adequacy of the formalization, addressing weak discernibility directly: we argue that weak discernibility is a claim *about* certain structured worlds, while behavioral identity is the identity criterion the eliminativist is committed to, and that the theorem shows these come apart exactly where the eliminativist needs them to coincide. Section 6 locates the mathematics honestly with respect to known facts about non-well-founded sets and final coalgebras: the collapse phenomenon has recognizable kin in the uniqueness of the Quine atom under Aczel's anti-foundation axiom, and we state precisely what is and is not new here. Section 7 draws the consequences: the eliminativist's live options are existence monism or the admission of an exogenous distinction, and we prove a supplementary result about that distinction: the formalism can detect that it is not carried by the relating, but provably cannot distinguish whether it is given or chosen. Section 8 concludes.

## 2. The formal home: worlds as coalgebras

### 2.1 Why coalgebras

A formalization of "relations without relata" must walk a line. If the model gives objects intrinsic features, it has smuggled in what the eliminativist denies. If it gives them nothing at all, there is no model. The coalgebraic resolution is that an object *is* exactly one datum: the set of objects it relates to. A world is a pair (X, dest) with `dest : X → P_κ(X)`, where P_κ is the powerset functor bounded at cardinal κ (the bound ensures the mathematics is well behaved; κ can be as large as one likes, and nothing in the paper depends on its value).

This is not an exotic choice. Coalgebras of powerset-like functors are the standard semantics for transition systems, for non-well-founded sets, and for Kripke frames. Their canonical notion of indiscernibility, bisimilarity, is the accepted formalization of "same observable structure" across computer science and modal logic. When the eliminativist says an object is its relational role, the coalgebraist has a precise paraphrase: an object is its behavior under `dest`, and two objects have the same role exactly when they are bisimilar.

We stress what the carrier X is and is not. The elements of X are not relata in the traditional metaphysical sense, bearers of intrinsic natures. They are positions: bare indices whose entire content is given by `dest`. A plain coalgebra with behavioral identity is exactly a world in which positions with the same relational content are the same position. This is, we will argue in Section 5, the strongest honest reading of "relata are nothing over and above their relational roles."

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

In the formal development the theorem is `ws2_import_theorem`, with a static form `ws2_import_theorem_static` concluding `Subsingleton X` from the first two hypotheses. There is also a dynamic sharpening: on the terminal (final) coalgebra, where behavioral identity holds by construction, all *productive* threads (histories that never bottom out) are not merely bisimilar but literally equal, and equal to the canonical self-looping state Ω (`ws1_productive_unique`). A purely relational atomless history is unique: there is exactly one way to relate forever without ground, and it is the One relating to itself.

### 3.3 The strip test: every hypothesis is load-bearing

A no-go theorem earns its keep by the failure of its weakenings. Each hypothesis, dropped, admits an explicit plural countermodel, and each countermodel is a recognizable philosophical position.

**Drop atomlessness: the leaf world (`leafCoalg`).** Two states; one relates to the other; the other relates to nothing. This world is plain, behaviorally identified, and plural. The empty node is discernible from the non-empty node by its relating alone, and everything downstream inherits discernibility from it. This is the traditional picture: a ground floor of atoms (here, one atom) from which all difference flows. The theorem does not refute atomism; it prices it. Difference is available exactly where the relating bottoms out.

**Drop plainness: the labelled world (`labelLoop`).** Two states, each relating only to itself, carrying distinct labels. Behaviorally identified over the *labelled* functor, atomless, plural. A label is a coordinate that the plain relating does not carry; with labels, plurality is trivial. This is the moderate structuralist's world, and the countermodel makes the cost explicit: the labels are doing the individuating, and they are not relational structure. (Section 7 returns to what a label is, semantically rather than syntactically.)

**Drop behavioral identity: the two-loop world (`twoLoop`).** Two states, each relating only to itself, no labels. Plain, atomless, plural, and *not* behaviorally identified: the total relation is a bisimulation not contained in equality. The two loops are structurally indiscernible yet distinct. Their difference is primitive thisness, haecceity, brute numerical distinctness with no discernible ground. This world is consistent; the theorem does not rule it out. But it is precisely the world the eliminativist structuralist cannot claim, because admitting it concedes that identity and relational role come apart, which is the denial of the view.

The three countermodels triangulate the theorem. Atoms, labels, or haecceities: pick one, and plurality is cheap. Refuse all three, and plurality is gone. That trilemma, we take it, is the exact logical geography of the individuation debate in OSR, now with each region certified inhabited or empty by proof.

## 4. Machine verification

All results are formalized in Lean 4 and checked against Mathlib (pinned versions recorded in the artifact). The development is free of `sorry`, `admit`, `native_decide`, and custom axioms. An in-build audit module runs `#print axioms` over every headline theorem; each rests on at most Lean's standard classical triple (`propext`, `Classical.choice`, `Quot.sound`), and several, including the verdict computations, on none. The countermodels of Section 3.3 are constructed terms, not assumptions: `leafCoalg`, `labelLoop`, and `twoLoop` are definitions whose claimed properties are theorems about them.

We make the usual division of epistemic labor explicit. The checker certifies that the theorems follow from the definitions. It cannot certify that the definitions capture the philosophy; that argument is Section 5, and it is the paper's genuinely philosophical burden. What machine-checking removes from the table is the classic failure mode of formal philosophy, in which the interesting step hides inside an unexamined proof or an ambiguous formal statement. Here every claim of the form "this world is behaviorally identified" or "this relation is a bisimulation" is discharged by a proof object a referee can run.

The minimal artifact (the theorem, the engine, the countermodels, the audit) is being extracted to a standalone repository with continuous integration and an archived DOI release [TBV: repository reference to be inserted].

## 5. Adequacy: is behavioral identity the structuralist's criterion?

The theorem is only as interesting as its hypotheses are faithful. The load falls on behavioral identity, and the objection will come from the weak discernibility literature, so we take it head on.

### 5.1 The weak discernibility reply, and why it does not touch the theorem

Saunders and Muller argued, for quantum cases, that numerically distinct indiscernibles can be *weakly discerned*: an irreflexive relation holds between them that neither bears to itself, and this suffices for a defensible form of the identity of indiscernibles. Whatever its merits in quantum mechanics, note the logical shape of the reply: it *exhibits worlds* in which relations discern. It is an existence claim about certain structures.

The Parmenides collapse is a universal claim about a *class* of structures characterized by an identity criterion. The two do not compete; they pass through each other, and where they meet is instructive. In the two-loop countermodel, is there an irreflexive relation weakly discerning the loops? Over the plain signature, every relation definable from the structure is invariant under the swap automorphism, and the theorem's engine shows that bisimilarity, the finest structurally available equivalence, already identifies them. Weak discernment of the two loops requires a relation that the plain relating does not carry. The weak discernibility strategy, applied to a plain atomless world, must therefore import its discerning relation, and an imported relation is a label in the semantic sense of Section 7. The strategy is not wrong; it is a way of *occupying the labelled-world horn* of the trilemma while describing it in relational vocabulary.

Put differently: weak discernibility saves plurality in worlds that have enough structure to weakly discern. The theorem concerns whether pure, atomless relating can *generate* that structure from nothing, and proves it cannot. The eliminativist who invokes weak discernibility owes an account of where the irreflexive relation came from, and the theorem says: not from the plain relating.

Two features of the existing literature make this reply less radical than it may sound. First, the concession is already on record from within the structuralist camp: Esfeld and Lam argue that weak discernibility establishes only the numerical diversity of objects, not their individuation, and cannot ground any priority of relations over relata; accordingly their moderate OSR takes plurality as a primitive posit. The theorem turns that concession from a judgment call into a forced move. Second, Leitgeb and Ladyman exhibit graph-theoretic structures that violate even weak formulations of the identity of indiscernibles (structurally indistinguishable nodes discerned by nothing, not even an irreflexive relation), so the weak-discernibility strategy is already known not to generalize to pure structures; their own response is to take the identity and difference of positions as primitive facts constituted by the structure as a whole. In the present framework that response has an exact address: it is the two-loop horn, the denial of behavioral identity. The trilemma of Section 3.3 thus has named occupants in the literature for each horn, and the theorem's contribution is to prove the horns exhaustive.

### 5.2 Why bisimilarity, and not isomorphism or definability

A referee may ask why structural indiscernibility is bisimilarity rather than, say, being swapped by an automorphism, or satisfying the same formulas. Three reasons. First, bisimilarity is the canonical process-theoretic notion of "same relational behavior," with fifty years of convergent usage across modal logic, set theory, and computer science; it is not gerrymandered for this result. Second, bisimilarity is exactly the criterion the mathematically serious version of relational fundamentality already adopts: Aczel-style non-well-founded set theory takes "bisimilar implies equal" (strong extensionality) as its identity axiom. Our behavioral identity condition is that axiom transplanted from sets to arbitrary relational worlds. Third, and decisively for the dialectic: bisimilarity is the *weakest* of the candidate criteria on the table, hence the hardest to collapse with. Anything identified by a coarser criterion (elementary equivalence, automorphism orbits) is bisimilar a fortiori in the relevant constructions. Proving collapse under the weakest identification is proving it under all of them. [TBV: verify the precise inclusion claims for the intended class of structures before submission.]

### 5.3 What the theorem does not show

The theorem also enters a running exchange about mathematical framework. Bain defended radical OSR by arguing that the incoherence charge rests on set-theoretic formulations of structure and that category theory, by de-emphasizing objects, gives relations-without-relata a coherent home; Lam and Wüthrich replied that category theory is no more hospitable (the morphisms-only reformulation is mere relabelling, generalized elements resurrect constituents, and categories like Hilb and nCob lose the relations along with the relata); further rounds followed (Lal and Teh; Eva). The present result takes the critics' side with a different instrument. Rather than arguing that a categorical formulation fails to eliminate objects, we grant the eliminativist a fully categorical home (coalgebras of an endofunctor, with bisimulation its native indiscernibility) and prove that the elimination succeeds and then self-destructs: taken at full strength, it eliminates plurality itself. The problem was never the framework's ability to express relations without relata; it is what relations without relata express.

The theorem does not show that our world is one thing. It does not show OSR is false. It shows that a specific package (plain + behaviorally identified + atomless + plural) is inconsistent, and therefore that every structural realist must decline at least one conjunct and should say which. Moderate OSR declines plainness (relata as thin nodes still admit non-relational numerical diversity, or spacetime points carry it). Priority-based views decline atomlessness at the limit (there is a fundamental level, even if structural). Views that accept primitive numerical diversity decline behavioral identity. And existence monism accepts the collapse and declines plurality. The theorem's contribution is to make this a forced choice with certified exits, rather than a suggestive worry.

## 6. Locating the mathematics honestly

The collapse engine has recognizable kin, and the paper names them. The identity criterion itself is standard under two names: coalgebras in which bisimilar states are equal are Aczel and Mendler's *strongly extensional* coalgebras and Rutten's *simple* systems (Universal Coalgebra, Theorem 8.1 gives the equivalence with the no-proper-quotients formulation). Under Aczel's anti-foundation axiom, every graph has a unique decoration, two nodes decorate to the same set exactly when a bisimulation relates them, and the Quine atom Ω = {Ω} is the unique set satisfying its equation: uniqueness of solutions for circular set equations is textbook material. Final coalgebras for the κ-bounded powerset functors exist (Rutten, Theorems 10.4 and 10.6; the unbounded powerset has none), Worrell characterized the finite-powerset final coalgebra as the set of finitely branching strongly extensional trees, and Adámek, Levy, Milius, Moss and Sousa have mapped the P_λ final chains in detail. Every ingredient of the theorem is established, canonically named machinery. Two further pieces of that machinery serve the paper directly: every coalgebra has a canonical behaviorally identified quotient (Rutten, Proposition 8.2, quotienting by the greatest bisimulation), so the collapse governs every plain world after extensional quotienting, not only worlds that happen to satisfy the identity criterion outright.

What a systematic sweep of that literature did not find is the combined statement: that the hereditarily non-empty part of an arbitrary behaviorally identified plain coalgebra is a subsingleton. The canonical survey of non-wellfounded set theory (Moss's SEP entry) does not state or discuss it; Worrell's paper supplies exactly the setting in which it could be checked (a leafless strongly extensional tree is precisely an SHNE state) and does not state it; a recent fully-formalized treatment of anti-foundation in type theory (Gylterud, Stenholm and Veltri) mentions the Quine atom only as a motivating example, with no occurrence of hereditary non-emptiness or atomlessness in its text. This negative existential survived three-vote adversarial verification across the four canonical sources checked (see the accompanying literature review). There is also a structural reason the question could go unasked: the literature's headline results run in the opposite direction, establishing how *large* the final coalgebras are (they contain all the leaf-bearing trees), whereas the collapse concerns the leafless fragment nobody had reason to isolate before atomlessness became a philosophical premise. We conclude, provisionally [TBV: a targeted check of Aczel 1988, Barwise and Moss, and the strongly-extensional Kripke frame literature, plus a specialist consultation, remains owed before submission], that the engine is best described as elementary given the classical machinery and apparently unstated at this generality.

The novelty claims are therefore staked in three tiers:

1. **The philosophical deployment is new.** The standing objections to eliminativist OSR are informal, as Esfeld and Lam's survey records while explicitly declining to rule the position incoherent a priori; no formal impossibility result exists in this debate. This paper supplies one, with the three countermodels mapping the escape routes onto the standard positions.
2. **The packaging is new.** The engine lemma is proved for arbitrary plain coalgebras, not inside a set theory and not on a final coalgebra: no anti-foundation axiom and no terminality is assumed, and behavioral identity appears as an explicit hypothesis, which is exactly what lets the countermodels negate it and the debate map onto it.
3. **The mathematics of the engine, taken alone, is folklore-adjacent**, and the paper says so plainly: four lines, elementary given fifty years of coalgebra, apparently unstated. If a prior statement at this generality surfaces, it will be cited, and the contribution rests on tiers 1 and 2 without loss.

Distinctness from Newman's problem is worth one paragraph. Newman's objection is that "the world has structure W" is nearly trivial because structure is cheap: any collection of the right cardinality carries W. The Parmenides collapse points the opposite direction: for *plain atomless* worlds under the structuralist identity criterion, structure is not cheap but impossible to diversify; cardinality itself collapses. The two results bracket eliminativist structuralism from both sides: with unconstrained relata, structure says almost nothing (Newman); with no relata at all, structure cannot even say "two" (this paper).

## 7. The exogenous distinction: given or chosen

Suppose the eliminativist accepts the theorem and buys plurality with a label, as the labelled countermodel shows she must if she keeps atomlessness and behavioral identity over the plain part. What has she bought, semantically?

The formal development includes a semantic characterization of imports. A coordinate on a world is *recoverable* when it is definable from the plain relating (invariant under plain bisimilarity); it is an *import* when two plain-bisimilar states can differ on it. Theorems in the development show a free label is an import in this sense, while any recoverable label collapses along with the plain structure it supervenes on (`ws4_free_label_is_import`, `ws4_recoverable_atomless_collapses`). So the label that buys plurality is not a notational convenience; it is, provably, a distinction the relating cannot carry. Plurality in an atomless behaviorally identified world is exactly as costly as one exogenous distinction.

The development then proves a small, strange result about that cost, which we offer as the paper's closing observation rather than its thesis. Two metaphysical stories about the exogenous distinction suggest themselves: it is *given* (a pre-existing non-relational fact, an atom in disguise) or it is *chosen* (a freely originated differentiation, a symmetry breaking with no prior ground). The formal result (`att_cannot_distinguish_atomless_histories`): any function of an atomless relational history takes the same value on all of them, since all such histories are equal; hence no internal test, however sophisticated, distinguishes a world whose exogenous distinction was given from one whose distinction was chosen. The formalism can certify *that* the distinction is exogenous and is provably silent on *which kind* of exogeny it is. Readers of the Eleatics may hear in this an old note: what breaks the One cannot, from inside the broken world, be traced to necessity or to act. We state it as a theorem and leave it there.

## 8. Conclusion

Take the eliminativist structural realist at her word. Let the world be relating and nothing else; let same role mean same thing; let there be no bottom. Then there is at most one thing: Parmenides, machine-checked. The result is not a refutation of structural realism but a certified trilemma at its foundation: atoms, labels, or haecceities. Every escape from the One is one of the three, each is exhibited by a countermodel, and the choice among them is now the precise content of the question "what individuates?" The relating, provably, does not.

---

## References

*[Working list, compiled from the source-quoted literature sweep in `literature-review.md`. Entries marked [TBV] need a final metadata check; unmarked entries carry source-verified details from the sweep. Full reading of Lal & Teh and Eva is still owed.]*

- Aczel, P. (1988). *Non-Well-Founded Sets*. CSLI Lecture Notes 14. Stanford: CSLI.
- Adámek, J., Levy, P., Milius, S., Moss, L. & Sousa, L. (2015). "On final coalgebras of power-set functors and saturated trees." *Applied Categorical Structures* 23: 609-641. doi:10.1007/s10485-014-9372-9. [TBV: pages]
- Bain, J. (2013). "Category-theoretic structure and radical ontic structural realism." *Synthese* 190: 1621-1635.
- Barwise, J. & Moss, L. (1996). *Vicious Circles*. Stanford: CSLI. [TBV]
- Bigaj, T. (2022). [Absolute discernibility of quantum particles; per SEP Structural Realism.] [TBV]
- Chakravartty, A. (1998). [The canonical relations-need-relata formulation, p. 399.] [TBV: title and venue]
- Dipert, R. (1997). "The mathematical structure of the world: the world as graph." *Journal of Philosophy* 94: 329-358. [TBV: pages]
- Esfeld, M. & Lam, V. "Ontic structural realism as a metaphysics of objects." [The five-position taxonomy; weak discernibility as diversity without individuation; primitive plurality; the super-holist scenario.] Preprint: philsci-archive 5531. [TBV: final venue and year]
- Eva, B. (2016). [Reply on category theory and structuralism, contesting Lal & Teh; per SEP.] [TBV]
- French, S. (2010). [The collapse of intermediate positions into eliminativism, section 7.] [TBV]
- French, S. (2014). *The Structure of the World*. Oxford: OUP. [TBV]
- French, S. & Ladyman, J. (2003). "Remodelling structural realism." *Synthese* 136: 31-56. [TBV: pages]
- Gylterud, H., Stenholm, E. & Veltri, N. "Terminal coalgebras and non-wellfounded sets in homotopy type theory." arXiv:2001.06696. [TBV: final venue]
- Ladyman, J. (1998). "What is structural realism?" *Studies in History and Philosophy of Science* 29: 409-424. [TBV: pages]
- Ladyman, J. (2007). "On the identity and diversity of objects in a structure." *Proceedings of the Aristotelian Society*, supp. vol. [TBV]
- Ladyman, J. & Ross, D. (2007). *Every Thing Must Go*. Oxford: OUP.
- Lal, R. & Teh, N. (2017). [Reply to Bain on category-theoretic structuralism; per SEP.] [TBV]
- Lam, V. & Wüthrich, C. (2015). "No categorial support for radical ontic structural realism." *British Journal for the Philosophy of Science* 66: 605-634. doi:10.1093/bjps/axt053.
- Leitgeb, H. & Ladyman, J. (2008). "Criteria of identity and structuralist ontology." *Philosophia Mathematica* 16(3): 388-396. [TBV: end page]
- Moss, L. "Non-wellfounded set theory." *Stanford Encyclopedia of Philosophy* (2008, rev. 2018).
- Muller, F. A. & Saunders, S. (2008). "Discerning fermions." *British Journal for the Philosophy of Science* 59(3): 499-548. doi:10.1093/bjps/axn027.
- Muller, F. A. & Seevinck, M. (2009). "Discerning elementary particles." *Philosophy of Science* 76(2): 179-200. doi:10.1086/647486.
- Newman, M. H. A. (1928). "Mr. Russell's 'causal theory of perception'." *Mind* 37: 137-148. [TBV: pages]
- Oderberg, D. [The objection to graphical structuralism answered by Shackel 2011.] [TBV]
- Rutten, J. (2000). "Universal coalgebra: a theory of systems." *Theoretical Computer Science* 249: 3-80.
- Saunders, S. (2006). "Physics and Leibniz's principles." In Brading & Castellani (eds.), *Symmetries in Physics*. Cambridge: CUP. [TBV: year of volume]
- Schaffer, J. (2010). "Monism: the priority of the whole." *Philosophical Review* 119: 31-76. [TBV: pages]
- Shackel, N. (2011). [Defense of metaphysical graphical structuralism against Oderberg.] *Analysis* 71(1): 10-21. [TBV: title and end page]
- Worrell, J. (2005). "On the final sequence of a finitary set functor." *Theoretical Computer Science* 338: 184-199. [TBV: volume and pages]
