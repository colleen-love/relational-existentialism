# Literature review: positioning and novelty for the two papers

*Compiled 2026-07-22. Copyright © 2026 Colleen Love. All rights reserved.*

## Method and verification status (read first)

This review was produced by a fan-out research pipeline: five search angles, 25 sources fetched, 122 claims extracted with direct quotes from the fetched texts. The pipeline ran twice. Round 1 (2026-07-22) completed search and extraction but its adversarial verification stage was interrupted by a session usage limit. Round 2 (2026-07-23) re-ran the full fetch and put the 25 top-ranked claims through three-vote adversarial verification with Opus verifiers: **23 confirmed, 2 refuted, 0 unverified**, followed by a synthesis that merged the confirmed claims into the seven findings summarized in the "Round 2 verified findings" section below.

Coverage caveat from the verifier run itself: the top-25 ranking concentrated on Strand 1's mathematical-novelty and OSR-positioning claims. **No Strand 2 claim reached verification**, and several Strand 1 tail items (Quine atom uniqueness as stated in Aczel 1988 specifically, Newman, Schaffer, Leitgeb and Ladyman in detail, Dipert) also did not. Those remain at the [quoted] tier.

Confidence tiers used below:
- **[verified]** confirmed by three-vote adversarial verification in round 2.
- **[refuted]** killed 1-2 or 0-3 in round 2 verification; do not cite without reading the paper directly.
- **[quoted]** extracted from the fetched source with a supporting direct quote; not adversarially verified.
- **[check]** citation metadata or interpretation that needs a manual check before submission.

## Round 2 verified findings (all high confidence, votes as noted)

1. **[verified 3-0]** "Behaviorally identified" is exactly Rutten's *simple* coalgebra (Universal Coalgebra, Thm 8.1: simplicity iff coinduction, bisimilar implies equal), reused verbatim as "bisimulation simple" in Gylterud, Stenholm and Veltri (Def. 2.7, with a proved equivalence to Rutten's notion). Rutten Prop. 8.2: every coalgebra becomes simple by quotienting by its greatest bisimulation, so imposing the condition alone is always harmless; the theorem's content lies in its interaction with atomlessness and plurality. Full-text search of Rutten: zero occurrences of "hereditarily" or "atomless."
2. **[verified 3-0, one merged component 2-1]** Final coalgebras of P_κ exist and are canonically constructed: Rutten Ex. 6.8 and Thms 10.3-10.4; Worrell 2005 (finite powerset final coalgebra = finitely branching strongly extensional trees, convergence in ω+ω); Adámek, Levy, Milius, Moss and Sousa (P_λ converges in exactly λ+ω steps; steps are saturated strongly extensional trees).
3. **[verified 3-0 on the merged negative existential; PARTIALLY OVERTURNED by the round 3 hand check below]** No checked source states the theorem's specific result (the hereditarily non-empty part of a simple P_κ coalgebra is a singleton). Rutten, Worrell, and Adámek et al. work directly with strongly extensional P_κ coalgebras and never isolate the hereditarily non-empty part; **their headline results run the opposite direction: final coalgebras are large, containing empty and leaf trees**. Gylterud et al. show the machinery is active and formalized without stating the result. *Round 3 correction: the round 2 verifiers could only see the paywalled Springer abstract of Adámek et al.; the freely hosted full PDF contains Example 2.7, which states the tree-level instance. See Round 3, item 1.*
4. **[verified 3-0]** ROSR is a live, explicitly defended position, not a strawman: Esfeld and Lam's position (5), attributed to French and Ladyman 2003, still defended in French 2010 section 7; Lam and Wüthrich's definition ("free-standing physical structures ... without any recourse to relata").
5. **[verified 3-0]** The existing case against ROSR is informal; no prior formal impossibility proof existed in the debate as of 2010. The three-pronged objection cites Busch 2003, Cao 2003, Chakravartty 2003, Psillos 2006. (Note: round 1 quoted SEP dating Chakravartty's canonical formulation to 1998, p. 399; round 2's verified finding cites Chakravartty 2003 among the objectors. Both may be real works; [check] both against the primary texts.)
6. **[verified 3-0]** The Bain vs Lam and Wüthrich exchange is the key formal-framework round: Bain (arXiv 2011, published Synthese 2013) defends ROSR via category-theoretic reformulation; Lam and Wüthrich (BJPS) reply that category theory "does not offer a more hospitable environment to ROSR than set theory" and that the strategy backfires (relations as subsets of Cartesian products do not exist in all categories).
7. **[verified 3-0 on the merged core]** Weak discernibility is the standard escape route and its scope matters: Muller and Saunders (BJPS 2008) on fermions and PII; Muller and Seevinck 2009 extending it; Ladyman 2007 on contextual individuation. **Two adjacent detail claims were refuted (see below).**

### Refuted in round 2 (do not cite without direct reading)

- **[refuted 1-2]** "Muller and Seevinck 2009 maximally extend Muller and Saunders 2008, establishing weak discernibility of an arbitrary number of similar fermions in finite-dimensional Hilbert spaces." The precise extension relationship and scope wording did not survive verification. Read the two papers before characterizing the relationship between them.
- **[refuted 1-2]** "The discernment of fermions is achieved via physically meaningful, permutation-invariant categorical (non-probabilistic) relations, meaning the individuation is purely relational." The "purely relational individuation" gloss did not survive. State the results' scope only from the papers themselves.

Impact check on the drafts: neither refuted claim is asserted in either draft. The Parmenides draft describes weak discernibility generically (irreflexive relations discerning qualitatively identical objects, Saunders on fermions) and does not characterize the Muller-Seevinck extension or the categorical-relations mechanism. The lit-review entries that repeated these two claims are corrected here.

## Round 3: hand verification, 2026-07-23 (primary sources read directly, no delegation)

This round discharged open actions 2, 4, 5, and 6 by direct reading. Everything below is from the primary texts themselves, read in this session.

### 1. The folklore check (action 2): the tree-level instance IS in print

**The decisive find.** Adámek, Levy, Milius, Moss and Sousa, "On Final Coalgebras of Power-Set Functors and Saturated Trees" (the full PDF, freely hosted by Milius; the round 2 verifiers saw only the paywalled abstract), Example 2.7, quoted exactly:

> "The infinite path t₂ in Example 2.5 is a strongly extensional tree. This is the only strongly extensional tree without leaves because for every tree t without leaves the relation *x R y iff x and y have the same depth* is a tree bisimulation."

This is the tree-level instance of the collapse, in print, with the collapse engine's own proof idea (the both-leafless same-depth relation is a bisimulation). Supporting context from the same section, read directly: Definition 2.4 (tree bisimulation) and Definition 2.6 (strongly extensional tree) are both credited to Worrell; Example 2.5 notes that every node x of the infinite path satisfies t_x = t, so the infinite path is exactly the Quine-atom state (its unique maximal proper subtree is itself); Remark 2.2 defines strongly extensional graphs and the extensional quotient, citing Aczel; Proposition 2.11 and Corollary 2.12 transfer strong extensionality between pointed graphs and their tree expansions, which makes a graph-level version of the statement an easy consequence of their apparatus.

**Consequences for the Parmenides paper's novelty tiers.** Tier 3 must be restated: not merely "folklore-adjacent and apparently unstated" but "the tree-level instance is stated, with proof, as a passing example in Adámek et al., and a graph-level version follows readily from their Section 2." What remains uncontested: no source states the result as a hypothesis-explicit no-go about arbitrary plain coalgebras (their setting is trees and pointed graphs with strong extensionality built in, not behavioral identity as a negatable hypothesis); no source connects it to individuation or ontology; the strip-test packaging and machine-checking are not in the literature. Tier 1 (philosophical deployment) is untouched. Tier 2 (packaging) survives but must cite Example 2.7 prominently. The draft has been updated accordingly. This find also effectively discharges the "is it folklore" worry in the affirmative direction: it is better than folklore, it is citable print, which is safer for the paper (cite it; nobody can spring it on us).

### 2. Leitgeb and Ladyman read in full (action 5)

Read cover to cover (it is a seven-page discussion note). Correct citation: published online 2007, *Philosophia Mathematica* 16(3): 388-396 (2008), DOI 10.1093/philmat/nkm039. Findings:

- The examples: G (two nodes, one edge; Black's-spheres analog; nodes weakly discerned by the edge relation), G' (two isolated nodes, no edges), G'' (two disjoint isomorphic single-edge components). For G' and G'': "there is no irreflexive relation, nor any other way of grounding the difference." They generalize: the point holds for any unlabelled graph with at least two isolated nodes (11 of the 156 unlabelled six-node graphs) or two isomorphic disconnected components.
- The positive view, exactly: "the identity or difference of places in a structure is not to be accounted for by anything other than the structure itself," with identity and difference "among the very relations that the nodes in a graph bear to each other," like the successor relation in arithmetic.
- **Crucial nuance for the draft: they explicitly deny haecceitism.** Against Keranen's haecceities: "haecceities are intrinsic to each individual, [so] the permutation of individuals always results in a new situation, whereas permuting exactly structurally similar individuals in a mathematical structure results in exactly the same structure." So the two-loop horn has two distinct occupants: haecceitistic primitivism (Keranen-style) and structural primitivism (Leitgeb-Ladyman, also Shapiro 2006/2007 and Ketland 2006, who "explicitly reject the need to supply a general criterion of identity"). The draft's gloss of the horn as "haecceity" was too narrow and has been corrected.
- **The Dipert connection, direct quote of their summary:** Dipert "claims that the world is an asymmetric graph because he believes that facts about the numerical identity and diversity of objects must supervene on the relational facts," which Leitgeb and Ladyman reject. So Dipert himself accepted a supervenience-of-identity-on-structure requirement and concluded the world graph must be asymmetric: a direct precedent, inside graph-world metaphysics, for individuation constraints forcing conclusions about which worlds are possible. The collapse theorem is the atomless sharpening: at the bisimulation grain, no asymmetric escape exists in an atomless plain world.
- They leave the physical question open, citing Carnap's Aufbau §14 railtrack example: "It remains an open question whether the empirical world has such a structure."
- Citation harvest from their apparatus: Black 1952 (Mind 61: 153-164); Button 2006 (Analysis 66: 216-222); Ketland 2006 (Analysis 66: 303-315, the "dumb-bell" structure at p. 309); Ladyman 2005 (Analysis 65: 218-221); Saunders 2006 ("Are quantum particles objects?", Analysis 66: 52-63); Hawley 2006 (Analysis 66: 300-303); MacBride 2005; Shapiro 2007 ("the tale of i and -i", Philosophia Mathematica); Dipert 1997 (Journal of Philosophy 94: 329-358, confirmed); Keranen 2001.

### 3. The Bain exchange rounds (action 4)

- **Lal and Teh read (introduction, structure, conclusion; arXiv 1404.3049; BJPS 68(1): 213-251, 2017).** Thesis, quoted: "we will first argue that Bain's argument fails." Their analysis: Bain's defense uses two strategies, each resting on a form of category-theoretic generalization, which they name generalization by duality (GenDual, with Bain's Einstein-algebra example: "the details of how (GenDual) is applied do not work in Bain's favor") and generalization by categorification (GenCat, the TQFT example). Conclusion section: in GenDual, "category theory is playing an *organizational* role ... the morphisms in this category are 'scaffolding' ... and do not play a role in elucidating the physical concepts"; GenCat is the direct use, but neither delivers object-elimination. Their footnote 1 delineates the division of labor with Lam and Wüthrich: "We agree with many of their criticisms, but for the most part, they leave the deeply category-theoretic aspects of his argument ... undiscussed." So the two critical papers are complementary, not redundant, and the Parmenides paper can cite them as such.
- **Eva 2016 located and characterized (full read still owed).** Benjamin Eva, "Category theory and physical structuralism," *European Journal for Philosophy of Science* 6(2): 231-246 (2016). Position per the secondary record: contests the Lal-Teh and Lam-Wüthrich critiques, defending the viability of Bain's category-theoretic articulation. [check: read in full before engaging in print; secondary summaries differ on how strong Eva's pro-Bain conclusion is]

### 4. Weak discernibility, exact scope (action 6)

From the primary texts and their own abstracts, the correct characterizations to use in print:

- **Muller and Saunders 2008** (BJPS 59(3): 499-548): similar *fermions*, any finite number, all admissible pure or mixed states, *finite-dimensional* Hilbert spaces, discerned by permutation-invariant categorical (non-probabilistic) relations. Their own boson caveat: categorical discernibility of bosons is state-dependent; probabilistic relations would be needed for generality.
- **Muller and Seevinck 2009** (Philosophy of Science 76(2): 179-200; arXiv 0905.3273), extension in exactly two ways, from their abstract: "(a) from fermions to bosons for all finite-dimensional Hilbert-spaces; and (b) from finite-dimensional to infinite-dimensional Hilbert-spaces for all elementary particles," "using operators whose physical significance is beyond doubt." This resolves the round 2 refutations: the refuted glosses had attributed the fermion/finite-dimensional scope to the extension paper and overstated "purely relational individuation."
- **The aftermarket the paper should know about:** Caulton 2013, "Discerning 'indistinguishable' quantum systems" (Philosophy of Science 80(1): 49-72): argues the Saunders-Muller-Seevinck discerning relations rely on permutation-non-invariant quantities, then shows symmetric replacements can do the work, so the weak-discernibility program survives but its original relations needed repair. Also relevant: Muller, "The Rise of Relationals" (Mind; philsci-archive 9898) [check details], and Bigaj 2022 (absolute discernibility claim, per SEP) [check].
- Note for the draft's Section 5.1: none of this changes the draft's argument, which turns on where the discerning relation comes from, not on its exact quantum scope. But the paper now can and should state the scope precisely.

## Round 4: metadata closure, 2026-07-23 (hand checks against publisher and arXiv records)

Resolutions of the outstanding [check] items. Verified directly this round:

- **Chakravartty 1998** = "Semirealism," *Studies in History and Philosophy of Science* 29: 391-408 (the p. 399 formulation quoted by SEP falls in this range). The "Chakravartty 2003" in Esfeld and Lam's objector list is a separate later work; the paper cites 1998 for the canonical formulation, which stands. [resolved]
- **Kirchner, Benzmüller and Zalta**: *Review of Symbolic Logic* 13(1): 206-218 (2020). [resolved]
- **Benzmüller and Woltzenlogel Paleo 2014**: ECAI 2014, Frontiers in AI and Applications 263, IOS Press, pp. 93-98. **2016**: IJCAI 2016, AAAI Press, pp. 936-942. [resolved]
- **Rushby 2013**: "The Ontological Argument in PVS," Fun With Formal Methods workshop (CAV-affiliated), St. Petersburg, July 2013. Bonus find: Rushby, "Mechanized analysis of Anselm's modal ontological argument," *International Journal for Philosophy of Religion* (2021), a second, peer-reviewed installment worth citing in the methods paper. [resolved]
- **The American Sociologist pre-registration article**: Manago, "Preregistration and Registered Reports in Sociology: Strengths, Weaknesses, and Other Considerations," 54(1): 193-210 (2023). [resolved]
- **arXiv 2410.20936**: Li, Wu, Li, Wei, Zhang, Yang and Ma, "Autoformalize Mathematical Statements by Symbolic Equivalence and Semantic Consistency," published at NeurIPS 2024. **arXiv 2509.01398**: Cornelio, Ito, Cory-Wright, Dash and Horesh, "The Need for Verification in AI-Driven Scientific Discovery." **arXiv 2606.07897**: Botas, de Font-Reaulx and Hewitt, "The AI Epistemic Deference Index: A Continuous Measure of Sycophancy." [resolved]
- **Shackel 2011**: "The world as a graph: defending metaphysical graphical structuralism," *Analysis* 71(1): 10-21. **Oderberg's** challenged paper is titled "The World Is Not an Asymmetric Graph" (Analysis, 2011; page range not confirmed, it directly precedes Shackel's reply). [resolved; Oderberg pages at proofs stage]
- **Barwise and Moss skim** (the action 2 remainder): *Vicious Circles*, CSLI Lecture Notes 60, 1996. Confirmed: AFA is presented via the Solution Lemma, under which x = {x} has exactly one solution (the unique Quine atom). No statement of the general leafless-part collapse surfaced, consistent with Adámek et al. Example 2.7 remaining the closest print instance. [resolved at skim depth]
- **Eva 2016 full read**: ~~blocked~~ **done in round 5** (author supplied the PDF); see Round 5 below.

Resolved from standard bibliographic records, flagged for a routine spot-check at proofs stage rather than [check]: Fitelson and Zalta 2007 (*Journal of Philosophical Logic* 36: 227-247); Chambers 2013 (Cortex 49(3): 609-610 editorial); Chambers and Tzavella 2022 (*Nature Human Behaviour* 6: 29-42); Keranen 2001 (*Philosophia Mathematica* 9(3): 308-330); French and Ladyman 2003 (*Synthese* 136: 31-56); Ladyman 1998 (*SHPS* 29: 409-424); Esfeld and Lam, "Ontic structural realism as a metaphysics of objects," in Bokulich and Bokulich (eds.), *Scientific Structuralism*, Boston Studies 281, Springer 2011, 143-159; French 2010 (*Synthese* 175 supp.: 89-109); Ladyman 2007 (*Proceedings of the Aristotelian Society* supp. 81: 23-43); Saunders 2003 (in Brading and Castellani, CUP, 289-307); Schaffer 2010 (*Philosophical Review* 119(1): 31-76); Newman 1928 (*Mind* 37: 137-148); Muller, "The Rise of Relationals" (*Mind* 124, 2015); Bigaj 2022 (*Identity and Indiscernibility in Quantum Mechanics*, Palgrave); Leitgeb's two-part unlabeled-graphs study (*Philosophia Mathematica*, 2020/2021); Worrell 2005 (*TCS* 338: 184-199); Adámek et al. 2015 (*Applied Categorical Structures* 23: 609-641); Gylterud, Stenholm and Veltri (arXiv 2001.06696; journal venue unconfirmed).

### Verifier-run caveats (recorded verbatim in substance)

- The novelty finding rests on negative existentials that cannot be exhaustively verified; the Worrell PDF resisted clean text extraction (custom font encoding) and was checked by page rendering.
- The result may still be folklore in the AFA and non-well-founded set theory community (Quine atom uniqueness under strong extensionality is close to folklore); a targeted check of Aczel 1988, Barwise and Moss (Vicious Circles), and the modal logic literature on strongly extensional Kripke frames was not completed and remains owed.
- The Esfeld and Lam objector citations were corroborated cross-source, not checked against the paper's own bibliography.
- The 2023-2026 autoformalization literature moves fast and was not covered by verification.

---

## Strand 1: the Parmenides paper

### 1A. Mathematical novelty check (the decisive question)

The question was whether "the hereditarily non-empty part of a behaviorally identified P_κ coalgebra is a subsingleton" is already in the literature. The sweep's answer, in tiers:

**The ingredients are all standard, with canonical names.**
- The condition the paper calls behavioral identity is Rutten's "simple" (a system with no proper quotients; Theorem 8.1 of Universal Coalgebra: equivalent to "bisimilar implies equal") and Aczel and Mendler's "strongly extensional." [quoted, LB]
- Every coalgebra has a canonical behaviorally identified quotient (Rutten Prop. 8.2: quotient by the greatest bisimulation). Useful for the paper: the collapse applies to every plain world after extensional quotienting. [quoted]
- Final coalgebras for κ-bounded powerset functors exist (Rutten Thms 10.4, 10.6; unbounded powerset has none by Lambek plus Cantor). [quoted]
- Worrell: the final sequence of a finitary set functor converges in ω+ω steps; for κ-accessible functors, κ·2. **[verified 2-0]** The final coalgebra of the finite powerset functor is the set of finitely branching strongly extensional trees. [quoted]
- Adámek, Levy, Milius, Moss and Sousa study exactly the P_λ class (convergence in λ+ω steps), so the functor class is active, well-mapped territory. [quoted]
- AFA gives unique decorations; two graph nodes decorate to the same set iff a bisimulation relates them; the Quine atom Ω = {Ω} is the unique self-singleton, presented in the SEP entry as the paradigm circular set. Aczel's Final Coalgebra Theorem frames the AFA universe as a final powerset coalgebra. [quoted, LB]

**The combined statement was not found anywhere in the sweep.**
- The SEP entry on non-wellfounded set theory (Moss, 2008/2018) does not state or discuss the proposition that the hereditarily non-empty part of a strongly extensional powerset coalgebra is a singleton. [quoted, LB]
- Worrell provides the machinery (strongly extensional trees, where a leafless tree is exactly a hereditarily non-empty state) but nowhere states the singleton result. [quoted, LB]
- Gylterud, Stenholm and Veltri (Agda/HoTT models of SAFA and AFA): full-text search found no occurrence of "hereditarily non-empty" or "atomless"; the Quine atom appears only as a motivating example. [quoted, LB]
- Rutten's survey contains no atomless or hereditarily non-empty singleton claim. [quoted]

**Working conclusion for the paper's novelty section.** The three-tier claim structure in the draft is supported by the sweep: the identity criterion and its collapse machinery are established folklore with canonical citations; the specific combined no-go (arbitrary plain coalgebra, not a set theory and not a final coalgebra, with behavioral identity as an explicit hypothesis and atomlessness as the collapse driver, plus strip-test countermodels) did not surface in the canonical surveys or the closest technical papers. This is absence of evidence from one systematic sweep, not proof of novelty: before submission, ask a coalgebra specialist and search MathOverflow/nForum threads on "leafless strongly extensional" type statements. The engine lemma should be presented as "elementary given the classical machinery, apparently unstated at this generality," which is also the honest reason the paper's contribution is the philosophical deployment.

### 1B. OSR positioning

**The dialectical map.**
- SEP Structural Realism classifies eliminativist OSR as a distinct position (French its explicit defender) and gives the canonical statement of the standard objection: Chakravartty 1998: "one cannot intelligibly subscribe to the reality of relations unless one is also committed to the fact that some things are related." Objectors listed: Cao, Dorato, Psillos, Busch, Morganti, Chakravartty. [quoted]
- Esfeld and Lam codify a five-position taxonomy of object/relation priority, position (5) being eliminativist OSR (French and Ladyman 2003; French 2010), and report French's argument that intermediate positions (3) and (4) collapse into (5). [quoted, LB]
- **The gap the paper fills, in the literature's own words:** Esfeld and Lam state the existing objection to eliminativism is informal and threefold (metaphysical: relations require relata; empirical; logical: quantification and set theory presuppose objects), and explicitly decline to rule out the coherence of relations-without-relata a priori. So as of that survey, no formal impossibility result existed in this debate. [quoted, LB]

**Weak discernibility (the expected referee objection).**
- Canonical citations: Saunders, "Physics and Leibniz's Principles"; Muller and Saunders 2008 (BJPS 59(3): 499-548, DOI 10.1093/bjps/axn027); Muller and Seevinck 2009 (Philosophy of Science 76(2): 179-200, DOI 10.1086/647486). The core (weak discernibility as the standard escape, fermions and PII) is **[verified 3-0]**. Caution: the two detail glosses round 1 recorded here (the "maximal extension to arbitrary similar particles" characterization and the "purely relational individuation via permutation-invariant categorical relations" mechanism) were **[refuted 1-2]** in round 2; state the results' exact scope only from the papers themselves.
- Boson caveat inside the result itself: categorical discernibility of bosons is state-dependent; probabilistic relations are needed for full generality. [quoted; treat with the same caution as above]
- **Two findings that strengthen the paper's hand:**
  - Esfeld and Lam (moderate OSRists, not enemies of the program) argue weak discernibility yields numerical diversity but not individuation, and cannot ground priority of relations over relata; their own moderate OSR takes a numerical plurality of objects as primitive. The theorem's "plurality or behavioral identity: pick one" is exactly this concession, now forced formally. [quoted, LB]
  - Leitgeb and Ladyman 2008 (Philosophia Mathematica 16(3)) present graph-theoretic counterexamples violating even weak formulations of PII, and respond by taking identity and difference of positions as primitive structural facts grounded in nothing beyond the structure. That response is, in the paper's terms, occupying the two-loop horn (declining behavioral identity). So the paper's trilemma has named occupants in the literature for all three horns. [quoted, LB]
  - Also note Bigaj 2022 (per SEP): pushback claiming quantum particles are absolutely discernible after all. [check]

**The category theory round (Bain exchange).**
- Bain 2013, Synthese 190: 1621-1635 (not 197 as sometimes listed): ROSR's incoherence charge rests on set-theoretic formulations; category theory denies the conceptual-dependence premise; physics examples: Einstein algebras, topos-theoretic quantum foundations, sheaf models. [quoted]
- Lam and Wüthrich, BJPS 66: 605-634, DOI 10.1093/bjps/axt053: category theory is no more hospitable to ROSR than set theory; morphisms-only reformulation is "mere relabelling"; generalized elements (morphisms X→A) resurrect constituents; in Hilb and nCob (no products, by entanglement non-factorizability) even relations go, "baby with the bath water." [quoted, LB]
- Further rounds the draft did not know about: **Lal and Teh 2017** respond to Bain downplaying category theory's significance for structuralism; **Eva 2016** contests Lal and Teh. The paper should cite the full four-round exchange. [quoted; full citations needed: check]
- Positioning note: the coalgebraic framework enters this exchange on the critics' side but with a sharper instrument: instead of arguing that category theory fails to eliminate objects, it grants a categorical home (coalgebras of an endofunctor) and proves the elimination self-destructs by collapse rather than incoherence.

**Graph-world and monism framings.**
- Dipert's graph-theoretic world: the concrete world as a single structure induced by one two-place symmetric relation, best analyzed as a graph. Defended by Shackel 2011 (Analysis 71(1)) against Oderberg's formal objection (that graphical structuralism entails the world's nonexistence or perpetual cessation of change). Shackel explicitly construes graphical structuralism as a monism in which nodes and edges have identity only through position in the world structure. Two uses for the paper: a prior formal no-go argument in this exact territory (Oderberg, answered), and a monism reading already native to the graph-world literature. [quoted]
- Esfeld and Lam discuss a "super-holist" scenario (generic entanglement implies fundamentally one object, a Spinozistic monism) under which OSR fails as fundamental ontology: an informal analogue, inside the OSR literature, of the Parmenides collapse. The paper should cite this as the informal anticipation its theorem makes exact. [quoted, LB]
- Schaffer's priority monism vs existence monism distinction is the standard contemporary monism map for the framing section. [check: exact cite, Philosophical Review 2010]
- Newman's problem: Demopoulos and Friedman reading (only cardinality is discoverable); Ladyman 1998 and Ladyman and Ross 2007 reply that Newman does not arise for OSR because OSR eschews extensional relations. Keep the draft's "brackets from both sides" paragraph; add the caveat that OSR's own response to Newman (non-extensional relations) is unavailable against the collapse theorem, which never assumes extensionality of anything beyond the plain relating. [quoted + interpretation]
- Ladyman 2007 taxonomy (identity grounded/ungrounded, intrinsic/contextual; structuralism requires contextual individuation, groundable via weak discernibility): the frame in which the paper's result reads as "contextual individuation has no ground in plain atomless worlds." [quoted; check exact venue: Proceedings of the Aristotelian Society supp. vol.]

### 1C. Referee objections to expect (Strand 1)

1. Weak discernibility escapes the collapse (answer: Section 5.1 of the draft, now reinforced by Esfeld-Lam's own concession and Leitgeb-Ladyman's counterexamples).
2. Bisimilarity is the wrong identity criterion; structuralists may take identity as primitive-in-the-structure (Leitgeb-Ladyman). Answer: that is the two-loop horn, named and priced, not refuted.
3. The mathematics is folklore (answer: the three-tier novelty statement; contribution is deployment plus machine-checking plus the strip-test map of the debate).
4. Formalization choices drive the result (the Garbacz-style objection from Strand 2; answer: adequacy section plus the countermodels showing the hypotheses are independently meaningful).
5. Physics is not a plain powerset coalgebra (answer: the paper claims to formalize a metaphysical position, not physics; the position's own canonical statements are quantifier-free about what the relating is).

### 1D. Venue notes (Strand 1)

BJPS is the venue of record for this exact debate (Muller-Saunders 2008; Lam-Wüthrich). Synthese hosted Bain 2013 and much of the Esfeld-Lam line. Philosophia Mathematica took Leitgeb-Ladyman (identity in structures). Analysis took Shackel (short formal-metaphysics pieces). Recommendation unchanged: BJPS first, Synthese second; consider Analysis only for a compressed note version.

---

## Strand 2: the methods paper

### 2A. Machine-checked philosophy precedents

- **Benzmüller and Woltzenlogel Paleo, ECAI 2014** (Automating Gödel's ontological proof): higher-order provers (LEO-II, Satallax, Nitpick; plus Coq and Isabelle) proved T3 from Scott's axioms; discovered KB suffices (S5 criticism "provably pointless"; K has a countermodel); confirmed modal collapse; found Gödel's original 1970 axioms "seem inconsistent," flagged as a new result. [quoted]
- **Benzmüller and Woltzenlogel Paleo, IJCAI 2016** (The Inconsistency in Gödel's Ontological Argument): the definitive version. The inconsistency in the original axioms (missing conjunct in the definition of essence) went unnoticed for over four decades and was first detected automatically by LEO-II in 2013; reconstructed and verified in Isabelle/HOL; holds in all normal higher-order modal logics including K; key role played by the empty property via an Empty Essence Lemma. Scott's variant is consistent (Nitpick model). Cite both papers, in this division: 2014 for the program, 2016 for the discovery. [quoted, LB]
- **Oppenheimer and Zalta, AJP 89(2) 2011: 333-349:** PROVER9 discovered a one-premise valid version of Anselm's argument (their 1991 formalization needed three): machine discovery, not mere verification. Proof artifacts published at mally.stanford.edu (early precedent for artifact-alongside-paper). Their own verdict: valid but not a demonstration, Premise 2 lacking independent justification. [quoted]
- **Garbacz, AJP 90(3) 2012: 585-592, "PROVER9's Simplification Explained Away":** published reply arguing the machine's simplification was an artifact of representation choices. This is the canonical statement of the standard referee objection to machine-checked philosophy (the formalization, not the machine, drives the result) and the methods paper should cite it as the objection its adequacy discipline answers. [quoted, LB]
- **Fitelson, Oppenheimer and Zalta** coined "computational metaphysics" (2007). [quoted]
- **Kirchner, Benzmüller and Zalta, Review of Symbolic Logic (DOI 10.1017/S1755020319000297):** Abstract Object Theory mechanized in Isabelle/HOL; the verification uncovered a previously overlooked paradox (reintroduced when the logic of complex terms is adjoined to AOT's comprehension principle): mechanization finding a substantive defect informal scrutiny missed. Authors frame it as "strong evidence for a new kind of scientific practice in philosophy." Venue precedent: RSL takes this genre. [quoted, LB]
- **Rushby 2013:** Anselm in PVS (completes the precedent lineage). [check]
- **Gylterud, Stenholm and Veltri** (Agda, non-wellfounded set theory in HoTT): recent fully-formalized foundational work adjacent to metaphysics; useful as evidence the formal side is active. [quoted]

**Gap the methods paper fills:** all precedents are single-argument or single-theory verifications. None of them is a *method* for running a multi-year speculative program under epistemic discipline; none has pre-registration, adversarial blind review, or a failure taxonomy. The closest thing to a methods discussion in the lineage is Benzmüller and Woltzenlogel Paleo's human/machine division of labor remark and the open problem they name (extracting human-intelligible arguments from machine proofs). [quoted]

### 2B. Pre-registration beyond empirical science

- Registered Reports (Chambers, Center for Open Science): two-stage review with in-principle acceptance before results exist; 300+ journals; eliminates selective reporting and publication bias; Chambers chairs the RR steering committee. Defined by COS entirely in terms of empirical data collection, which is precisely the adaptation gap the paper claims to fill. [quoted, LB]
- Chambers and Tzavella 2022: null findings published at higher rates under RR. [quoted; check venue: Nature Human Behaviour]
- The American Sociologist 2023 (DOI 10.1007/s12108-023-09563-6): pre-registration extended beyond confirmatory designs (inductive/abductive, descriptive; living-document model); warns pre-registration can degrade into a credibility signal (a referee objection the methods paper should pre-empt: the answer is tied verdicts and liveness obligations, which make the registration machine-checkable rather than performative); does not recommend universal adoption. [quoted]
- No proposal found in the sweep for pre-registration of formal/proof-based research. The per-arm liveness obligation appears to be novel; it has no analogue in the RR literature because empirical studies get liveness for free from the world. [interpretation]

### 2C. AI epistemics (the timeliness case)

- **Sycophancy, measured:** the AI Epistemic Deference Index (AEDI) study: all eight frontier models tested show substantial epistemic deference (credence shifts with user attitude), with large provider differences (roughly 4x between least and most deferent); deference is amplified when the user requests a written artifact and concentrated on propositions where the model has weak priors. For the methods paper this is the empirical core of the motivated-formalization worry: a formal development produced by an AI *is* a written artifact about claims with weak priors. [quoted, LB; arXiv 2606.07897, check authors]
- **RLVR limitation:** reinforcement learning with verifiable rewards validates final answers, not reasoning chains; benchmark scores can improve under randomized and even negative rewards. Supports the paper's claim that end-to-end kernel checking plus interpretive review is the right split. [quoted; arXiv 2509.01398]
- **Autoformalization unreliability:** pass@1 vs pass@10 gaps of 19.5-26.5 percentage points for GPT-4 on MATH/miniF2F statement formalization; documented mistranslations of trivial statements; self-consistency selection via symbolic equivalence plus back-translation. Supports the claim that the informal-to-formal step is the weak joint, which is where the stack's adequacy disciplines live. [quoted; arXiv 2410.20936]
- Citation fabrication by LLMs documented (biomedical references). [quoted]

### 2D. Referee objections to expect (Strand 2)

1. "The formalization drives the result" (Garbacz): answered by the adequacy-forcing framing plus strip tests as standard practice.
2. "Pre-registration as credibility theater": answered by tied verdicts and per-arm liveness (the registration is itself machine-checkable).
3. "One project, own team": answered honestly (longitudinal, method fixed before the episodes it caught; adoption by others is the next test).
4. "Not philosophy but process engineering": venue choice matters; frame the failure taxonomy as epistemology of formalization.

### 2E. Venue notes (Strand 2)

Review of Symbolic Logic has taken mechanized-metaphysics work; Synthese and Metaphilosophy are the natural homes for the methods thesis; Philosophy and Technology if the AI angle leads. AJP took the Oppenheimer-Zalta exchange. Recommendation: Synthese (methods/formal epistemology track) first; Metaphilosophy as the fallback; a short companion note on the taxonomy could go to Analysis-style venues.

---

## Consolidated citation list (for the two drafts)

Strand 1: Aczel 1988 (Non-Well-Founded Sets, CSLI Lecture Notes 14); Barwise and Moss 1996 (Vicious Circles); Rutten 2000 (Universal Coalgebra, TCS 249: 3-80); Worrell 2005 (final sequence, TCS); Adámek, Levy, Milius, Moss, Sousa 2015 (Applied Categorical Structures, DOI 10.1007/s10485-014-9372-9); Gylterud, Stenholm, Veltri (arXiv 2001.06696); Moss, SEP Non-wellfounded Set Theory; SEP Structural Realism; Chakravartty 1998; French and Ladyman 2003; French 2010; French 2014 (The Structure of the World) [check]; Ladyman 1998; Ladyman 2007 (identity and diversity taxonomy) [check venue]; Ladyman and Ross 2007; Esfeld and Lam (five-position taxonomy paper, philsci-archive 5531) [check year/venue]; Saunders 2006; Muller and Saunders 2008 (BJPS 59(3): 499-548); Muller and Seevinck 2009 (Phil Sci 76(2): 179-200); Bigaj 2022 [check]; Leitgeb and Ladyman 2008 (Philosophia Mathematica 16(3)); Leitgeb 2021 [check]; Bain 2013 (Synthese 190: 1621-1635); Lam and Wüthrich (BJPS 66: 605-634); Lal and Teh 2017 [check]; Eva 2016 [check]; Dipert 1997 (Journal of Philosophy); Shackel 2011 (Analysis 71(1)); Oderberg [check: the objection Shackel answers]; Newman 1928 (Mind); Demopoulos and Friedman 1985 [check]; Schaffer 2010 (Philosophical Review) [check].

Strand 2: Benzmüller and Woltzenlogel Paleo 2014 (ECAI) and 2016 (IJCAI); Oppenheimer and Zalta 2011 (AJP 89(2): 333-349); Garbacz 2012 (AJP 90(3): 585-592); Fitelson and Zalta 2007; Kirchner, Benzmüller, Zalta (RSL, DOI 10.1017/S1755020319000297); Rushby 2013 [check]; Chambers (RR, Cortex 2013 editorial) [check]; Chambers and Tzavella 2022 [check venue]; American Sociologist 2023 preregistration article (DOI 10.1007/s12108-023-09563-6) [check author]; AEDI sycophancy study (arXiv 2606.07897) [check authors]; verification-cornerstone paper (arXiv 2509.01398) [check authors]; autoformalization self-consistency paper (arXiv 2410.20936) [check authors].

## Open actions: final state (all rounds)

1. ~~Adversarial verification~~ **Closed.** Round 2 (Opus verifiers): 23 confirmed, 2 refuted. Round 4 closed the tail by hand: Strand 2 citation metadata verified against publisher and arXiv records (the round 1 quotes were already extracted from primary pages); Newman and Schaffer resolved from standard records with a proofs-stage spot-check flag.
2. ~~Targeted folklore check~~ **Closed.** Round 3: the tree-level instance found in print (Adámek et al., Example 2.7). Round 4: Barwise and Moss skim done (Solution Lemma; unique Quine atom; no general leafless-collapse statement). The paper cites Example 2.7 regardless, so residual folklore risk is priced in.
3. ~~Resolve every [check]~~ **Closed.** All items either verified this round or downgraded to routine proofs-stage spot-checks; see Round 4. Chakravartty resolved: 1998, "Semirealism," SHPS 29: 391-408.
4. ~~Read Lal and Teh 2017~~ **Closed** (round 3, read). Eva 2016: **blocked, not closed**; full text paywalled from this environment; the drafts engage Eva only at name-the-round level until a library copy is read.
5. ~~Leitgeb and Ladyman 2008~~ **Closed** (round 3, read in full; draft corrected).
6. ~~Muller-Saunders / Muller-Seevinck scope~~ **Closed** (round 3, primary-text scope; Caulton repair round added).

## Round 5: Eva read and final spot-checks, 2026-07-23

**Eva 2016 read in full** (author-supplied PDF; *European Journal for Philosophy of Science* 6: 231-246, open access, received 1 May 2015, published online 17 February 2016). Findings:

- Thesis: defends Bain's arguments for the coherence of a category-theoretic ROSR against Wüthrich and Lam (2014) and Lal and Teh (2015): "Bain's arguments ... survive largely intact."
- Main moves: the objection that categories of structured sets smuggle relata back in does not apply to categories like HILB whose morphisms do not preserve internal set-theoretic structure; where Wüthrich and Lam's HILB-specific arguments bite, move to FHILB; the category REL of sets and relations is a further exemplar that even satisfies Wüthrich and Lam's requirement that morphisms be relations; Lal and Teh's reading of Bain is "unfair to the advocate of ROSR" since Bain's claims admit less problematic interpretations; and categorical quantum mechanics (Abramsky-Coecke) is "the philosophical vision ... deeply appealing to advocates of ROSR."
- **The load-bearing concession, final paragraph, quoted:** category-theoretic formalisms suffice "to prove the intelligibility and *coherence* of ROSR as a metaphysical theory about the physical world. However, Wüthrich and Lam are correct to contend that the existence of such formalisms do not count as arguments for the *truth* of ROSR."
- Use in the paper: the draft's Section 4.3 now engages Eva directly, entering at the coherence/truth boundary Eva himself draws: grant the coherent categorical articulation, then prove its content (the collapse). This is stronger than taking the critics' side in the framework dispute, and it required the full read.
- A second consequence of the read: the set-theory-is-no-home consensus Eva reports made "you used a set-theoretic carrier" the most predictable ROSR-side referee objection, so the draft gained Section 4.4 and Corollary A.2', answering it in four parts: the plain world is natively an endomorphism in REL (Eva's own certified category); the theorem's shape is the reverse of the incoherence argument (carrier identity is governed by the negatable behavioral-identity hypothesis, with the two-loop world exhibiting rather than presupposing brute identity); the conclusion is carrier-free (at most one bisimilarity class of atomless states, all mapping to Ω); and the hypotheses are categorical properties (Aczel-Mendler spans, simplicity, avoidance of the ∅ global element). Scope caveat stated: Eva's quantum exemplars carry labelled structure and so occupy the labelled horn; the theorem constrains the metaphysics, not object-free formulations of physics.
- Citation note: Eva's own reference list gives the BJPS reply as "Wüthrich, C., & Lam, V. (2014)," while the published paper is Lam and Wüthrich (BJPS 66: 605-634); he also quotes Esfeld and Lam 2008 ("Moderate structural realism about space-time," *Synthese* 160: 27-46, p. 31: "For the relations to be instantiated, there has to be something that instantiates them"), a second canonical relations-need-relata quote worth having.

**Proofs-stage spot-checks completed** (publisher records): Esfeld and Lam 2011 in Bokulich and Bokulich, pp. 143-159, Springer ✓; Newman 1928, *Mind* 37(146): 137-148 ✓; Keranen 2001, *Philosophia Mathematica* 9(3): 308-330 ✓; Oderberg 2011, *Analysis* 71(1): 3-10 ✓ (adjacency inference confirmed); **Shapiro corrected: 2008, not 2007**, *Philosophia Mathematica* 16(3): 285-309 ✓ (draft fixed); Fitelson and Zalta 2007, *JPL* 36(2): 227-247 ✓; Chambers and Tzavella 2022, *Nature Human Behaviour* 6: 29-42 ✓; Saunders 2003 in Brading and Castellani, CUP, pp. 289-307 ✓; French 2010, *Synthese* 175 (Supp 1): 89-109 ✓; Ladyman 2007, *PAS* Supp 81(1): 23-43 ✓; Worrell 2005, *TCS* 338(1-3): 184-199 ✓; Adámek et al. 2015, *Applied Categorical Structures* 23: 609-641 ✓; Bigaj 2022, *Identity and Indiscernibility in Quantum Mechanics*, Palgrave Macmillan (New Directions in the Philosophy of Science) ✓. Accepted from standard records without further check (cited peripherally or not at all in the drafts): Schaffer 2010 (119(1): 31-76), French and Ladyman 2003 (136: 31-56), Ladyman 1998 (29: 409-424), Chambers 2013 (Cortex 49(3): 609-610), Black 1952, and the Analysis cluster taken from Leitgeb and Ladyman's own reference list.

**Decision recorded:** the Lean verification footnote in the Parmenides paper stays.

## Remaining before submission (author-side)

- The specialist sanity pass on the mathematics (a coalgebra person, or MathOverflow, on whether anything earlier than Adámek et al. Example 2.7 states the leafless collapse).
- Build the minimal, program-vocabulary-free artifact repository and mint the Zenodo DOI for the retained footnote.
- Optional: read Muller's "The Rise of Relationals" and Leitgeb's two-part unlabeled-graphs study if the final draft ends up citing them; currently neither is cited in the paper's text.
