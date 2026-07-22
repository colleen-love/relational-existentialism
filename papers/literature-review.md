# Literature review: positioning and novelty for the two papers

*Compiled 2026-07-22. Copyright © 2026 Colleen Love. All rights reserved.*

## Method and verification status (read first)

This review was produced by a fan-out research pipeline: five search angles, 25 sources fetched, 123 claims extracted with direct quotes from the fetched texts. The pipeline's adversarial verification stage (three independent votes per claim) was interrupted by a session usage limit after confirming one claim; the remaining claims are **source-quoted but not adversarially verified**. Practical meaning: each claim below was extracted by a reader agent from the actual source with a supporting quote, which is far stronger than citation from memory, but quotes can be misread in context. Before submission, the load-bearing claims (marked LB below) should be re-verified by hand or by re-running the verification stage.

Confidence tiers used below:
- **[verified]** confirmed by independent adversarial votes (one claim).
- **[quoted]** extracted from the fetched source with a supporting direct quote.
- **[check]** citation metadata or interpretation that needs a manual check before submission.

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
- Canonical citations: Saunders, "Physics and Leibniz's Principles"; Muller and Saunders 2008 (BJPS 59(3): 499-548, DOI 10.1093/bjps/axn027): all finite fermion assemblies weakly discerned by permutation-invariant categorical relations, no haecceities and no revision of logic or set theory; Muller and Seevinck 2009 (Philosophy of Science 76(2): 179-200, DOI 10.1086/647486): maximal extension to arbitrary similar particles. [quoted]
- Boson caveat inside the result itself: categorical discernibility of bosons is state-dependent; probabilistic relations are needed for full generality. [quoted]
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

## Open actions before submission

1. Re-run the adversarial verification stage on the LB-marked claims (the pipeline can be resumed; or verify by hand).
2. Expert check on the mathematical novelty question (coalgebra specialist; MathOverflow).
3. Resolve every [check]: exact years, venues, authors, page ranges.
4. Read Lal and Teh 2017 and Eva 2016 in full (the sweep only located them).
5. Read Leitgeb and Ladyman 2008 in full: it is the closest philosophical neighbor and partially anticipates the two-loop horn.
